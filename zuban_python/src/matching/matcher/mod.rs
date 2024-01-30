mod bound;
mod type_var_matcher;
mod utils;

use core::fmt;
use std::{borrow::Cow, collections::HashSet};

pub use type_var_matcher::FunctionOrCallable;
use type_var_matcher::{BoundKind, TypeVarMatcher};
use utils::match_arguments_against_params;
pub(crate) use utils::{
    calculate_callable_init_type_vars_and_return, calculate_callable_type_vars_and_return,
    calculate_class_init_type_vars_and_return, calculate_function_type_vars_and_return,
    CalculatedTypeArgs,
};

use self::{bound::TypeVarBound, type_var_matcher::CalculatedTypeVarLike};

use super::{
    params::{matches_simple_params, InferrableParamIterator},
    FormatData, Match, OnTypeError, ParamsStyle, ResultContext, SignatureMatch,
};
use crate::{
    arguments::{Arg, ArgKind},
    database::{Database, PointLink},
    debug,
    diagnostics::IssueType,
    inference_state::InferenceState,
    type_::{
        match_tuple_type_arguments, AnyCause, CallableContent, CallableParam, CallableParams,
        GenericItem, GenericsList, ParamSpecArg, ParamSpecTypeVars, ParamSpecUsage, ParamType,
        ReplaceSelf, StarParamType, TupleArgs, TupleUnpack, Type, TypeArgs, TypeVarKind,
        TypeVarLike, TypeVarLikeUsage, TypeVarLikes, TypeVarTupleUsage, TypeVarUsage, TypedDict,
        TypedDictGenerics, Variance, WithUnpack,
    },
    type_helpers::{Callable, Class, Function},
};

#[derive(Debug)]
struct CheckedTypeRecursion<'a> {
    type1: &'a Type,
    type2: &'a Type,
    previously_checked: Option<&'a CheckedTypeRecursion<'a>>,
}

#[derive(Default)]
pub struct Matcher<'a> {
    type_var_matchers: Vec<TypeVarMatcher>,
    checking_type_recursion: Option<CheckedTypeRecursion<'a>>,
    class: Option<&'a Class<'a>>,
    func_or_callable: Option<FunctionOrCallable<'a>>,
    ignore_promotions: bool,
    replace_self: Option<ReplaceSelf<'a>>,
    pub ignore_positional_param_names: bool, // Matches `ignore_pos_arg_names` in Mypy
    match_reverse: bool,                     // For contravariance subtypes
}

impl<'a> Matcher<'a> {
    pub fn new(
        class: Option<&'a Class<'a>>,
        func_or_callable: FunctionOrCallable<'a>,
        type_var_matchers: Vec<TypeVarMatcher>,
        replace_self: Option<ReplaceSelf<'a>>,
    ) -> Self {
        Self {
            class,
            func_or_callable: Some(func_or_callable),
            type_var_matchers,
            replace_self,
            ..Self::default()
        }
    }

    pub fn new_class_matcher(i_s: &InferenceState, class: Class) -> Self {
        let type_var_likes = class.type_vars(i_s);
        if type_var_likes.is_empty() {
            Self::default()
        } else {
            Self {
                type_var_matchers: vec![TypeVarMatcher::new(
                    class.node_ref.as_link(),
                    type_var_likes.clone(),
                )],
                ..Self::default()
            }
        }
    }

    pub fn new_callable_matcher(callable: &'a CallableContent) -> Self {
        let type_var_matcher = (!callable.type_vars.is_empty())
            .then(|| TypeVarMatcher::new(callable.defined_at, callable.type_vars.clone()));
        Self {
            class: None,
            type_var_matchers: type_var_matcher.into_iter().collect(),
            func_or_callable: Some(FunctionOrCallable::Callable(Callable::new(callable, None))),
            ..Self::default()
        }
    }

    pub fn new_reverse_callable_matcher(callable: &'a CallableContent) -> Self {
        let mut m = Self::new_callable_matcher(callable);
        m.match_reverse = true;
        m
    }

    pub fn new_function_matcher(
        function: Function<'a, 'a>,
        type_vars: &TypeVarLikes,
        replace_self: ReplaceSelf<'a>,
    ) -> Self {
        let type_var_matcher = (!type_vars.is_empty())
            .then(|| TypeVarMatcher::new(function.node_ref.as_link(), type_vars.clone()));
        Self {
            type_var_matchers: type_var_matcher.into_iter().collect(),
            func_or_callable: Some(FunctionOrCallable::Function(function)),
            replace_self: Some(replace_self),
            ..Self::default()
        }
    }

    pub fn new_typed_dict_matcher(typed_dict: &TypedDict) -> Self {
        let type_var_matcher = match &typed_dict.generics {
            TypedDictGenerics::NotDefinedYet(type_var_likes) => Some(TypeVarMatcher::new(
                typed_dict.defined_at,
                type_var_likes.clone(),
            )),
            TypedDictGenerics::None => None,
            TypedDictGenerics::Generics(_) => None,
        };
        Self {
            type_var_matchers: type_var_matcher.into_iter().collect(),
            ..Self::default()
        }
    }

    pub fn add_reverse_callable_matcher(&mut self, c: &CallableContent) {
        if !c.type_vars.is_empty() {
            self.type_var_matchers.push(TypeVarMatcher::new_reverse(
                c.defined_at,
                c.type_vars.clone(),
            ))
        }
    }

    pub fn disable_reverse_callable_matcher(&mut self, db: &Database, c: &CallableContent) {
        if !c.type_vars.is_empty() {
            let matcher = self
                .type_var_matchers
                .iter_mut()
                .find(|m| m.match_in_definition == c.defined_at && m.enabled)
                .unwrap();
            matcher.enabled = false;
            if cfg!(feature = "zuban_debug") {
                let generics = matcher.clone().into_generics_list(db);
                debug!(
                    "Type vars for reverse callable matching [{}]{}",
                    generics.format(&FormatData::new_short(db)),
                    if matcher.has_unresolved_transitive_constraints() {
                        " (has unresolved transitive constraints)"
                    } else {
                        ""
                    }
                );
            }
        }
    }

    pub fn with_ignored_promotions() -> Self {
        Self {
            ignore_promotions: true,
            ..Self::default()
        }
    }

    pub fn with_ignore_positional_param_names(mut self) -> Self {
        self.ignore_positional_param_names = true;
        self
    }

    pub fn ignore_positional_param_names(&self) -> bool {
        self.ignore_positional_param_names
    }

    pub fn ignore_promotions(&self) -> bool {
        self.ignore_promotions
    }

    #[inline]
    pub fn might_have_defined_type_vars(&self) -> bool {
        !self.type_var_matchers.is_empty() || self.func_or_callable.is_some()
    }

    #[inline]
    pub fn has_type_var_matcher(&self) -> bool {
        !self.type_var_matchers.is_empty()
    }

    pub fn is_matching_reverse(&self) -> bool {
        self.match_reverse
    }

    pub fn match_reverse<T, C: FnOnce(&mut Self) -> T>(&mut self, callable: C) -> T {
        self.match_reverse = !self.match_reverse;
        let result = callable(self);
        self.match_reverse = !self.match_reverse;
        result
    }

    pub fn match_self(
        &mut self,
        i_s: &InferenceState,
        value_type: &Type,
        variance: Variance,
    ) -> Match {
        match value_type {
            Type::Self_ => Match::new_true(),
            _ => {
                if matches!(self.func_or_callable, Some(FunctionOrCallable::Function(_))) {
                    // In case we are working within a function, Self is bound already.
                    return self.replace_self.unwrap()().matches(i_s, self, value_type, variance);
                } else {
                    Match::new_false()
                }
            }
        }
    }

    fn match_or_add_type_var_if_responsible(
        &mut self,
        i_s: &InferenceState,
        t1: &TypeVarUsage,
        value_type: &Type,
        variance: Variance,
        from_reverse: bool,
    ) -> Option<Match> {
        let normal_side_matching = from_reverse == self.match_reverse;
        let type_var_matchers_count = self.type_var_matchers.len();
        for (i, tv_matcher) in self
            .type_var_matchers
            .iter()
            .filter(|tvm| tvm.enabled)
            .enumerate()
        {
            if tv_matcher.match_in_definition == t1.in_definition
                && tv_matcher.match_reverse != normal_side_matching
            {
                if type_var_matchers_count > 1 {
                    let mut has_unresolved_constraint = false;
                    value_type.search_type_vars(&mut |tv| {
                        for tv_matcher in &self.type_var_matchers {
                            if tv_matcher.match_in_definition == tv.in_definition()
                                && tv_matcher.match_reverse == normal_side_matching
                            {
                                has_unresolved_constraint = true;
                            }
                        }
                    });
                    if has_unresolved_constraint {
                        let tv_matcher = &mut self.type_var_matchers[i];
                        tv_matcher.calculated_type_vars[t1.index.as_usize()]
                            .unresolved_transitive_constraints
                            .push(BoundKind::TypeVar(TypeVarBound::new(
                                value_type.clone(),
                                variance,
                                t1.type_var.as_ref(),
                            )));
                        return Some(Match::new_true());
                    }
                }
                let tv_matcher = &mut self.type_var_matchers[i];
                return Some(tv_matcher.match_or_add_type_var(
                    i_s,
                    t1,
                    t1.type_var.as_ref(),
                    value_type,
                    variance,
                ));
            }
        }
        if normal_side_matching {
            if let Some(class) = self.class {
                if class.node_ref.as_link() == t1.in_definition {
                    let g = class
                        .generics()
                        .nth_usage(i_s.db, &TypeVarLikeUsage::TypeVar(Cow::Borrowed(t1)))
                        .expect_type_argument();
                    return Some(g.simple_matches(i_s, value_type, variance));
                }
            }
            // If we're in a class context, we must also be in a method.
            if let Some(func_class) = self.func_or_callable.as_ref().and_then(|f| f.class()) {
                if t1.in_definition == func_class.node_ref.as_link() {
                    let g = func_class
                        .generics()
                        .nth_usage(i_s.db, &TypeVarLikeUsage::TypeVar(Cow::Borrowed(t1)))
                        .expect_type_argument();
                    return Some(g.matches(i_s, self, value_type, variance));
                }
                // The case that the if does not hit happens e.g. for
                // testInvalidNumberOfTypeArgs:
                // class C:  # Forgot to add type params here
                //     def __init__(self, t: T) -> None: pass
            }
        }
        None
    }

    pub fn match_or_add_type_var(
        &mut self,
        i_s: &InferenceState,
        tv1: &TypeVarUsage,
        other: &Type,
        variance: Variance,
    ) -> Match {
        let other_side = match other {
            Type::TypeVar(tv2) => self
                .match_or_add_type_var_if_responsible(
                    i_s,
                    tv2,
                    &Type::TypeVar(tv1.clone()),
                    variance.invert(),
                    true,
                )
                .unwrap_or_else(|| {
                    (tv1.index == tv2.index && tv1.in_definition == tv2.in_definition).into()
                }),
            _ => Match::new_false(),
        };
        let m = self.match_or_add_type_var_if_responsible(i_s, tv1, other, variance, false);
        m.unwrap_or(other_side)
    }

    pub fn match_or_add_type_var_reverse_if_responsible(
        &mut self,
        i_s: &InferenceState,
        type_var_usage: &TypeVarUsage,
        other: &Type,
        variance: Variance,
    ) -> Option<Match> {
        self.match_or_add_type_var_if_responsible(
            i_s,
            type_var_usage,
            other,
            variance.invert(),
            true,
        )
    }

    pub fn match_or_add_type_var_tuple(
        &mut self,
        i_s: &InferenceState,
        tvt: &TypeVarTupleUsage,
        args2: TupleArgs,
        variance: Variance,
    ) -> Match {
        for (i, tv_matcher) in self
            .type_var_matchers
            .iter()
            .filter(|tvm| tvm.enabled)
            .enumerate()
        {
            if tv_matcher.match_in_definition == tvt.in_definition {
                let tv_matcher = &mut self.type_var_matchers[i];
                return tv_matcher.calculated_type_vars[tvt.index.as_usize()]
                    .match_or_add_type_var_tuple(i_s, args2);
            }
        }
        if let Some(class) = self.class {
            if class.node_ref.as_link() == tvt.in_definition {
                let ts1 = class
                    .generics()
                    .nth_usage(i_s.db, &TypeVarLikeUsage::TypeVarTuple(Cow::Borrowed(tvt)))
                    .expect_type_arguments();
                return match_tuple_type_arguments(
                    i_s,
                    &mut Matcher::default(),
                    &ts1.args,
                    &args2,
                    variance,
                );
            }
        }
        // If we're in a class context, we must also be in a method.
        if let Some(func_class) = self.func_or_callable.as_ref().and_then(|f| f.class()) {
            if tvt.in_definition == func_class.node_ref.as_link() {
                let ts1 = func_class
                    .generics()
                    .nth_usage(i_s.db, &TypeVarLikeUsage::TypeVarTuple(Cow::Borrowed(tvt)))
                    .expect_type_arguments();
                return match_tuple_type_arguments(
                    i_s,
                    &mut Matcher::default(),
                    &ts1.args,
                    &args2,
                    variance,
                );
            }
        }
        matches!(
            args2,
            TupleArgs::WithUnpack(u) if u.before.is_empty() && u.after.is_empty()
                 && matches!(&u.unpack, TupleUnpack::TypeVarTuple(tvt2) if tvt == tvt2)
        )
        .into()
    }

    pub fn match_or_add_param_spec_against_param_spec(
        &mut self,
        i_s: &InferenceState,
        p1_pre_param_spec: &[Type],
        p1: &ParamSpecUsage,
        p2_pre_param_spec: &[Type],
        p2: &ParamSpecUsage,
        type_vars2: Option<(&TypeVarLikes, PointLink)>,
        variance: Variance,
    ) -> Match {
        let mut p2_pre_iterator = p2_pre_param_spec.iter();
        let mut matches = Match::new_true();
        for t1 in p1_pre_param_spec {
            let Some(t2) = p2_pre_iterator.next() else {
                return Match::new_false()
            };
            matches &= t1.matches(i_s, self, t2, variance);
            if !matches.bool() {
                return matches;
            }
        }
        let match_params =
            |i_s: &_, matches, params: &ParamSpecArg, p2_pre_iterator: std::slice::Iter<_>| {
                match &params.params {
                    CallableParams::Simple(params1) => todo!(),
                    CallableParams::Any(_) => matches,
                    CallableParams::WithParamSpec(pre, usage) => {
                        if pre.len() != p2_pre_iterator.len() {
                            todo!()
                        } else {
                            debug!("TODO should maybe use type vars?");
                            let mut matches = matches;
                            for (t1, t2) in pre.iter().zip(p2_pre_iterator) {
                                matches &= t1.simple_matches(i_s, t2, variance);
                            }
                            matches & (usage == p2).into()
                        }
                    }
                }
            };
        if let Some(class) = self.class {
            if class.node_ref.as_link() == p1.in_definition {
                let usage = class.generics().nth_param_spec_usage(i_s.db, p1);
                return match_params(i_s, matches, &usage, p2_pre_iterator);
            } else {
                todo!()
            }
        }

        for (i, tv_matcher) in self
            .type_var_matchers
            .iter()
            .filter(|tvm| tvm.enabled)
            .enumerate()
        {
            if tv_matcher.match_in_definition == p1.in_definition {
                let tv_matcher = &mut self.type_var_matchers[i];
                let calc = &mut tv_matcher.calculated_type_vars[p1.index.as_usize()];
                return match &mut calc.type_ {
                    BoundKind::ParamSpecArgument(p) => {
                        match_params(i_s, matches, p, p2_pre_iterator)
                    }
                    BoundKind::Uncalculated { .. } => {
                        calc.type_ = BoundKind::ParamSpecArgument(ParamSpecArg::new(
                            CallableParams::WithParamSpec(
                                p2_pre_iterator.cloned().collect(),
                                p2.clone(),
                            ),
                            type_vars2.map(|type_vars| ParamSpecTypeVars {
                                type_vars: type_vars.0.clone(),
                                in_definition: type_vars.1,
                            }),
                        ));
                        matches
                    }
                    _ => unreachable!(),
                };
            }
        }
        (p2_pre_iterator.next().is_none() && p1 == p2).into()
    }

    pub fn match_or_add_param_spec(
        &mut self,
        i_s: &InferenceState,
        pre_param_spec_types: &[Type],
        p1: &ParamSpecUsage,
        params2_iterator: std::slice::Iter<CallableParam>,
        type_vars2: Option<(&TypeVarLikes, PointLink)>,
        variance: Variance,
    ) -> Match {
        debug_assert!(!self.is_matching_reverse());
        let mut params2_iterator = params2_iterator.peekable();
        let mut matches = Match::new_true();
        for pre in pre_param_spec_types {
            let t = match params2_iterator.peek().map(|p| &p.type_) {
                Some(ParamType::PositionalOnly(t) | ParamType::PositionalOrKeyword(t)) => {
                    params2_iterator.next();
                    t
                }
                Some(ParamType::Star(StarParamType::ArbitraryLen(t))) => t,
                _ => return Match::new_false(),
            };
            matches &= pre.matches(i_s, self, t, variance);
            if !matches.bool() {
                return matches;
            }
        }
        let match_params = |i_s, matches, params: &_, params2_iterator| match params {
            CallableParams::Simple(params1) => {
                matches
                    & matches_simple_params(
                        i_s,
                        &mut Matcher::default(),
                        params1.iter(),
                        params2_iterator,
                        variance,
                    )
            }
            CallableParams::Any(_) => matches,
            CallableParams::WithParamSpec(_, _) => todo!(),
        };
        for (i, tv_matcher) in self
            .type_var_matchers
            .iter()
            .filter(|tvm| tvm.enabled)
            .enumerate()
        {
            if tv_matcher.match_in_definition == p1.in_definition {
                let tv_matcher = &mut self.type_var_matchers[i];
                let calc = &mut tv_matcher.calculated_type_vars[p1.index.as_usize()];
                return match &mut calc.type_ {
                    BoundKind::ParamSpecArgument(p) => {
                        match_params(i_s, matches, &p.params, params2_iterator)
                    }
                    BoundKind::Uncalculated { .. } => {
                        calc.type_ = BoundKind::ParamSpecArgument(ParamSpecArg::new(
                            CallableParams::Simple(params2_iterator.cloned().collect()),
                            type_vars2.map(|type_vars| ParamSpecTypeVars {
                                type_vars: type_vars.0.clone(),
                                in_definition: type_vars.1,
                            }),
                        ));
                        matches
                    }
                    _ => unreachable!(),
                };
            } else {
                todo!()
            }
        }
        if let Some(class) = self.class {
            if class.node_ref.as_link() == p1.in_definition {
                let usage = class.generics().nth_param_spec_usage(i_s.db, p1);
                return match_params(i_s, matches, &usage.params, params2_iterator);
            } else {
                todo!()
            }
        }
        Match::new_false()
    }

    pub(crate) fn match_param_spec_arguments<'db, 'b, 'c>(
        &self,
        i_s: &InferenceState<'db, '_>,
        usage: &ParamSpecUsage,
        args: Box<[Arg<'db, 'b>]>,
        func_or_callable: FunctionOrCallable,
        add_issue: &dyn Fn(IssueType),
        on_type_error: Option<OnTypeError<'db, '_>>,
    ) -> SignatureMatch {
        let func_class = self.func_or_callable.and_then(|f| f.class());
        let param_spec_arg = if let Some(type_var_matcher) = self.type_var_matchers.first() {
            if type_var_matcher.match_in_definition == usage.in_definition {
                match &type_var_matcher.calculated_type_vars[usage.index.as_usize()].type_ {
                    BoundKind::ParamSpecArgument(p) => Cow::Borrowed(p),
                    // This means that an Any came along.
                    BoundKind::Uncalculated { .. } => return SignatureMatch::new_true(),
                    BoundKind::TypeVar(_) | BoundKind::TypeVarTuple(_) => unreachable!(),
                }
            } else {
                todo!("why?")
            }
        } else if let Some(class) = self.class.or(func_class.as_ref()) {
            class.generics().nth_param_spec_usage(i_s.db, usage)
        } else {
            todo!("When does this even happen?")
        };
        match &param_spec_arg.params {
            CallableParams::Simple(params) => {
                let iter = InferrableParamIterator::new(
                    i_s.db,
                    params.as_ref().iter(),
                    args.into_vec().into_iter(),
                );
                match_arguments_against_params(
                    i_s,
                    &mut Matcher::default(),
                    func_or_callable,
                    &add_issue,
                    on_type_error,
                    iter,
                )
            }
            CallableParams::Any(_) => SignatureMatch::new_true(),
            CallableParams::WithParamSpec(pre, usage1) => {
                let mut arg_iterator = args.into_vec().into_iter();
                if !pre.is_empty() {
                    for (spec_t, arg_t) in pre.iter().zip(arg_iterator.by_ref()) {
                        if let Some(arg_inf) =
                            arg_t.maybe_positional_arg(i_s, &mut ResultContext::Unknown)
                        {
                            match spec_t.is_simple_super_type_of(i_s, &arg_inf.as_type(i_s)) {
                                Match::False { similar, .. } => {
                                    return SignatureMatch::False { similar }
                                }
                                Match::True { .. } => (),
                            }
                        } else {
                            return SignatureMatch::False { similar: false };
                        }
                    }
                }
                let Some(last_arg) = arg_iterator.next() else {
                    todo!()
                };
                match last_arg.kind {
                    ArgKind::ParamSpec {
                        usage: ref usage2, ..
                    } => {
                        if usage1 == usage2 {
                            if arg_iterator.next().is_some() {
                                unreachable!()
                            }
                            SignatureMatch::new_true()
                        } else {
                            if let Some(on_type_error) = on_type_error {
                                debug!("TODO should add an error for param spec mismatches");
                                /*
                                (on_type_error.callback)(
                                    i_s,
                                    &|_| todo!(),
                                    &last_arg,
                                    Box::from("TODO X"),
                                    Box::from("TODO Y"),
                                )
                                */
                            }
                            SignatureMatch::False { similar: false }
                        }
                    }
                    _ => {
                        if let Some(type_var_matcher) = self.type_var_matchers.first() {
                            dbg!(self.class);
                        }
                        todo!("{:?}", last_arg.kind)
                    }
                }
            }
        }
    }

    pub fn format(
        &self,
        usage: &TypeVarLikeUsage,
        format_data: &FormatData,
        params_style: ParamsStyle,
    ) -> Box<str> {
        // In general this whole function should look very similar to the matches function, since
        // on mismatches this can be run.
        if let Some(type_var_matcher) = self.type_var_matchers.first() {
            if type_var_matcher.match_in_definition == usage.in_definition() {
                let current = &type_var_matcher.calculated_type_vars[usage.index().as_usize()];
                return match &current.type_ {
                    BoundKind::TypeVar(bound) => bound.format(format_data.db, format_data.style),
                    BoundKind::TypeVarTuple(ts) => ts.format(format_data),
                    BoundKind::ParamSpecArgument(p) => p.params.format(format_data, params_style),
                    BoundKind::Uncalculated { fallback } => {
                        if let TypeVarLike::TypeVar(type_var) = usage.as_type_var_like() {
                            if let TypeVarKind::Bound(bound) = &type_var.kind {
                                return bound.format(format_data);
                            }
                        }
                        Type::Never.format(format_data)
                    }
                };
            }
        }
        if let Some(class) = self.class {
            if class.node_ref.as_link() == usage.in_definition() {
                return class
                    .generics()
                    .nth_usage(format_data.db, usage)
                    .format(&format_data.remove_matcher())
                    .unwrap_or("()".into());
            }
        }
        if let Some(func_class) = self.func_or_callable.as_ref().and_then(|f| f.class()) {
            if usage.in_definition() == func_class.node_ref.as_link() {
                return func_class
                    .generics()
                    .nth_usage(format_data.db, usage)
                    .format(format_data)
                    .unwrap_or("()".into());
            }
        }
        usage.format_without_matcher(format_data.db, params_style)
    }

    fn iter_calculated_type_vars(&mut self) -> std::slice::IterMut<CalculatedTypeVarLike> {
        if let Some(type_var_matcher) = self.type_var_matchers.first_mut() {
            type_var_matcher.calculated_type_vars.iter_mut()
        } else {
            unreachable!()
        }
    }

    pub fn remove_self_from_callable(
        self,
        i_s: &InferenceState,
        mut callable: CallableContent,
    ) -> CallableContent {
        // Since self was removed, there is no self without annotation anymore.
        callable
            .kind
            .update_had_first_self_or_class_annotation(true);

        if !callable.type_vars.is_empty() {
            let tv_matcher = self.type_var_matchers.first().unwrap();
            let defined_at = callable.defined_at;
            callable = callable.replace_type_var_likes_and_self(
                i_s.db,
                &mut self.as_usage_closure(i_s.db, |usage| {
                    let index = usage.index().as_usize();
                    if usage.in_definition() == defined_at {
                        let c = &tv_matcher.calculated_type_vars[index];
                        debug_assert!(!c.calculated());
                        let new_index = tv_matcher
                            .calculated_type_vars
                            .iter()
                            .take(index)
                            .filter(|c| !c.calculated())
                            .count();
                        usage.into_generic_item_with_new_index(new_index.into())
                    } else {
                        usage.into_generic_item()
                    }
                }),
                &|| unreachable!("Self should have been remapped already"),
            );
            let mut old_type_vars = std::mem::replace(
                &mut callable.type_vars,
                i_s.db.python_state.empty_type_var_likes.clone(),
            )
            .as_vec();
            for (i, c) in tv_matcher.calculated_type_vars.iter().enumerate().rev() {
                if c.calculated() {
                    old_type_vars.remove(i);
                }
            }
            if !old_type_vars.is_empty() {
                callable.type_vars = TypeVarLikes::from_vec(old_type_vars);
            }
        }
        callable
    }

    pub fn replace_type_var_likes_for_nested_context(&self, db: &Database, t: &Type) -> Type {
        self.replace_type_var_likes(db, t, |usage| {
            if let TypeVarLike::TypeVar(tv) = usage.as_type_var_like() {
                if let TypeVarKind::Bound(bound) = &tv.kind {
                    return GenericItem::TypeArg(bound.clone());
                }
            }
            usage.as_type_var_like().as_any_generic_item()
        })
    }

    pub fn replace_type_var_likes_for_unknown_type_vars(&self, db: &Database, t: &Type) -> Type {
        self.replace_type_var_likes(db, t, |usage| {
            usage.as_type_var_like().as_never_generic_item()
        })
    }

    fn replace_type_var_likes(
        &self,
        db: &Database,
        t: &Type,
        on_uncalculated: impl Fn(TypeVarLikeUsage) -> GenericItem,
    ) -> Type {
        t.replace_type_var_likes(db, &mut self.as_usage_closure(db, on_uncalculated))
    }

    // TODO it feels extremely weird that we use GenericItem+'b
    pub fn as_usage_closure<'b>(
        &'b self,
        db: &'b Database,
        on_uncalculated: impl for<'x> Fn(TypeVarLikeUsage<'x>) -> GenericItem + 'b,
    ) -> impl for<'y> Fn(TypeVarLikeUsage<'y>) -> GenericItem + 'b {
        move |usage| {
            for type_var_matcher in self.type_var_matchers.iter().filter(|tvm| tvm.enabled) {
                if usage.in_definition() == type_var_matcher.match_in_definition {
                    let current = &type_var_matcher.calculated_type_vars[usage.index().as_usize()];
                    return match &current.type_ {
                        BoundKind::TypeVar(t) => GenericItem::TypeArg(t.clone().into_type(db)),
                        BoundKind::TypeVarTuple(ts) => {
                            GenericItem::TypeArgs(TypeArgs::new(ts.clone()))
                        }
                        BoundKind::ParamSpecArgument(param_spec) => {
                            GenericItem::ParamSpecArg(param_spec.clone())
                        }
                        // Any is just ignored by the context later.
                        BoundKind::Uncalculated { .. } => on_uncalculated(usage),
                    };
                }
            }
            if let Some(c) = self.class {
                if c.node_ref.as_link() == usage.in_definition() {
                    return c.generics().nth_usage(db, &usage).into_generic_item(db);
                }
            }
            if let Some(func_class) = self.func_or_callable.as_ref().and_then(|f| f.class()) {
                if usage.in_definition() == func_class.node_ref.as_link() {
                    let g = func_class
                        .generics()
                        .nth_usage(db, &usage)
                        .into_generic_item(db);
                    return match g {
                        GenericItem::TypeArg(t) => GenericItem::TypeArg(
                            self.replace_type_var_likes_for_nested_context(db, &t),
                        ),
                        GenericItem::TypeArgs(_) => todo!(),
                        GenericItem::ParamSpecArg(_) => todo!(),
                    };
                }
            }
            usage.into_generic_item()
        }
    }

    pub fn set_all_contained_type_vars_to_any(
        &mut self,
        i_s: &InferenceState,
        type_: &Type,
        cause: AnyCause,
    ) {
        if let Some(matcher) = self.type_var_matchers.first_mut() {
            matcher.set_all_contained_type_vars_to_any(i_s, type_, cause)
        }
    }

    pub fn avoid_recursion(
        &mut self,
        type1: &Type,
        type2: &Type,
        callable: impl FnOnce(&mut Matcher) -> Match,
    ) -> Match {
        let mut type_recursion = self.checking_type_recursion.as_ref();
        while let Some(tr) = type_recursion {
            if type1 == tr.type1 && type2 == tr.type2 {
                return Match::new_true();
            }
            type_recursion = tr.previously_checked;
        }
        let mut inner_matcher = Matcher {
            type_var_matchers: std::mem::take(&mut self.type_var_matchers),
            checking_type_recursion: Some(CheckedTypeRecursion {
                type1,
                type2,
                previously_checked: self.checking_type_recursion.as_ref(),
            }),
            class: self.class,
            func_or_callable: self.func_or_callable,
            ignore_promotions: self.ignore_promotions,
            ignore_positional_param_names: self.ignore_positional_param_names,
            replace_self: self.replace_self,
            match_reverse: self.match_reverse,
        };
        let result = callable(&mut inner_matcher);
        // Need to move back, because it was moved previously.
        self.type_var_matchers = std::mem::take(&mut inner_matcher.type_var_matchers);
        result
    }

    fn finish_matcher(mut self, db: &Database) -> (Self, Option<TypeVarLikes>) {
        if self.type_var_matchers.len() < 2 {
            // Finishing is only needed if multiple type var matchers need to negotiate type
            // vars.
            return (self, None);
        }

        let mut cycles = self.find_unresolved_transitive_constraint_cycles(db);
        self.add_free_type_var_likes_to_cycles(&mut cycles);

        for cycle in &cycles.cycles {
            self.resolve_cycle(db, &cycles, cycle)
        }
        (
            self,
            (!cycles.free_type_var_likes.is_empty())
                .then(|| TypeVarLikes::from_vec(cycles.free_type_var_likes)),
        )
    }

    fn resolve_cycle(&mut self, db: &Database, cycles: &TypeVarCycles, cycle: &TypeVarCycle) {
        let mut current_bound = if let Some(free_type_var_index) = cycle.free_type_var_index {
            let in_definition = self.type_var_matchers[0].match_in_definition;
            match cycles.free_type_var_likes[free_type_var_index].clone() {
                TypeVarLike::TypeVar(type_var) => {
                    BoundKind::TypeVar(TypeVarBound::Invariant(Type::TypeVar(TypeVarUsage {
                        type_var,
                        index: free_type_var_index.into(),
                        in_definition,
                    })))
                }
                TypeVarLike::TypeVarTuple(tvt) => BoundKind::TypeVarTuple(TupleArgs::WithUnpack(
                    WithUnpack::with_empty_before_and_after(TupleUnpack::TypeVarTuple(
                        TypeVarTupleUsage {
                            type_var_tuple: tvt,
                            index: free_type_var_index.into(),
                            in_definition,
                        },
                    )),
                )),
                TypeVarLike::ParamSpec(_) => todo!(),
            }
        } else {
            BoundKind::default()
        };
        for tv_in_cycle in &cycle.set {
            // Use normal bound
            let used = &mut self.type_var_matchers[tv_in_cycle.matcher_index].calculated_type_vars
                [tv_in_cycle.type_var_index];
            let taken_bounds = std::mem::take(&mut used.type_);
            if !current_bound.merge(db, taken_bounds).bool() {
                todo!()
            }

            // Use unresolved transitive constraints
            let unresolved_transitive_constraints =
                std::mem::take(&mut used.unresolved_transitive_constraints);

            for unresolved in unresolved_transitive_constraints.into_iter() {
                // Cache unresolved transitive constraints recursively to create a topological
                // sorting.
                let mut is_in_cycle = false;
                let replaced_unresolved = unresolved.replace_type_var_likes(db, &mut |usage| {
                    for matcher_index in 0..self.type_var_matchers.len() {
                        let tv_matcher = &self.type_var_matchers[matcher_index];
                        if usage.in_definition() == tv_matcher.match_in_definition {
                            let type_var_index = usage.index().as_usize();
                            let c = &tv_matcher.calculated_type_vars[type_var_index];
                            let depending_on = cycles
                                .find_cycle(TypeVarAlreadySeen {
                                    matcher_index,
                                    type_var_index,
                                })
                                .unwrap();
                            if !c.unresolved_transitive_constraints.is_empty() {
                                self.resolve_cycle(db, cycles, depending_on)
                            }
                            if let Some(free_type_var_index) = depending_on.free_type_var_index {
                                let in_definition = self.type_var_matchers[0].match_in_definition;
                                return match cycles.free_type_var_likes[free_type_var_index].clone()
                                {
                                    TypeVarLike::TypeVar(type_var) => {
                                        GenericItem::TypeArg(Type::TypeVar(TypeVarUsage {
                                            type_var,
                                            index: free_type_var_index.into(),
                                            in_definition,
                                        }))
                                    }
                                    TypeVarLike::TypeVarTuple(_) => todo!(),
                                    TypeVarLike::ParamSpec(_) => todo!(),
                                };
                            } else {
                                if depending_on.set.contains(tv_in_cycle) {
                                    is_in_cycle = true;
                                    return usage.into_generic_item();
                                }
                                let first_entry = depending_on.set.iter().next().unwrap();
                                let tv_matcher = &self.type_var_matchers[first_entry.matcher_index];
                                let tvl = &tv_matcher.type_var_likes[first_entry.type_var_index];
                                return tv_matcher.calculated_type_vars[first_entry.type_var_index]
                                    .clone()
                                    .into_generic_item(db, tvl);
                            }
                        }
                    }
                    usage.into_generic_item()
                });
                if !is_in_cycle {
                    if !current_bound.merge(db, replaced_unresolved).bool() {
                        todo!()
                    }
                }
            }
        }

        // Set the bounds properly
        for tv_in_cycle in &cycle.set {
            self.type_var_matchers[tv_in_cycle.matcher_index].calculated_type_vars
                [tv_in_cycle.type_var_index]
                .type_ = current_bound.clone();
        }
    }

    fn add_free_type_var_likes_to_cycles(&self, cycles: &mut TypeVarCycles) {
        for cycle in &mut cycles.cycles {
            if !cycle.has_bound {
                cycle.free_type_var_index = Some(cycles.free_type_var_likes.len());
                let new_tv = self.choose_free_type_variable(cycle);
                cycles.free_type_var_likes.push(new_tv);
            }
        }
    }

    fn choose_free_type_variable(&self, cycle: &TypeVarCycle) -> TypeVarLike {
        let iterator = cycle.set.iter().map(|tv| {
            (
                tv,
                &self.type_var_matchers[tv.matcher_index].type_var_likes[tv.type_var_index],
            )
        });
        let lowest = iterator
            .min_by_key(|(tv, _)| (tv.matcher_index, tv.type_var_index))
            .unwrap();
        lowest.1.clone()
    }

    fn find_unresolved_transitive_constraint_cycles(&self, db: &Database) -> TypeVarCycles {
        let mut cycles = TypeVarCycles::default();
        for (i, tv_matcher) in self.type_var_matchers.iter().enumerate() {
            for (k, tv) in tv_matcher.calculated_type_vars.iter().enumerate() {
                let current = TypeVarAlreadySeen {
                    matcher_index: i,
                    type_var_index: k,
                };
                let already_seen = TransitiveConstraintAlreadySeen {
                    current,
                    previous: None,
                };
                if !tv.calculated() && tv.unresolved_transitive_constraints.is_empty() {
                    // Create a cycle for a type var that is not part of a cycle
                    cycles.add(TransitiveConstraintAlreadySeen {
                        current,
                        previous: Some(&already_seen),
                    })
                } else {
                    let has_bound = self.add_cycles(db, &mut cycles, tv, already_seen);
                    if has_bound {
                        cycles.enable_has_bound_for_type_var(current)
                    }
                }
            }
        }
        cycles
    }

    fn add_cycles(
        &self,
        db: &Database,
        cycles: &mut TypeVarCycles,
        calculated: &CalculatedTypeVarLike,
        current_seen: TransitiveConstraintAlreadySeen,
    ) -> bool {
        let mut has_bound = calculated.calculated();
        for constraint in &calculated.unresolved_transitive_constraints {
            match constraint {
                BoundKind::TypeVar(tv_bound) => {
                    let t = match tv_bound {
                        TypeVarBound::Upper(t) => t,
                        TypeVarBound::Lower(t) => t,
                        TypeVarBound::Invariant(t) => todo!(),
                        TypeVarBound::UpperAndLower(..) => todo!(),
                    };
                    t.search_type_vars(&mut |usage| {
                        for (matcher_index, tv_matcher) in self.type_var_matchers.iter().enumerate()
                        {
                            if usage.in_definition() == tv_matcher.match_in_definition {
                                let type_var_index = usage.index().as_usize();
                                let current = &tv_matcher.calculated_type_vars[type_var_index];
                                let new_current_seen = TypeVarAlreadySeen {
                                    matcher_index,
                                    type_var_index,
                                };
                                let new_already_seen = TransitiveConstraintAlreadySeen {
                                    current: new_current_seen,
                                    previous: Some(&current_seen),
                                };
                                if new_already_seen.is_cycle_and_return_next().is_some() {
                                    cycles.add(new_already_seen)
                                } else {
                                    has_bound |=
                                        self.add_cycles(db, cycles, current, new_already_seen);
                                    if cycles.find_cycle(new_current_seen).is_none() {
                                        has_bound = true;
                                    }
                                }
                            }
                        }
                    })
                }
                BoundKind::TypeVarTuple(_) => todo!(),
                BoundKind::ParamSpecArgument(_) => todo!(),
                BoundKind::Uncalculated { fallback } => unreachable!(),
            }
        }
        has_bound
    }

    pub fn into_type_arg_iterator_or_any<'db>(
        self,
        db: &'db Database,
    ) -> impl Iterator<Item = Type> + 'db {
        self.type_var_matchers
            .into_iter()
            .next()
            .unwrap()
            .calculated_type_vars
            .into_iter()
            .map(|c| {
                c.maybe_calculated_type(db)
                    .unwrap_or(Type::Any(AnyCause::Todo))
            })
    }

    pub fn into_type_arg_iterator<'x>(
        self,
        db: &'x Database,
        type_vars: &'x TypeVarLikes,
    ) -> impl Iterator<Item = Type> + 'x {
        self.type_var_matchers
            .into_iter()
            .next()
            .unwrap()
            .calculated_type_vars
            .into_iter()
            .zip(type_vars.iter())
            .map(|(c, type_var_like)| {
                let GenericItem::TypeArg(t) = c.into_generic_item(
                    db,
                    type_var_like
                ) else {
                    unreachable!();
                };
                t
            })
    }

    pub fn into_generics_list(self, db: &Database) -> (Option<GenericsList>, Option<TypeVarLikes>) {
        let (slf, tvls) = self.finish_matcher(db);
        (
            slf.type_var_matchers
                .into_iter()
                .next()
                .map(|m| m.into_generics_list(db)),
            tvls,
        )
    }
}

impl fmt::Debug for Matcher<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("Matcher")
            .field("type_var_matcher", &self.type_var_matchers)
            .field("checking_type_recursion", &self.checking_type_recursion)
            .field("class", &self.class)
            .field("func_or_callable", &self.func_or_callable)
            .field("ignore_promotions", &self.ignore_promotions)
            .field("replace_self", &self.replace_self.map(|_| "..."))
            .field(
                "ignore_positional_param_names",
                &self.ignore_positional_param_names,
            )
            .field("match_reverse", &self.match_reverse)
            .finish()
    }
}

#[derive(Copy, Clone, PartialEq, Debug, Eq, Hash)]
struct TypeVarAlreadySeen {
    matcher_index: usize,
    type_var_index: usize,
}

#[derive(Debug)]
struct TransitiveConstraintAlreadySeen<'a> {
    current: TypeVarAlreadySeen,
    previous: Option<&'a TransitiveConstraintAlreadySeen<'a>>,
}

impl<'a> TransitiveConstraintAlreadySeen<'a> {
    fn is_cycle_and_return_next(&self) -> Option<TypeVarAlreadySeen> {
        let mut checking = self;
        while let Some(c) = checking.previous {
            if c.current == self.current {
                return Some(checking.current);
            }
            checking = c;
        }
        None
    }

    fn iter_ancestors(&self) -> TypeVarAlreadySeenIterator<'a> {
        TypeVarAlreadySeenIterator(self.previous)
    }
}

struct TypeVarAlreadySeenIterator<'a>(Option<&'a TransitiveConstraintAlreadySeen<'a>>);

impl Iterator for TypeVarAlreadySeenIterator<'_> {
    type Item = TypeVarAlreadySeen;

    fn next(&mut self) -> Option<Self::Item> {
        let first = self.0.take()?;
        let result = Some(first.current);
        self.0 = first.previous;
        result
    }
}

#[derive(Default)]
struct TypeVarCycles {
    cycles: Vec<TypeVarCycle>,
    free_type_var_likes: Vec<TypeVarLike>,
}

impl TypeVarCycles {
    fn add(&mut self, already_seen: TransitiveConstraintAlreadySeen) {
        for tv in already_seen.iter_ancestors() {
            for (i, cycle) in self.cycles.iter_mut().enumerate() {
                if cycle.set.contains(&tv) {
                    // If a cycle is discovered, add the type vars to that cycle.
                    cycle.set.extend(already_seen.iter_ancestors());

                    // We have to merge cycles that are connected to our cycle here.
                    // e.g. we have (A, B) and (C, D) and a new cycle (B, C) is added.
                    // In that case it should not be 2 or 3 cycles, but one like:
                    // (A, B, C, D).
                    let mut taken_cycle = std::mem::take(&mut cycle.set);
                    for other_cycle in self.cycles.iter_mut().skip(i) {
                        for other_tv in already_seen.iter_ancestors() {
                            if other_cycle.set.contains(&other_tv) {
                                taken_cycle.extend(other_cycle.set.drain())
                            }
                        }
                    }
                    self.cycles[i].set = taken_cycle;
                    self.cycles.retain(|cycle| !cycle.set.is_empty());
                    return;
                }
            }
        }
        self.cycles.push(TypeVarCycle::new(HashSet::from_iter(
            already_seen.iter_ancestors(),
        )));
    }

    fn enable_has_bound_for_type_var(&mut self, tv: TypeVarAlreadySeen) {
        for cycle in &mut self.cycles {
            if cycle.set.contains(&tv) {
                cycle.has_bound = true;
                break;
            }
        }
    }

    fn find_cycle(&self, tv: TypeVarAlreadySeen) -> Option<&TypeVarCycle> {
        for cycle in &self.cycles {
            if cycle.set.contains(&tv) {
                return Some(cycle);
            }
        }
        return None;
    }
}

#[derive(Debug)]
struct TypeVarCycle {
    set: HashSet<TypeVarAlreadySeen>,
    has_bound: bool,
    free_type_var_index: Option<usize>,
}

impl TypeVarCycle {
    fn new(set: HashSet<TypeVarAlreadySeen>) -> Self {
        // has_bound is initially initialized false and later updated.
        Self {
            set,
            has_bound: false,
            free_type_var_index: None,
        }
    }
}
