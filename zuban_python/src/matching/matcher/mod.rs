mod bound;
mod type_var_matcher;
mod utils;

use core::fmt;
use std::{borrow::Cow, collections::HashSet, rc::Rc};

pub use type_var_matcher::FunctionOrCallable;
use type_var_matcher::TypeVarMatcher;
use utils::match_arguments_against_params;
pub(crate) use utils::{
    calculate_callable_init_type_vars_and_return, calculate_callable_type_vars_and_return,
    calculate_class_init_type_vars_and_return, calculate_function_type_vars_and_return,
    CalculatedTypeArgs,
};

use self::{
    bound::{Bound, BoundKind},
    type_var_matcher::CalculatingTypeArg,
};

use super::{
    params::{matches_params, InferrableParamIterator},
    FormatData, Match, OnTypeError, ParamsStyle, ResultContext, SignatureMatch,
};
use crate::{
    arguments::{Arg, ArgKind, InferredArg},
    database::{Database, PointLink},
    debug,
    diagnostics::IssueType,
    inference_state::InferenceState,
    type_::{
        match_tuple_type_arguments, AnyCause, CallableContent, CallableParam, CallableParams,
        DbString, GenericItem, GenericsList, ParamSpecArg, ParamSpecUsage, ParamType, ReplaceSelf,
        StarParamType, TupleArgs, TupleUnpack, Type, TypeArgs, TypeVarKind, TypeVarLike,
        TypeVarLikeUsage, TypeVarLikes, TypeVarTupleUsage, TypeVarUsage, TypedDict,
        TypedDictGenerics, Variance, WithUnpack,
    },
    type_helpers::{Callable, Class, Function},
    utils::join_with_commas,
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
    fn new(
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

    pub fn matches_callable(
        &mut self,
        i_s: &InferenceState,
        c1: &CallableContent,
        c2_ref: &CallableContent,
    ) -> Match {
        let mut c2 = Cow::Borrowed(c2_ref);
        let type_var_matchers_len = self.type_var_matchers.len() as u32;
        if !c2.type_vars.is_empty() {
            if self
                .type_var_matchers
                .iter()
                .any(|tvm| tvm.match_in_definition == c2.defined_at)
            {
                c2 = Cow::Owned(c2_ref.replace_type_var_likes_and_self(
                    i_s.db,
                    &mut |mut usage| {
                        if usage.in_definition() == c2_ref.defined_at {
                            usage.update_temporary_matcher_index(type_var_matchers_len)
                        }
                        usage.into_generic_item()
                    },
                    &|| Type::Self_,
                ));
            }
            self.type_var_matchers
                .push(TypeVarMatcher::new(c2.defined_at, c2.type_vars.clone()))
        }

        let result = c1.return_type.is_super_type_of(i_s, self, &c2.return_type)
            & matches_params(i_s, self, &c1.params, &c2.params).or(|| {
                // Mypy treats *args/**kwargs special
                c1.params.is_any_args_and_kwargs().into()
            });

        if cfg!(feature = "zuban_debug") {
            if !c2.type_vars.is_empty() {
                let i = self
                    .find_responsible_type_var_matcher_index(c2.defined_at, type_var_matchers_len)
                    .unwrap();
                let matcher = &self.type_var_matchers[i];
                let generics = matcher.clone().into_generics_list(i_s.db);
                debug!(
                    "Type vars for reverse callable matching [{}]{}",
                    generics.format(&FormatData::new_short(i_s.db)),
                    if matcher.has_unresolved_transitive_constraints() {
                        " (has unresolved transitive constraints)"
                    } else {
                        ""
                    }
                );
            }
        }
        result
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

    #[inline]
    pub fn has_responsible_matcher(&self, tvt2: &TypeVarTupleUsage) -> bool {
        self.find_responsible_type_var_matcher_index(tvt2.in_definition, tvt2.temporary_matcher_id)
            .is_some()
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

    fn find_responsible_type_var_matcher_index(
        &self,
        in_definition: PointLink,
        temporary_matcher_index: u32,
    ) -> Option<usize> {
        for (i, tv_matcher) in self.type_var_matchers.iter().enumerate() {
            if tv_matcher.match_in_definition == in_definition {
                if temporary_matcher_index > 0 && i != temporary_matcher_index as usize {
                    continue;
                }
                return Some(i);
            }
        }
        None
    }
    fn match_or_add_type_var_if_responsible(
        &mut self,
        i_s: &InferenceState,
        t1: &TypeVarUsage,
        value_type: &Type,
        variance: Variance,
    ) -> Option<Match> {
        if let Some(matcher_index) =
            self.find_responsible_type_var_matcher_index(t1.in_definition, t1.temporary_matcher_id)
        {
            if self.check_if_unresolved_transitive_constraint(
                TypeVarIndexed {
                    matcher_index,
                    type_var_index: t1.index.as_usize(),
                },
                |found_type_var| value_type.search_type_vars(found_type_var),
                || Bound::new_type_arg(value_type.clone(), variance, t1.type_var.as_ref()),
            ) {
                return Some(Match::new_true());
            }
            let tv_matcher = &mut self.type_var_matchers[matcher_index];
            return Some(tv_matcher.match_or_add_type_var(i_s, t1, value_type, variance));
        }
        if !self.match_reverse {
            if let Some(class) = self.class {
                if class.node_ref.as_link() == t1.in_definition {
                    let g = class
                        .generics()
                        .nth_usage(i_s.db, &TypeVarLikeUsage::TypeVar(t1.clone()))
                        .expect_type_argument();
                    return Some(g.simple_matches(i_s, value_type, variance));
                }
            }
            // If we're in a class context, we must also be in a method.
            if let Some(func_class) = self.func_or_callable.as_ref().and_then(|f| f.class()) {
                if t1.in_definition == func_class.node_ref.as_link() {
                    let g = func_class
                        .generics()
                        .nth_usage(i_s.db, &TypeVarLikeUsage::TypeVar(t1.clone()))
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

    #[inline]
    fn check_if_unresolved_transitive_constraint(
        &mut self,
        tv: TypeVarIndexed,
        find_type_var: impl FnOnce(&mut dyn FnMut(TypeVarLikeUsage)),
        as_constraint: impl Fn() -> Bound,
    ) -> bool {
        if self.type_var_matchers.len() <= 1 {
            return false;
        }
        let mut has_unresolved_constraint = false;
        find_type_var(&mut |tv| {
            if self
                .find_responsible_type_var_matcher_index(
                    tv.in_definition(),
                    tv.temporary_matcher_id(),
                )
                .is_some()
            {
                has_unresolved_constraint = true;
            }
        });
        if has_unresolved_constraint {
            self.add_unresolved_constraint(tv, as_constraint())
        }
        has_unresolved_constraint
    }

    fn add_unresolved_constraint(&mut self, tv: TypeVarIndexed, constraint: Bound) {
        let tv_matcher = &mut self.type_var_matchers[tv.matcher_index];
        tv_matcher.calculating_type_args[tv.type_var_index]
            .unresolved_transitive_constraints
            .push(constraint);
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
                .match_reverse(|matcher| {
                    matcher.match_or_add_type_var_if_responsible(
                        i_s,
                        tv2,
                        &Type::TypeVar(tv1.clone()),
                        variance.invert(),
                    )
                })
                .unwrap_or_else(|| {
                    (tv1.index == tv2.index && tv1.in_definition == tv2.in_definition).into()
                }),
            _ => Match::new_false(),
        };
        let m = self.match_or_add_type_var_if_responsible(i_s, tv1, other, variance);
        m.unwrap_or(other_side)
    }

    pub fn match_or_add_type_var_reverse_if_responsible(
        &mut self,
        i_s: &InferenceState,
        type_var_usage: &TypeVarUsage,
        other: &Type,
        variance: Variance,
    ) -> Option<Match> {
        self.match_reverse(|matcher| {
            matcher.match_or_add_type_var_if_responsible(
                i_s,
                type_var_usage,
                other,
                variance.invert(),
            )
        })
    }

    pub fn match_or_add_type_var_tuple(
        &mut self,
        i_s: &InferenceState,
        tvt1: &TypeVarTupleUsage,
        args2: TupleArgs,
        variance: Variance,
    ) -> Match {
        let other_side = match &args2 {
            TupleArgs::WithUnpack(WithUnpack {
                before,
                unpack: TupleUnpack::TypeVarTuple(tvt2),
                after,
            }) if before.len() == 0 && after.len() == 0 => self.match_reverse(|matcher| {
                matcher.match_or_add_type_var_tuple_internal(
                    i_s,
                    tvt2,
                    TupleArgs::WithUnpack(WithUnpack::with_empty_before_and_after(
                        TupleUnpack::TypeVarTuple(tvt1.clone()),
                    )),
                    variance.invert(),
                )
            }),
            _ => Match::new_false(),
        };
        let m = self.match_or_add_type_var_tuple_internal(i_s, tvt1, args2, variance);
        m.or(|| other_side)
    }

    pub fn match_or_add_type_var_tuple_internal(
        &mut self,
        i_s: &InferenceState,
        tvt: &TypeVarTupleUsage,
        args2: TupleArgs,
        variance: Variance,
    ) -> Match {
        if let Some(matcher_index) = self
            .find_responsible_type_var_matcher_index(tvt.in_definition, tvt.temporary_matcher_id)
        {
            if self.check_if_unresolved_transitive_constraint(
                TypeVarIndexed {
                    matcher_index,
                    type_var_index: tvt.index.as_usize(),
                },
                |found_type_var| args2.search_type_vars(found_type_var),
                || Bound::new_type_args(args2.clone(), variance),
            ) {
                return Match::new_true();
            }
            let tv_matcher = &mut self.type_var_matchers[matcher_index];
            return tv_matcher.calculating_type_args[tvt.index.as_usize()]
                .type_
                .merge(i_s.db, Bound::new_type_args(args2, variance));
        }

        if !self.match_reverse {
            if let Some(class) = self.class {
                if class.node_ref.as_link() == tvt.in_definition {
                    let ts1 = class
                        .generics()
                        .nth_usage(i_s.db, &TypeVarLikeUsage::TypeVarTuple(tvt.clone()))
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
                        .nth_usage(i_s.db, &TypeVarLikeUsage::TypeVarTuple(tvt.clone()))
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
        variance: Variance,
    ) -> Match {
        let mut p2_pre_iterator = p2_pre_param_spec.iter();
        let mut matches = Match::new_true();
        let mut only_check_reverse = false;
        for t1 in p1_pre_param_spec {
            let Some(t2) = p2_pre_iterator.next() else {
                only_check_reverse = true;
                break
            };
            matches &= t1.matches(i_s, self, t2, variance);
            if !matches.bool() {
                return matches;
            }
        }
        let mut reverse_m = Match::new_false();
        if p2_pre_iterator.clone().next().is_none() {
            if let Some(m) = self.match_reverse(|matcher| {
                matcher.match_or_add_param_spec_against_param_spec_internal(
                    i_s,
                    p2,
                    p1_pre_param_spec.iter().skip(p2_pre_param_spec.len()),
                    p1,
                    variance.invert(),
                )
            }) {
                reverse_m = m;
            }
        }
        if only_check_reverse {
            return reverse_m;
        }
        let m = self
            .match_or_add_param_spec_against_param_spec_internal(
                i_s,
                p1,
                p2_pre_iterator.clone(),
                p2,
                variance,
            )
            .unwrap_or_else(|| (p2_pre_iterator.next().is_none() && p1 == p2).into());
        (matches & m).or(|| reverse_m)
    }

    pub fn match_or_add_param_spec_against_param_spec_internal<'x>(
        &mut self,
        i_s: &InferenceState,
        p1: &ParamSpecUsage,
        p2_pre_iterator: impl ExactSizeIterator<Item = &'x Type>,
        p2: &ParamSpecUsage,
        variance: Variance,
    ) -> Option<Match> {
        let new_params =
            CallableParams::WithParamSpec(p2_pre_iterator.cloned().collect(), p2.clone());
        if let Some(matcher_index) =
            self.find_responsible_type_var_matcher_index(p1.in_definition, p1.temporary_matcher_id)
        {
            let new_bound = Bound::new_param_spec(new_params, variance);

            let type_var_index = p1.index.as_usize();
            if self
                .type_var_matchers
                .iter()
                .any(|tvm| tvm.match_in_definition == p2.in_definition)
            {
                self.add_unresolved_constraint(
                    TypeVarIndexed {
                        matcher_index,
                        type_var_index,
                    },
                    new_bound,
                );
                return Some(Match::new_true());
            }
            let tv_matcher = &mut self.type_var_matchers[matcher_index];
            return Some(
                tv_matcher.calculating_type_args[type_var_index]
                    .type_
                    .merge(i_s.db, new_bound),
            );
        }

        if !self.match_reverse {
            if let Some(class) = self.class {
                if class.node_ref.as_link() == p1.in_definition {
                    let usage = class.generics().nth_param_spec_usage(i_s.db, p1);
                    return Some(matches_params(
                        i_s,
                        &mut Matcher::default(),
                        &usage.params,
                        &new_params,
                    ));
                }
            }
        }
        None
    }

    pub fn match_or_add_param_spec(
        &mut self,
        i_s: &InferenceState,
        pre_param_spec_types: &[Type],
        p1: &ParamSpecUsage,
        params2_iterator: std::slice::Iter<CallableParam>,
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
        let new_params = CallableParams::Simple(params2_iterator.cloned().collect());
        if let Some(matcher_index) =
            self.find_responsible_type_var_matcher_index(p1.in_definition, p1.temporary_matcher_id)
        {
            let type_var_index = p1.index.as_usize();
            if self.check_if_unresolved_transitive_constraint(
                TypeVarIndexed {
                    matcher_index,
                    type_var_index: p1.index.as_usize(),
                },
                |found_type_var| new_params.search_type_vars(found_type_var),
                || Bound::new_param_spec(new_params.clone(), variance),
            ) {
                return matches;
            }
            let tv_matcher = &mut self.type_var_matchers[matcher_index];
            return matches
                & tv_matcher.calculating_type_args[type_var_index]
                    .type_
                    .merge(i_s.db, Bound::new_param_spec(new_params, variance));
        }
        if !self.match_reverse {
            if let Some(class) = self.class {
                if class.node_ref.as_link() == p1.in_definition {
                    let usage = class.generics().nth_param_spec_usage(i_s.db, p1);
                    return matches
                        & matches_params(i_s, &mut Matcher::default(), &usage.params, &new_params);
                } else {
                    todo!()
                }
            }
        }
        Match::new_false()
    }

    pub(crate) fn match_param_spec_arguments<'db, 'b, 'c>(
        &mut self,
        i_s: &InferenceState<'db, '_>,
        usage: &ParamSpecUsage,
        args: Box<[Arg<'db, 'b>]>,
        func_or_callable: FunctionOrCallable,
        add_issue: &dyn Fn(IssueType),
        on_type_error: Option<OnTypeError<'db, '_>>,
    ) -> SignatureMatch {
        let func_class = self.func_or_callable.and_then(|f| f.class());
        let param_spec_usage;
        let params = if let Some(type_var_matcher) = self.type_var_matchers.first_mut() {
            if type_var_matcher.match_in_definition == usage.in_definition {
                let t = &mut type_var_matcher.calculating_type_args[usage.index.as_usize()].type_;
                match t {
                    // TODO fix variance for matching
                    Bound::Invariant(BoundKind::ParamSpec(p))
                    | Bound::Upper(BoundKind::ParamSpec(p))
                    | Bound::Lower(BoundKind::ParamSpec(p)) => p,
                    Bound::Uncalculated { .. } => {
                        // TODO fix variance
                        *t = Bound::new_param_spec(
                            infer_params_from_args(i_s, args),
                            Variance::Invariant,
                        );
                        return SignatureMatch::new_true();
                    }
                    _ => todo!(),
                }
            } else {
                todo!("why?")
            }
        } else if let Some(class) = self.class.or(func_class.as_ref()) {
            param_spec_usage = class.generics().nth_param_spec_usage(i_s.db, usage);
            &param_spec_usage.params
        } else {
            todo!("When does this even happen?")
        };
        match params {
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
    ) -> MatcherFormatResult {
        // In general this whole function should look very similar to the matches function, since
        // on mismatches this can be run.
        if let Some(i) = self.find_responsible_type_var_matcher_index(
            usage.in_definition(),
            usage.temporary_matcher_id(),
        ) {
            let current =
                &self.type_var_matchers[i].calculating_type_args[usage.index().as_usize()];
            return current.type_.format(usage, format_data, params_style);
        }
        if !self.match_reverse {
            if let Some(class) = self.class {
                if class.node_ref.as_link() == usage.in_definition() {
                    return MatcherFormatResult::Str(
                        class
                            .generics()
                            .nth_usage(format_data.db, usage)
                            .format(&format_data.remove_matcher())
                            .unwrap_or("()".into()),
                    );
                }
            }
            if let Some(func_class) = self.func_or_callable.as_ref().and_then(|f| f.class()) {
                if usage.in_definition() == func_class.node_ref.as_link() {
                    return MatcherFormatResult::Str(
                        func_class
                            .generics()
                            .nth_usage(format_data.db, usage)
                            .format(format_data)
                            .unwrap_or("()".into()),
                    );
                }
            }
        }
        MatcherFormatResult::Str(usage.format_without_matcher(format_data.db, params_style))
    }

    fn iter_calculating(&mut self) -> std::slice::IterMut<CalculatingTypeArg> {
        if let Some(type_var_matcher) = self.type_var_matchers.first_mut() {
            type_var_matcher.calculating_type_args.iter_mut()
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
                        let c = &tv_matcher.calculating_type_args[index];
                        debug_assert!(!c.calculated());
                        let new_index = tv_matcher
                            .calculating_type_args
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
            for (i, c) in tv_matcher.calculating_type_args.iter().enumerate().rev() {
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

    pub fn as_usage_closure<'b>(
        &'b self,
        db: &'b Database,
        on_uncalculated: impl Fn(TypeVarLikeUsage) -> GenericItem + 'b,
    ) -> impl Fn(TypeVarLikeUsage) -> GenericItem + 'b {
        move |usage| {
            if let Some(i) = self.find_responsible_type_var_matcher_index(
                usage.in_definition(),
                usage.temporary_matcher_id(),
            ) {
                let current =
                    &self.type_var_matchers[i].calculating_type_args[usage.index().as_usize()];
                return current
                    .type_
                    .clone()
                    .into_generic_item(db, |_| on_uncalculated(usage));
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
        for (i, tvm) in self.type_var_matchers.iter_mut().enumerate() {
            tvm.set_all_contained_type_vars_to_any(i_s, type_, i as u32, cause)
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

    fn constraint_count(&self) -> usize {
        self.type_var_matchers
            .iter()
            .map(|tvm| {
                tvm.calculating_type_args
                    .iter()
                    .map(|c| c.unresolved_transitive_constraints.len() + c.calculated() as usize)
            })
            .flatten()
            .sum()
    }

    fn calculating_arg(&self, tv: TypeVarIndexed) -> &CalculatingTypeArg {
        &self.type_var_matchers[tv.matcher_index].calculating_type_args[tv.type_var_index]
    }

    fn find_secondary_transitive_constraints(&mut self, db: &Database, cycles: &TypeVarCycles) {
        debug!("Start calculating secondary transitive constraints");
        for cycle in &cycles.cycles {
            let mut unresolved = vec![];
            // First check for all relevant unresolved constraints in the cycle that are non-cycles
            for tv_index in &cycle.set {
                let tv = self.calculating_arg(*tv_index);
                for u in &tv.unresolved_transitive_constraints {
                    let mut is_cycle = false;
                    u.search_type_vars(&mut |usage| {
                        if let Some(matcher_index) = self.find_responsible_type_var_matcher_index(
                            usage.in_definition(),
                            usage.temporary_matcher_id(),
                        ) {
                            let current = TypeVarIndexed {
                                matcher_index,
                                type_var_index: usage.index().as_usize(),
                            };
                            if cycle.set.contains(&current) {
                                is_cycle = true;
                            }
                        }
                    });
                    if !is_cycle {
                        unresolved.push(u.clone());
                    }
                }
            }

            // Check non-transitive constraints first
            for wanted_constraint in &unresolved {
                for tv_index in &cycle.set {
                    let c = self.calculating_arg(*tv_index);
                    if c.calculated() {
                        let bound = c.type_.clone();
                        let i_s = &InferenceState::new(db);

                        let t1 = match wanted_constraint {
                            Bound::Invariant(t) => t,
                            Bound::Upper(t) => t,
                            Bound::UpperAndLower(_, _) => todo!(),
                            Bound::Lower(t) => t,
                            Bound::Uncalculated { .. } => unreachable!(),
                        };
                        let (t2, variance) = match bound {
                            Bound::Invariant(t) => (t, Variance::Invariant),
                            Bound::Upper(t) => (t, Variance::Contravariant),
                            Bound::UpperAndLower(_, _) => todo!(),
                            Bound::Lower(t) => (t, Variance::Covariant),
                            Bound::Uncalculated { .. } => unreachable!(),
                        };
                        let m = t1.matches(i_s, self, &t2, variance);
                        debug!(
                            "Secondary constraint match for {} against {}: {m:?}",
                            t1.format_short(db),
                            t2.format_short(db)
                        );
                    }
                }
            }

            // TODO check unresolved against each other
        }
    }

    fn finish_matcher(mut self, db: &Database) -> (Self, Result<Option<TypeVarLikes>, Match>) {
        if self.type_var_matchers.len() < 2 {
            // Finishing is only needed if multiple type var matchers need to negotiate type
            // vars.
            return (self, Ok(None));
        }

        let mut cycles = self.find_unresolved_transitive_constraint_cycles(db);
        let before = self.constraint_count();
        self.find_secondary_transitive_constraints(db, &cycles);
        if before < self.constraint_count() {
            cycles = self.find_unresolved_transitive_constraint_cycles(db);
        }
        if let Err(m) = self.add_free_type_var_likes_to_cycles(db, &mut cycles) {
            return (self, Err(m));
        }

        if cfg!(feature = "zuban_debug") {
            debug!("Got the following transitive constraint cycles:");
            for cycle in &cycles.cycles {
                let bound = match cycle.free_type_var_index {
                    Some(index) => format!(
                        "with free type var {:?}",
                        cycles.free_type_var_likes[index].name(db)
                    ),
                    None => "has bounds".into(),
                };
                debug!(
                    " - {} {}",
                    join_with_commas(cycle.set.iter().map(|tv| {
                        format!(
                            "({}, {}, {})",
                            tv.matcher_index,
                            tv.type_var_index,
                            self.type_var_matchers[tv.matcher_index].type_var_likes
                                [tv.type_var_index]
                                .name(db)
                        )
                    })),
                    bound
                );
            }
        }
        for cycle in &cycles.cycles {
            if let Err(e) = self.resolve_cycle(db, &cycles, cycle) {
                for type_var_matcher in &mut self.type_var_matchers {
                    for (i, c) in type_var_matcher
                        .calculating_type_args
                        .iter_mut()
                        .enumerate()
                    {
                        c.type_
                            .set_to_any(&type_var_matcher.type_var_likes[i], AnyCause::FromError);
                    }
                }
                return (self, Err(e));
            }
        }
        (
            self,
            Ok((!cycles.free_type_var_likes.is_empty())
                .then(|| TypeVarLikes::from_vec(cycles.free_type_var_likes))),
        )
    }

    fn resolve_cycle(
        &mut self,
        db: &Database,
        cycles: &TypeVarCycles,
        cycle: &TypeVarCycle,
    ) -> Result<(), Match> {
        let mut current_bound = if let Some(free_type_var_index) = cycle.free_type_var_index {
            let in_definition = self.type_var_matchers[0].match_in_definition;
            Bound::Invariant(
                match cycles.free_type_var_likes[free_type_var_index].clone() {
                    TypeVarLike::TypeVar(type_var) => {
                        BoundKind::TypeVar(Type::TypeVar(TypeVarUsage {
                            type_var,
                            index: free_type_var_index.into(),
                            in_definition,
                            temporary_matcher_id: 0,
                        }))
                    }
                    TypeVarLike::TypeVarTuple(tvt) => BoundKind::TypeVarTuple(
                        TupleArgs::WithUnpack(WithUnpack::with_empty_before_and_after(
                            TupleUnpack::TypeVarTuple(TypeVarTupleUsage {
                                type_var_tuple: tvt,
                                index: free_type_var_index.into(),
                                in_definition,
                                temporary_matcher_id: 0,
                            }),
                        )),
                    ),
                    TypeVarLike::ParamSpec(param_spec) => {
                        BoundKind::ParamSpec(CallableParams::WithParamSpec(
                            Rc::from([]),
                            ParamSpecUsage {
                                param_spec,
                                index: free_type_var_index.into(),
                                in_definition,
                                temporary_matcher_id: 0,
                            },
                        ))
                    }
                },
            )
        } else {
            Bound::default()
        };
        for tv_in_cycle in &cycle.set {
            // Use normal bound
            let used = &mut self.type_var_matchers[tv_in_cycle.matcher_index].calculating_type_args
                [tv_in_cycle.type_var_index];
            let taken_bounds = std::mem::take(&mut used.type_);
            let m = current_bound.merge(db, taken_bounds);
            if !m.bool() {
                return Err(m);
            }

            // Use unresolved transitive constraints
            let unresolved_transitive_constraints =
                std::mem::take(&mut used.unresolved_transitive_constraints);

            for unresolved in unresolved_transitive_constraints.into_iter() {
                // Cache unresolved transitive constraints recursively to create a topological
                // sorting.
                let mut is_in_cycle = false;
                let mut had_error = None;
                let replaced_unresolved = unresolved.replace_type_var_likes(db, &mut |usage| {
                    if had_error.is_some() {
                        return usage.into_generic_item();
                    }
                    if let Some(matcher_index) = self.find_responsible_type_var_matcher_index(
                        usage.in_definition(),
                        usage.temporary_matcher_id(),
                    ) {
                        let tv = TypeVarIndexed {
                            matcher_index,
                            type_var_index: usage.index().as_usize(),
                        };
                        let c = self.calculating_arg(tv);
                        let depending_on = cycles.find_cycle(tv).unwrap();
                        if !c.unresolved_transitive_constraints.is_empty() {
                            let m = self.resolve_cycle(db, cycles, depending_on);
                            if let Err(err) = m {
                                had_error = Some(err);
                                return usage.into_generic_item();
                            }
                        }
                        if let Some(free_type_var_index) = depending_on.free_type_var_index {
                            let in_definition = self.type_var_matchers[0].match_in_definition;
                            let index = free_type_var_index.into();
                            return match cycles.free_type_var_likes[free_type_var_index].clone() {
                                TypeVarLike::TypeVar(type_var) => {
                                    GenericItem::TypeArg(Type::TypeVar(TypeVarUsage {
                                        type_var,
                                        index,
                                        in_definition,
                                        temporary_matcher_id: 0,
                                    }))
                                }
                                TypeVarLike::TypeVarTuple(type_var_tuple) => {
                                    GenericItem::TypeArgs(TypeArgs::new(TupleArgs::WithUnpack(
                                        WithUnpack::with_empty_before_and_after(
                                            TupleUnpack::TypeVarTuple(TypeVarTupleUsage {
                                                type_var_tuple,
                                                index,
                                                in_definition,
                                                temporary_matcher_id: 0,
                                            }),
                                        ),
                                    )))
                                }
                                TypeVarLike::ParamSpec(param_spec) => {
                                    GenericItem::ParamSpecArg(ParamSpecArg {
                                        params: CallableParams::WithParamSpec(
                                            Rc::from([]),
                                            ParamSpecUsage {
                                                param_spec,
                                                index: free_type_var_index.into(),
                                                in_definition,
                                                temporary_matcher_id: 0,
                                            },
                                        ),
                                        type_vars: None,
                                    })
                                }
                            };
                        } else {
                            if depending_on.set.contains(tv_in_cycle) {
                                is_in_cycle = true;
                                return usage.into_generic_item();
                            }
                            let first_entry = depending_on.set.iter().next().unwrap();
                            let tv_matcher = &self.type_var_matchers[first_entry.matcher_index];
                            let tvl = &tv_matcher.type_var_likes[first_entry.type_var_index];
                            return tv_matcher.calculating_type_args[first_entry.type_var_index]
                                .clone()
                                .into_generic_item(db, tvl);
                        }
                    }
                    usage.into_generic_item()
                });
                if let Some(err) = had_error {
                    return Err(err);
                }
                if !is_in_cycle {
                    let m = current_bound.merge(db, replaced_unresolved);
                    if !m.bool() {
                        return Err(m);
                    }
                }
            }
        }

        // Set the bounds properly
        for tv_in_cycle in &cycle.set {
            self.type_var_matchers[tv_in_cycle.matcher_index].calculating_type_args
                [tv_in_cycle.type_var_index]
                .type_ = current_bound.clone();
        }
        Ok(())
    }

    fn add_free_type_var_likes_to_cycles(
        &self,
        db: &Database,
        cycles: &mut TypeVarCycles,
    ) -> Result<(), Match> {
        for cycle in &mut cycles.cycles {
            if !cycle.has_bound {
                cycle.free_type_var_index = Some(cycles.free_type_var_likes.len());
                let new_tv = self.choose_free_type_variable(db, cycle)?;
                cycles.free_type_var_likes.push(new_tv);
            }
        }
        Ok(())
    }

    fn choose_free_type_variable(
        &self,
        db: &Database,
        cycle: &TypeVarCycle,
    ) -> Result<TypeVarLike, Match> {
        let as_type_var_like = |tv_index: TypeVarIndexed| {
            &self.type_var_matchers[tv_index.matcher_index].type_var_likes[tv_index.type_var_index]
        };
        let mut lst = Vec::from_iter(cycle.set.iter().cloned());
        lst.sort();
        let mut preferred_bound: Option<&_> = None;
        for tv_index in &lst {
            let type_var_like = as_type_var_like(*tv_index);
            if let TypeVarLike::TypeVar(new) = type_var_like {
                if !matches!(new.kind, TypeVarKind::Unrestricted) {
                    if let Some(current) = preferred_bound {
                        let TypeVarLike::TypeVar(current_tv) = current else {
                            unreachable!()
                        };
                        match (&current_tv.kind, &new.kind) {
                            (TypeVarKind::Bound(t1), TypeVarKind::Bound(t2)) => {
                                let i_s = &InferenceState::new(db);
                                if t1.is_simple_sub_type_of(i_s, t2).bool() {
                                    // Nothing left to do here.
                                } else if t2.is_simple_sub_type_of(i_s, t1).bool() {
                                    preferred_bound = Some(type_var_like)
                                } else {
                                    return Err(Match::new_false());
                                }
                            }
                            _ => return Err(Match::new_false()),
                        }
                    } else {
                        preferred_bound = Some(type_var_like)
                    }
                    continue;
                }
            }
        }
        if let Some(preferred_bound) = preferred_bound {
            Ok(preferred_bound.clone())
        } else {
            Ok(as_type_var_like(lst[0]).clone())
        }
    }

    fn find_unresolved_transitive_constraint_cycles(&self, db: &Database) -> TypeVarCycles {
        let mut cycles = TypeVarCycles::default();
        for (i, tv_matcher) in self.type_var_matchers.iter().enumerate() {
            for (k, tv) in tv_matcher.calculating_type_args.iter().enumerate() {
                let current = TypeVarIndexed {
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
        // Add all the remaining type var that are not actually a cycle to the list of cycles, so
        // we can just iterate over all distinct "cycles".
        for (i, tv_matcher) in self.type_var_matchers.iter().enumerate() {
            for (k, tv) in tv_matcher.calculating_type_args.iter().enumerate() {
                let current = TypeVarIndexed {
                    matcher_index: i,
                    type_var_index: k,
                };
                if cycles.find_cycle(current).is_none() {
                    cycles.cycles.push(TypeVarCycle {
                        set: HashSet::from([current]),
                        has_bound: tv.calculated()
                            | !tv.unresolved_transitive_constraints.is_empty(),
                        free_type_var_index: None,
                    });
                }
            }
        }
        cycles
    }

    fn add_cycles(
        &self,
        db: &Database,
        cycles: &mut TypeVarCycles,
        calc: &CalculatingTypeArg,
        current_seen: TransitiveConstraintAlreadySeen,
    ) -> bool {
        let mut has_bound = calc.calculated();
        for unresolved in &calc.unresolved_transitive_constraints {
            let cycle_search = &mut |usage: TypeVarLikeUsage| {
                if let Some(matcher_index) = self.find_responsible_type_var_matcher_index(
                    usage.in_definition(),
                    usage.temporary_matcher_id(),
                ) {
                    let type_var_index = usage.index().as_usize();
                    let new_current_seen = TypeVarIndexed {
                        matcher_index,
                        type_var_index,
                    };
                    let new_already_seen = TransitiveConstraintAlreadySeen {
                        current: new_current_seen,
                        previous: Some(&current_seen),
                    };
                    if new_already_seen.is_cycle() {
                        cycles.add(new_already_seen)
                    } else {
                        let current = self.calculating_arg(new_current_seen);
                        has_bound |= self.add_cycles(db, cycles, current, new_already_seen);
                        if cycles.find_cycle(new_current_seen).is_none() {
                            has_bound = true;
                        }
                    }
                    return;
                }
            };
            unresolved.search_type_vars(cycle_search)
        }
        has_bound
    }

    pub fn into_type_arg_iterator_or_any<'db>(
        self,
        db: &'db Database,
    ) -> impl Iterator<Item = Type> + 'db {
        debug_assert!(self
            .type_var_matchers
            .first()
            .unwrap()
            .type_var_likes
            .iter()
            .all(|tvl| matches!(tvl, TypeVarLike::TypeVar(_))));
        self.type_var_matchers
            .into_iter()
            .next()
            .unwrap()
            .calculating_type_args
            .into_iter()
            .map(|c| {
                let GenericItem::TypeArg(g) = c.type_.into_generic_item(db, |_| {
                    GenericItem::TypeArg(Type::Any(AnyCause::Todo))
                }) else {
                    unreachable!();
                };
                g
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
            .calculating_type_args
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

    pub fn into_type_arguments(
        self,
        db: &Database,
    ) -> (Match, Option<GenericsList>, Option<TypeVarLikes>) {
        let (slf, result) = self.finish_matcher(db);
        let type_args = slf
            .type_var_matchers
            .into_iter()
            .next()
            .map(|m| m.into_generics_list(db));
        match result {
            Ok(tvls) => (Match::new_true(), type_args, tvls),
            Err(m) => (m, type_args, None),
        }
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

#[derive(Copy, Clone, PartialEq, Debug, Eq, Hash, PartialOrd, Ord)]
struct TypeVarIndexed {
    matcher_index: usize,
    type_var_index: usize,
}

#[derive(Debug)]
struct TransitiveConstraintAlreadySeen<'a> {
    current: TypeVarIndexed,
    previous: Option<&'a TransitiveConstraintAlreadySeen<'a>>,
}

impl<'a> TransitiveConstraintAlreadySeen<'a> {
    fn is_cycle(&self) -> bool {
        self.iter_ancestors()
            .any(|ancestor| ancestor == self.current)
    }

    fn iter_ancestors(&self) -> TypeVarAlreadySeenIterator<'a> {
        TypeVarAlreadySeenIterator(self.previous)
    }
}

struct TypeVarAlreadySeenIterator<'a>(Option<&'a TransitiveConstraintAlreadySeen<'a>>);

impl Iterator for TypeVarAlreadySeenIterator<'_> {
    type Item = TypeVarIndexed;

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
        let cycle_parts = || {
            already_seen
                .iter_ancestors()
                .take_while(|tv| *tv != already_seen.current)
                .chain(std::iter::once(already_seen.current))
        };
        for tv in cycle_parts() {
            for (i, cycle) in self.cycles.iter_mut().enumerate() {
                if cycle.set.contains(&tv) {
                    // If a cycle is discovered, add the type vars to that cycle.
                    cycle.set.extend(cycle_parts());

                    // We have to merge cycles that are connected to our cycle here.
                    // e.g. we have (A, B) and (C, D) and a new cycle (B, C) is added.
                    // In that case it should not be 2 or 3 cycles, but one like:
                    // (A, B, C, D).
                    let mut taken_cycle = std::mem::take(&mut cycle.set);
                    let mut new_has_bound = false;
                    for other_cycle in self.cycles.iter_mut().skip(i) {
                        for other_tv in cycle_parts() {
                            if other_cycle.set.contains(&other_tv) {
                                taken_cycle.extend(other_cycle.set.drain());
                                new_has_bound |= other_cycle.has_bound;
                            }
                        }
                    }
                    self.cycles[i].set = taken_cycle;
                    self.cycles[i].has_bound |= new_has_bound;
                    self.cycles.retain(|cycle| !cycle.set.is_empty());
                    return;
                }
            }
        }
        self.cycles
            .push(TypeVarCycle::new(HashSet::from_iter(cycle_parts())));
    }

    fn enable_has_bound_for_type_var(&mut self, tv: TypeVarIndexed) {
        for cycle in &mut self.cycles {
            if cycle.set.contains(&tv) {
                cycle.has_bound = true;
                return;
            }
        }
    }

    fn find_cycle(&self, tv: TypeVarIndexed) -> Option<&TypeVarCycle> {
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
    set: HashSet<TypeVarIndexed>,
    has_bound: bool,
    free_type_var_index: Option<usize>,
}

impl TypeVarCycle {
    fn new(set: HashSet<TypeVarIndexed>) -> Self {
        // has_bound is initially initialized false and later updated.
        Self {
            set,
            has_bound: false,
            free_type_var_index: None,
        }
    }
}

fn infer_params_from_args<'db>(
    i_s: &InferenceState<'db, '_>,
    args: Box<[Arg<'db, '_>]>,
) -> CallableParams {
    let mut params = vec![];
    for arg in args.iter() {
        let inferred_arg = arg.infer(i_s, &mut ResultContext::Unknown);
        let InferredArg::Inferred(inf) = inferred_arg else {
            todo!()
        };
        let t = inf.as_type(i_s);
        let p = match (
            arg.is_keyword_argument(),
            arg.in_args_or_kwargs_and_arbitrary_len(),
        ) {
            (false, false) => CallableParam::new_anonymous(ParamType::PositionalOnly(t)),
            (true, false) => {
                let Some(key) = arg.keyword_name(i_s.db) else {
                    unreachable!()
                };
                CallableParam {
                    type_: ParamType::PositionalOnly(t),
                    name: Some(DbString::RcStr(key.into())),
                    has_default: false,
                }
            }
            (false, true) => todo!(),
            (true, true) => todo!(),
        };
        params.push(p);
    }
    CallableParams::Simple(params.into())
}

pub enum MatcherFormatResult {
    Str(Box<str>),
    TypeVarTupleUnknown,
}
