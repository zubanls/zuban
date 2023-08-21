mod bound;
mod type_var_matcher;
mod utils;

pub use type_var_matcher::FunctionOrCallable;
pub use utils::{
    calculate_callable_init_type_vars_and_return, calculate_callable_type_vars_and_return,
    calculate_class_init_type_vars_and_return, calculate_function_type_vars_and_return,
    CalculatedTypeArguments,
};

use std::borrow::Cow;
use std::rc::Rc;

use super::params::{matches_simple_params, InferrableParamIterator2};
use super::{FormatData, Match, OnTypeError, ParamsStyle, SignatureMatch, Type};
use crate::arguments::{Argument, ArgumentKind};
use crate::database::{
    CallableContent, CallableParam, CallableParams, Database, DbType, GenericItem,
    ParamSpecArgument, ParamSpecTypeVars, ParamSpecUsage, ParamSpecific, PointLink,
    StarredParamSpecific, TupleTypeArguments, TypeArguments, TypeOrTypeVarTuple, TypeVarLikeUsage,
    TypeVarLikes, TypeVarUsage, Variance,
};
use crate::debug;
use crate::inference_state::InferenceState;
use crate::node_ref::NodeRef;
use crate::type_helpers::{Callable, Class, Function};
use type_var_matcher::{BoundKind, CalculatedTypeVarLike, TypeVarMatcher};
use utils::match_arguments_against_params;

#[derive(Debug)]
struct CheckedTypeRecursion<'a> {
    type1: &'a DbType,
    type2: &'a DbType,
    previously_checked: Option<&'a CheckedTypeRecursion<'a>>,
}

#[derive(Default, Debug)]
pub struct Matcher<'a> {
    pub(super) type_var_matcher: Option<TypeVarMatcher>,
    checking_type_recursion: Option<CheckedTypeRecursion<'a>>,
    class: Option<&'a Class<'a>>,
    func_or_callable: Option<FunctionOrCallable<'a>>,
    ignore_promotions: bool,
    match_reverse: bool, // For contravariance subtypes
}

impl<'a> Matcher<'a> {
    pub fn new(
        class: Option<&'a Class<'a>>,
        func_or_callable: FunctionOrCallable<'a>,
        type_var_matcher: Option<TypeVarMatcher>,
    ) -> Self {
        Self {
            class,
            func_or_callable: Some(func_or_callable),
            type_var_matcher,
            ..Self::default()
        }
    }

    pub fn new_class_matcher(i_s: &InferenceState, class: Class) -> Self {
        let type_var_likes = class.type_vars(i_s);
        if type_var_likes.is_empty() {
            Self::default()
        } else {
            Self {
                type_var_matcher: Some(TypeVarMatcher::new(
                    class.node_ref.as_link(),
                    type_var_likes.len(),
                )),
                ..Self::default()
            }
        }
    }

    pub fn new_callable_matcher(callable: &'a CallableContent) -> Self {
        let type_var_matcher = (!callable.type_vars.is_empty())
            .then(|| TypeVarMatcher::new(callable.defined_at, callable.type_vars.len()));
        Self {
            class: None,
            type_var_matcher,
            func_or_callable: Some(FunctionOrCallable::Callable(Callable::new(callable, None))),
            ..Self::default()
        }
    }

    pub fn new_reverse_callable_matcher(callable: &'a CallableContent) -> Self {
        let mut m = Self::new_callable_matcher(callable);
        m.match_reverse = true;
        m
    }

    pub fn new_function_matcher(function: Function<'a, 'a>, type_vars: &TypeVarLikes) -> Self {
        let type_var_matcher = (!type_vars.is_empty())
            .then(|| TypeVarMatcher::new(function.node_ref.as_link(), type_vars.len()));
        Self {
            type_var_matcher,
            func_or_callable: Some(FunctionOrCallable::Function(function)),
            ..Self::default()
        }
    }

    pub fn with_ignored_promotions() -> Self {
        Self {
            ignore_promotions: true,
            ..Self::default()
        }
    }

    pub fn ignore_promotions(&self) -> bool {
        self.ignore_promotions
    }

    #[inline]
    pub fn might_have_defined_type_vars(&self) -> bool {
        self.type_var_matcher.is_some() || self.func_or_callable.is_some()
    }

    #[inline]
    pub fn has_type_var_matcher(&self) -> bool {
        self.type_var_matcher.is_some()
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

    pub fn match_or_add_type_var(
        &mut self,
        i_s: &InferenceState,
        t1: &TypeVarUsage,
        value_type: &Type,
        variance: Variance,
    ) -> Match {
        if let Some(matcher) = self.type_var_matcher.as_mut() {
            if matcher.match_in_definition == t1.in_definition {
                return matcher.match_or_add_type_var(
                    i_s,
                    t1,
                    t1.type_var.as_ref(),
                    value_type,
                    variance,
                );
            }
        }
        if let Some(class) = self.class {
            if class.node_ref.as_link() == t1.in_definition {
                let g = class
                    .generics()
                    .nth_usage(i_s.db, &TypeVarLikeUsage::TypeVar(Cow::Borrowed(t1)))
                    .expect_type_argument();
                return g.simple_matches(i_s, value_type, t1.type_var.variance);
            }
        }
        // If we're in a class context, we must also be in a method.
        if let Some(func_class) = self.func_or_callable.as_ref().and_then(|f| f.class()) {
            if t1.in_definition == func_class.node_ref.as_link() {
                let g = func_class
                    .generics()
                    .nth_usage(i_s.db, &TypeVarLikeUsage::TypeVar(Cow::Borrowed(t1)))
                    .expect_type_argument();
                return g.matches(i_s, self, value_type, t1.type_var.variance);
            }
            // The case that the if does not hit happens e.g. for
            // testInvalidNumberOfTypeArgs:
            // class C:  # Forgot to add type params here
            //     def __init__(self, t: T) -> None: pass
        }
        match value_type.as_ref() {
            DbType::TypeVar(t2) => {
                (t1.index == t2.index && t1.in_definition == t2.in_definition).into()
            }
            _ => Match::new_false(),
        }
    }

    pub fn match_type_var_tuple(
        &mut self,
        i_s: &InferenceState,
        tuple1: &[TypeOrTypeVarTuple],
        tuple2: &TupleTypeArguments,
        variance: Variance,
    ) -> Match {
        debug_assert!(!self.is_matching_reverse());
        let mut matches = Match::new_true();
        match tuple2 {
            TupleTypeArguments::FixedLength(ts2) => {
                let mut t2_iterator = ts2.iter();
                for t1 in tuple1.iter() {
                    match t1 {
                        TypeOrTypeVarTuple::Type(t1) => {
                            if let Some(t2) = t2_iterator.next() {
                                match t2 {
                                    TypeOrTypeVarTuple::Type(t2) => {
                                        matches &= Type::new(t1).matches(
                                            i_s,
                                            self,
                                            &Type::new(t2),
                                            variance,
                                        );
                                    }
                                    TypeOrTypeVarTuple::TypeVarTuple(_) => {
                                        return Match::new_false();
                                    }
                                }
                            } else {
                                matches &= Match::new_false();
                            }
                        }
                        TypeOrTypeVarTuple::TypeVarTuple(tvt) => {
                            // TODO TypeVarTuple currently we ignore variance completely
                            let tv_matcher = self.type_var_matcher.as_mut().unwrap();
                            let calculated =
                                &mut tv_matcher.calculated_type_vars[tvt.index.as_usize()];
                            let fetch = ts2.len() as isize + 1 - tuple1.len() as isize;
                            if let Ok(fetch) = fetch.try_into() {
                                if calculated.calculated() {
                                    calculated.merge_fixed_length_type_var_tuple(
                                        i_s,
                                        fetch,
                                        &mut t2_iterator.by_ref().take(fetch),
                                    );
                                } else {
                                    let types: Rc<_> =
                                        t2_iterator.by_ref().take(fetch).cloned().collect();
                                    calculated.type_ = BoundKind::TypeVarTuple(
                                        TypeArguments::new_fixed_length(types),
                                    );
                                }
                            } else {
                                // Negative numbers mean that we have non-matching tuples, but the fact they do not match
                                // will be noticed in a different place.
                            }
                        }
                    }
                }
            }
            TupleTypeArguments::ArbitraryLength(t2) => {
                let tv_matcher = self.type_var_matcher.as_mut().unwrap();
                for t1 in tuple1.iter() {
                    match t1 {
                        TypeOrTypeVarTuple::Type(t1) => {
                            todo!()
                        }
                        TypeOrTypeVarTuple::TypeVarTuple(tvt) => {
                            let calculated =
                                &mut tv_matcher.calculated_type_vars[tvt.index.as_usize()];
                            if calculated.calculated() {
                                todo!()
                            } else {
                                calculated.type_ = BoundKind::TypeVarTuple(
                                    TypeArguments::new_arbitrary_length(t2.as_ref().clone()),
                                );
                            }
                        }
                    }
                }
            }
        };
        matches
    }

    pub fn match_or_add_param_spec_against_param_spec(
        &mut self,
        i_s: &InferenceState,
        p1_pre_param_spec: &[DbType],
        p1: &ParamSpecUsage,
        p2_pre_param_spec: &[DbType],
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
            matches &= Type::new(t1).matches(i_s, self, &Type::new(t2), variance);
            if !matches.bool() {
                return matches;
            }
        }
        let match_params =
            |i_s: &_, matches, params: &ParamSpecArgument, p2_pre_iterator: std::slice::Iter<_>| {
                match &params.params {
                    CallableParams::Simple(params1) => todo!(),
                    CallableParams::Any => matches,
                    CallableParams::WithParamSpec(pre, usage) => {
                        if pre.len() != p2_pre_iterator.len() {
                            todo!()
                        } else {
                            debug!("TODO should maybe use type vars?");
                            let mut matches = matches;
                            for (t1, t2) in pre.iter().zip(p2_pre_iterator) {
                                matches &=
                                    Type::new(t1).simple_matches(i_s, &Type::new(t2), variance);
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
        let Some(tv_matcher) = self.type_var_matcher.as_mut() else {
            return (p2_pre_iterator.next().is_none() && p1 == p2).into()
        };
        if tv_matcher.match_in_definition == p1.in_definition {
            let calc = &mut tv_matcher.calculated_type_vars[p1.index.as_usize()];
            match &mut calc.type_ {
                BoundKind::ParamSpecArgument(p) => match_params(i_s, matches, p, p2_pre_iterator),
                BoundKind::Uncalculated => {
                    calc.type_ = BoundKind::ParamSpecArgument(ParamSpecArgument::new(
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
            }
        } else {
            (p2_pre_iterator.next().is_none() && p1 == p2).into()
        }
    }

    pub fn match_or_add_param_spec(
        &mut self,
        i_s: &InferenceState,
        pre_param_spec_types: &[DbType],
        p1: &ParamSpecUsage,
        params2_iterator: std::slice::Iter<CallableParam>,
        type_vars2: Option<(&TypeVarLikes, PointLink)>,
        variance: Variance,
    ) -> Match {
        debug_assert!(!self.is_matching_reverse());
        let mut params2_iterator = params2_iterator.peekable();
        let mut matches = Match::new_true();
        for pre in pre_param_spec_types {
            let t = match params2_iterator.peek().map(|p| &p.param_specific) {
                Some(ParamSpecific::PositionalOnly(t) | ParamSpecific::PositionalOrKeyword(t)) => {
                    params2_iterator.next();
                    t
                }
                Some(ParamSpecific::Starred(StarredParamSpecific::ArbitraryLength(t))) => t,
                _ => return Match::new_false(),
            };
            matches &= Type::new(pre).matches(i_s, self, &Type::new(t), variance);
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
            CallableParams::Any => matches,
            CallableParams::WithParamSpec(_, _) => todo!(),
        };
        if let Some(class) = self.class {
            if class.node_ref.as_link() == p1.in_definition {
                let usage = class.generics().nth_param_spec_usage(i_s.db, p1);
                return match_params(i_s, matches, &usage.params, params2_iterator);
            } else {
                todo!()
            }
        }
        let Some(tv_matcher) = self.type_var_matcher.as_mut() else {
            return Match::new_false()
        };
        if tv_matcher.match_in_definition == p1.in_definition {
            let calc = &mut tv_matcher.calculated_type_vars[p1.index.as_usize()];
            match &mut calc.type_ {
                BoundKind::ParamSpecArgument(p) => {
                    match_params(i_s, matches, &p.params, params2_iterator)
                }
                BoundKind::Uncalculated => {
                    calc.type_ = BoundKind::ParamSpecArgument(ParamSpecArgument::new(
                        CallableParams::Simple(params2_iterator.cloned().collect()),
                        type_vars2.map(|type_vars| ParamSpecTypeVars {
                            type_vars: type_vars.0.clone(),
                            in_definition: type_vars.1,
                        }),
                    ));
                    matches
                }
                _ => unreachable!(),
            }
        } else {
            todo!()
        }
    }

    pub fn match_param_spec_arguments<'db, 'b, 'c>(
        &self,
        i_s: &InferenceState<'db, '_>,
        usage: &ParamSpecUsage,
        args: Box<[Argument<'db, 'b>]>,
        func_or_callable: FunctionOrCallable,
        args_node_ref: &impl Fn() -> NodeRef<'c>,
        on_type_error: Option<OnTypeError<'db, '_>>,
    ) -> SignatureMatch {
        let func_class = self.func_or_callable.and_then(|f| f.class());
        let param_spec_arg = if let Some(type_var_matcher) = &self.type_var_matcher {
            if type_var_matcher.match_in_definition == usage.in_definition {
                match &type_var_matcher.calculated_type_vars[usage.index.as_usize()].type_ {
                    BoundKind::ParamSpecArgument(p) => Cow::Borrowed(p),
                    // This means that an Any came along.
                    BoundKind::Uncalculated => return SignatureMatch::new_true(),
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
                let iter = InferrableParamIterator2::new(
                    i_s.db,
                    params.as_ref().iter(),
                    args.into_vec().into_iter(),
                );
                match_arguments_against_params(
                    i_s,
                    &mut Matcher::default(),
                    func_or_callable,
                    args_node_ref,
                    on_type_error,
                    iter,
                )
            }
            CallableParams::Any => SignatureMatch::new_true(),
            CallableParams::WithParamSpec(pre, usage1) => {
                let mut arg_iterator = args.into_vec().into_iter();
                if !pre.is_empty() {
                    todo!()
                }
                let Some(last_arg) = arg_iterator.next() else {
                    todo!()
                };
                match last_arg.kind {
                    ArgumentKind::ParamSpec {
                        usage: ref usage2, ..
                    } => {
                        if usage1 == usage2 {
                            if arg_iterator.next().is_some() {
                                unreachable!()
                            }
                            SignatureMatch::new_true()
                        } else {
                            if let Some(on_type_error) = on_type_error {
                                (on_type_error.callback)(
                                    i_s,
                                    &|_| todo!(),
                                    &last_arg,
                                    Box::from("TODO X"),
                                    Box::from("TODO Y"),
                                )
                            }
                            SignatureMatch::False { similar: false }
                        }
                    }
                    _ => {
                        if let Some(type_var_matcher) = self.type_var_matcher.as_ref() {
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
        if let Some(type_var_matcher) = self.type_var_matcher.as_ref() {
            if type_var_matcher.match_in_definition == usage.in_definition() {
                let current = &type_var_matcher.calculated_type_vars[usage.index().as_usize()];
                return match &current.type_ {
                    BoundKind::TypeVar(bound) => bound.format(format_data.db, format_data.style),
                    BoundKind::TypeVarTuple(ts) => ts.format(format_data),
                    BoundKind::ParamSpecArgument(p) => p.params.format(format_data, params_style),
                    BoundKind::Uncalculated => DbType::Never.format(format_data),
                };
            }
        }
        if let Some(class) = self.class {
            if class.node_ref.as_link() == usage.in_definition() {
                return class
                    .generics()
                    .nth_usage(format_data.db, usage)
                    .format(&format_data.remove_matcher());
            }
        }
        if let Some(func_class) = self.func_or_callable.as_ref().and_then(|f| f.class()) {
            if usage.in_definition() == func_class.node_ref.as_link() {
                return func_class
                    .generics()
                    .nth_usage(format_data.db, usage)
                    .format(format_data);
            }
        }
        usage.format_without_matcher(format_data.db, params_style)
    }

    pub fn iter_calculated_type_vars(&mut self) -> std::slice::IterMut<CalculatedTypeVarLike> {
        if let Some(type_var_matcher) = self.type_var_matcher.as_mut() {
            type_var_matcher.calculated_type_vars.iter_mut()
        } else {
            unreachable!()
        }
    }

    pub fn replace_type_var_likes_for_nested_context(&self, db: &Database, t: &DbType) -> DbType {
        Type::new(t).replace_type_var_likes(db, &mut |type_var_like_usage| {
            if let Some(type_var_matcher) = self.type_var_matcher.as_ref() {
                if type_var_like_usage.in_definition() == type_var_matcher.match_in_definition {
                    let current = &type_var_matcher.calculated_type_vars
                        [type_var_like_usage.index().as_usize()];
                    return match &current.type_ {
                        BoundKind::TypeVar(t) => {
                            GenericItem::TypeArgument(t.clone().into_db_type(db))
                        }
                        BoundKind::TypeVarTuple(_) => todo!(),
                        BoundKind::ParamSpecArgument(param_spec) => {
                            GenericItem::ParamSpecArgument(param_spec.clone())
                        }
                        // Any is just ignored by the context later.
                        BoundKind::Uncalculated => {
                            type_var_like_usage.as_type_var_like().as_any_generic_item()
                        }
                    };
                }
            }
            if let Some(c) = self.class {
                if c.node_ref.as_link() == type_var_like_usage.in_definition() {
                    return c
                        .generics()
                        .nth_usage(db, &type_var_like_usage)
                        .into_generic_item(db);
                }
            }
            let func_class = self.func_or_callable.as_ref().unwrap().class().unwrap();
            if type_var_like_usage.in_definition() == func_class.node_ref.as_link() {
                let g = func_class
                    .generics()
                    .nth_usage(db, &type_var_like_usage)
                    .into_generic_item(db);
                match g {
                    GenericItem::TypeArgument(t) => GenericItem::TypeArgument(
                        self.replace_type_var_likes_for_nested_context(db, &t),
                    ),
                    GenericItem::TypeArguments(_) => todo!(),
                    GenericItem::ParamSpecArgument(_) => todo!(),
                }
            } else {
                type_var_like_usage.into_generic_item()
            }
        })
    }

    pub fn set_all_contained_type_vars_to_any(&mut self, i_s: &InferenceState, type_: &DbType) {
        if let Some(matcher) = self.type_var_matcher.as_mut() {
            matcher.set_all_contained_type_vars_to_any(i_s, type_)
        }
    }

    pub fn avoid_recursion(
        &mut self,
        type1: &DbType,
        type2: &DbType,
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
            type_var_matcher: self.type_var_matcher.take(),
            checking_type_recursion: Some(CheckedTypeRecursion {
                type1,
                type2,
                previously_checked: self.checking_type_recursion.as_ref(),
            }),
            class: self.class,
            func_or_callable: self.func_or_callable,
            ignore_promotions: self.ignore_promotions,
            match_reverse: self.match_reverse,
        };
        let result = callable(&mut inner_matcher);
        // Need to move back, because it was moved previously.
        self.type_var_matcher = inner_matcher.type_var_matcher.take();
        result
    }

    pub fn unwrap_calculated_type_args(self) -> Vec<CalculatedTypeVarLike> {
        self.type_var_matcher.unwrap().calculated_type_vars
    }
}
