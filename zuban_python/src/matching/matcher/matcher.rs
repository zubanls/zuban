use std::borrow::Cow;
use std::rc::Rc;

use super::super::params::{matches_simple_params, InferrableParamIterator2};
use super::super::{FormatData, Generic, Match, MismatchReason, ParamsStyle, SignatureMatch, Type};
use super::bound::TypeVarBound;
use super::type_var_matcher::{
    match_arguments_against_params, BoundKind, CalculatedTypeVarLike, FunctionOrCallable,
    TypeVarMatcher,
};
use crate::arguments::{Argument, ArgumentKind};
use crate::database::{
    CallableContent, CallableParam, CallableParams, DbType, ParamSpecUsage, ParamSpecific,
    RecursiveAlias, StarredParamSpecific, TupleTypeArguments, TypeArguments, TypeOrTypeVarTuple,
    TypeVar, TypeVarLikeUsage, TypeVarLikes, TypeVarUsage, Variance,
};
use crate::inference_state::InferenceState;
use crate::node_ref::NodeRef;
use crate::value::{Class, Function, OnTypeError};

struct CheckedTypeRecursion {
    recursive_alias1: Rc<RecursiveAlias>,
    type2: DbType,
}

#[derive(Default)]
pub struct Matcher<'a> {
    type_var_matcher: Option<TypeVarMatcher<'a>>,
    checked_type_recursions: Vec<CheckedTypeRecursion>,
}

impl<'a> Matcher<'a> {
    pub fn new(type_var_matcher: Option<TypeVarMatcher<'a>>) -> Self {
        Self {
            type_var_matcher,
            ..Self::default()
        }
    }

    pub fn new_reverse_callable_matcher(
        callable: &'a CallableContent,
        calculated_type_vars: &'a mut [CalculatedTypeVarLike],
    ) -> Self {
        let mut m = TypeVarMatcher::new(
            None,
            FunctionOrCallable::Callable(callable),
            callable.defined_at,
            calculated_type_vars,
        );
        m.match_reverse = true;
        Self {
            type_var_matcher: Some(m),
            ..Self::default()
        }
    }

    pub fn new_reverse_function_matcher(
        function: Function<'a>,
        type_vars: Option<&TypeVarLikes>,
        calculated_type_vars: &'a mut Vec<CalculatedTypeVarLike>,
    ) -> Self {
        if let Some(type_vars) = type_vars {
            calculated_type_vars.resize_with(type_vars.len(), Default::default);
            let mut m = TypeVarMatcher::new(
                None,
                FunctionOrCallable::Function(function),
                function.node_ref.as_link(),
                calculated_type_vars,
            );
            m.match_reverse = true;
            Self {
                type_var_matcher: Some(m),
                ..Self::default()
            }
        } else {
            Matcher::default()
        }
    }

    #[inline]
    pub fn has_type_var_matcher(&self) -> bool {
        self.type_var_matcher.is_some()
    }

    pub fn is_matching_reverse(&self) -> bool {
        self.type_var_matcher
            .as_ref()
            .map(|m| m.match_reverse)
            .unwrap_or(false)
    }

    pub fn match_reverse<T, C: FnOnce(&mut Self) -> T>(&mut self, callable: C) -> T {
        if let Some(matcher) = self.type_var_matcher.as_mut() {
            matcher.match_reverse = !matcher.match_reverse;
            let result = callable(self);
            let matcher = self.type_var_matcher.as_mut().unwrap();
            matcher.match_reverse = !matcher.match_reverse;
            result
        } else {
            callable(self)
        }
    }

    pub fn match_or_add_type_var(
        &mut self,
        i_s: &mut InferenceState,
        t1: &TypeVarUsage,
        value_type: &Type,
        variance: Variance,
    ) -> Match {
        match self.type_var_matcher.as_mut() {
            Some(matcher) => self.match_or_add_type_var_in_type_var_matcher(
                i_s,
                t1,
                t1.type_var.as_ref(),
                value_type,
                variance,
            ),
            None => match value_type.maybe_db_type() {
                Some(DbType::TypeVar(t2)) => {
                    (t1.index == t2.index && t1.in_definition == t2.in_definition).into()
                }
                _ => Match::new_false(),
            },
        }
    }

    pub fn match_type_var_tuple(
        &mut self,
        i_s: &mut InferenceState,
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
                                    let types: Box<_> =
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

    fn match_or_add_type_var_in_type_var_matcher(
        &mut self,
        i_s: &mut InferenceState,
        type_var_usage: &TypeVarUsage,
        type_var: &TypeVar,
        value_type: &Type,
        variance: Variance,
    ) -> Match {
        let type_var_matcher = self.type_var_matcher.as_mut().unwrap();
        let type_var_like = &type_var_usage.type_var;
        if type_var_matcher.match_in_definition == type_var_usage.in_definition {
            let current =
                &mut type_var_matcher.calculated_type_vars[type_var_usage.index.as_usize()];
            if let BoundKind::TypeVar(current_type) = &mut current.type_ {
                let m = current_type.merge_or_mismatch(i_s, value_type, variance);
                return match m.bool() || !type_var.restrictions.is_empty() {
                    true => m,
                    false => match current.defined_by_result_context {
                        true => Match::new_false(),
                        false => Match::False {
                            reason: MismatchReason::CannotInferTypeArgument(type_var_usage.index),
                            similar: false,
                        },
                    },
                };
            } else {
                debug_assert!(!current.calculated(), "{current:?}");
            }
            // Before setting the type var, we need to check if the constraints match.
            let mut mismatch_constraints = false;
            if !type_var.restrictions.is_empty() {
                if let Some(DbType::TypeVar(t2)) = value_type.maybe_db_type() {
                    if !t2.type_var.restrictions.is_empty() {
                        if current.calculated() {
                            todo!()
                        } else if t2.type_var.restrictions.iter().all(|r2| {
                            type_var.restrictions.iter().any(|r1| {
                                Type::new(r1)
                                    .is_simple_super_type_of(i_s, &Type::new(r2))
                                    .bool()
                            })
                        }) {
                            current.type_ = BoundKind::TypeVar(TypeVarBound::Invariant(
                                value_type.as_db_type(i_s),
                            ));
                            return Match::new_true();
                        } else {
                            mismatch_constraints = true;
                        }
                    }
                }
                if !mismatch_constraints {
                    for restriction in type_var.restrictions.iter() {
                        let m = Type::new(restriction).simple_matches(i_s, value_type, variance);
                        if m.bool() {
                            if current.calculated() {
                                // This means that any is involved and multiple restrictions
                                // are matching. Therefore just return Any.
                                current.type_ =
                                    BoundKind::TypeVar(TypeVarBound::Invariant(DbType::Any));
                                return m;
                            }
                            current.type_ =
                                BoundKind::TypeVar(TypeVarBound::Invariant(restriction.clone()));
                            if !value_type.has_any(i_s) {
                                return m;
                            }
                        }
                    }
                    mismatch_constraints = true;
                }
            }
            if let Some(bound) = &type_var.bound {
                mismatch_constraints |= !Type::new(bound)
                    .is_simple_super_type_of(i_s, value_type)
                    .bool();
            }
            if mismatch_constraints {
                return Match::False {
                    reason: MismatchReason::ConstraintMismatch {
                        expected: value_type.as_db_type(i_s),
                        type_var: type_var_usage.type_var.clone(),
                    },
                    similar: false,
                };
            }
            current.type_ =
                BoundKind::TypeVar(TypeVarBound::new(value_type.as_db_type(i_s), variance));
            if matches!(value_type.maybe_db_type(), Some(DbType::Any)) {
                Match::True { with_any: true }
            } else {
                Match::new_true()
            }
        } else {
            if let Some(parent_matcher) = type_var_matcher.parent_matcher.as_mut() {
                todo!()
            }
            if let Some(class) = type_var_matcher.class {
                if class.node_ref.as_link() == type_var_usage.in_definition {
                    let g = class
                        .generics
                        .nth_usage(
                            i_s,
                            &TypeVarLikeUsage::TypeVar(Cow::Borrowed(type_var_usage)),
                        )
                        .expect_type_argument();
                    return g.simple_matches(i_s, value_type, type_var.variance);
                }
            }
            match type_var_matcher.func_or_callable {
                FunctionOrCallable::Function(f) => {
                    // If we're in a class context, we must also be in a method.
                    if let Some(func_class) = f.class {
                        if type_var_usage.in_definition == func_class.node_ref.as_link() {
                            // By definition, because the class did not match there will never be a
                            // type_var_remap that is not defined.
                            let type_var_remap = func_class.type_var_remap.unwrap();
                            let g = Generic::new(&type_var_remap[type_var_usage.index])
                                .expect_type_argument();
                            // The remapping of type vars needs to be checked now. In a lot of
                            // cases this is T -> T and S -> S, but it could also be T -> S and S
                            // -> List[T] or something completely arbitrary.
                            g.matches(i_s, self, value_type, type_var.variance)
                        } else {
                            // Happens e.g. for testInvalidNumberOfTypeArgs
                            // class C:  # Forgot to add type params here
                            //     def __init__(self, t: T) -> None: pass
                            if let Some(DbType::TypeVar(v)) = value_type.maybe_db_type() {
                                if v == type_var_usage {
                                    return Match::new_true();
                                }
                            }
                            todo!(
                                "TODO free type param annotations; searched ({:?}), found {:?}",
                                type_var_matcher.match_in_definition,
                                type_var_usage.in_definition,
                            )
                        }
                    } else {
                        todo!(
                            "Probably nested generic functions??? {:?} {:?}",
                            type_var_usage.in_definition,
                            type_var_matcher.match_in_definition
                        )
                    }
                }
                FunctionOrCallable::Callable(c) => todo!(),
            }
        }
    }

    pub fn match_or_add_param_spec(
        &mut self,
        i_s: &mut InferenceState,
        pre_param_spec_types: &[DbType],
        p1: &ParamSpecUsage,
        params2: &[CallableParam],
        variance: Variance,
    ) -> Match {
        debug_assert!(!self.is_matching_reverse());
        let mut params2_iterator = params2.iter().peekable();
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
        let Some(tv_matcher) = self.type_var_matcher.as_mut() else {
            return Match::new_false()
        };
        let params1 = if tv_matcher.match_in_definition == p1.in_definition {
            let calc = &mut tv_matcher.calculated_type_vars[p1.index.as_usize()];
            match &mut calc.type_ {
                BoundKind::CallableParams(params_current) => Cow::Borrowed(params_current),
                BoundKind::Uncalculated => {
                    calc.type_ = BoundKind::CallableParams(CallableParams::Simple(
                        params2_iterator.cloned().collect(),
                    ));
                    return matches;
                }
                _ => unreachable!(),
            }
        } else if let Some(class) = tv_matcher.class {
            if class.node_ref.as_link() == p1.in_definition {
                class.generics().nth_param_spec_usage(i_s, p1)
            } else {
                todo!()
            }
        } else {
            todo!()
        };
        match params1.as_ref() {
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
        }
    }

    pub fn match_param_spec_arguments<'db, 'b, 'c>(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        usage: &ParamSpecUsage,
        args: Box<[Argument<'db, 'b>]>,
        class: Option<&Class>,
        function: Option<&Function>,
        args_node_ref: &impl Fn() -> NodeRef<'c>,
        on_type_error: Option<OnTypeError<'db, '_>>,
    ) -> SignatureMatch {
        let params = if let Some(type_var_matcher) = &self.type_var_matcher {
            if type_var_matcher.match_in_definition == usage.in_definition {
                match &type_var_matcher.calculated_type_vars[usage.index.as_usize()].type_ {
                    BoundKind::CallableParams(params) => Cow::Borrowed(params),
                    // This means that an Any came along.
                    BoundKind::Uncalculated => return SignatureMatch::True,
                    BoundKind::TypeVar(_) | BoundKind::TypeVarTuple(_) => unreachable!(),
                }
            } else if let Some(class) = type_var_matcher.class {
                class.generics().nth_param_spec_usage(i_s, usage)
            } else {
                todo!("why?")
            }
        } else {
            todo!("When does this even happen?")
        };
        match params.as_ref() {
            CallableParams::Simple(params) => {
                let iter = InferrableParamIterator2::new(
                    i_s.db,
                    params.as_ref().iter(),
                    args.into_vec().into_iter(),
                );
                match_arguments_against_params(
                    i_s,
                    &mut Matcher::default(),
                    class,
                    function,
                    args_node_ref,
                    on_type_error,
                    iter,
                )
            }
            CallableParams::Any => SignatureMatch::True,
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
                            SignatureMatch::True
                        } else {
                            if let Some(on_type_error) = on_type_error {
                                (on_type_error.callback)(
                                    i_s,
                                    class,
                                    function,
                                    &last_arg,
                                    Box::from("TODO X"),
                                    Box::from("TODO Y"),
                                )
                            }
                            SignatureMatch::False { similar: false }
                        }
                    }
                    _ => todo!(),
                }
            }
        }
    }

    pub fn format_in_type_var_matcher(
        &self,
        usage: &TypeVarLikeUsage,
        format_data: &FormatData,
        params_style: ParamsStyle,
    ) -> Box<str> {
        let type_var_matcher = self.type_var_matcher.as_ref().unwrap();
        let i_s = &mut InferenceState::new(format_data.db);
        // In general this whole function should look very similar to the matches function, since
        // on mismatches this can be run.
        if type_var_matcher.match_in_definition == usage.in_definition() {
            let current = &type_var_matcher.calculated_type_vars[usage.index().as_usize()];
            match &current.type_ {
                BoundKind::TypeVar(bound) => bound.format(i_s, format_data.style),
                BoundKind::TypeVarTuple(ts) => ts.format(format_data),
                BoundKind::CallableParams(params) => params.format(format_data, params_style),
                BoundKind::Uncalculated => DbType::Never.format(format_data),
            }
        } else {
            match type_var_matcher.func_or_callable {
                FunctionOrCallable::Function(f) => {
                    if let Some(class) = type_var_matcher.class {
                        if class.node_ref.as_link() == usage.in_definition() {
                            return class.generics.nth_usage(i_s, usage).format(format_data);
                        }
                        let func_class = f.class.unwrap();
                        if usage.in_definition() == func_class.node_ref.as_link() {
                            let type_var_remap = func_class.type_var_remap.unwrap();
                            Generic::new(&type_var_remap[usage.index()]).format(format_data)
                        } else {
                            usage.format_without_matcher(
                                format_data.db,
                                format_data.style,
                                params_style,
                            )
                        }
                    } else {
                        todo!("Probably nested generic functions???")
                    }
                }
                FunctionOrCallable::Callable(c) => todo!(),
            }
        }
    }

    pub fn iter_calculated_type_vars(&mut self) -> std::slice::IterMut<CalculatedTypeVarLike> {
        if let Some(type_var_matcher) = self.type_var_matcher.as_mut() {
            type_var_matcher.calculated_type_vars.iter_mut()
        } else {
            unreachable!()
        }
    }

    pub fn replace_type_var_likes_for_nested_context(
        &self,
        i_s: &mut InferenceState,
        t: &DbType,
    ) -> DbType {
        if let Some(type_var_matcher) = self.type_var_matcher.as_ref() {
            type_var_matcher.replace_type_var_likes_for_nested_context(i_s, t)
        } else {
            unreachable!()
        }
    }

    pub fn set_all_contained_type_vars_to_any(&mut self, i_s: &mut InferenceState, type_: &DbType) {
        if let Some(matcher) = self.type_var_matcher.as_mut() {
            matcher.set_all_contained_type_vars_to_any(i_s, type_)
        }
    }

    pub fn has_already_matched_recursive_alias(
        &self,
        rec1: &RecursiveAlias,
        rec2: &DbType,
    ) -> bool {
        for checked in &self.checked_type_recursions {
            if rec1 == checked.recursive_alias1.as_ref() && rec2 == &checked.type2 {
                return true;
            }
        }
        false
    }

    pub fn add_checked_type_recursion(
        &mut self,
        recursive_alias1: Rc<RecursiveAlias>,
        type2: DbType,
    ) {
        self.checked_type_recursions.push(CheckedTypeRecursion {
            recursive_alias1,
            type2,
        })
    }
}
