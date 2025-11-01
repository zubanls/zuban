use std::sync::Arc;

use super::{
    CallableContent, ClassGenerics, FunctionOverload, Tuple, Type, TypeVarKind, TypeVarLike,
    UnionType, WithUnpack,
};
use crate::{
    database::MetaclassState,
    debug,
    file::ClassNodeRef,
    inference_state::InferenceState,
    matching::{
        ErrorStrs, ErrorTypes, GotType, Match, Matcher, MismatchReason, avoid_protocol_mismatch,
        format_got_expected,
    },
    params::matches_params,
    recoverable_error,
    type_::{
        AnyCause, CallableLike, CallableParams, LiteralKind, TupleArgs, TupleUnpack, Variance,
    },
    type_helpers::{Class, TypeOrClass},
};

impl Type {
    fn matches_internal(
        &self,
        i_s: &InferenceState,
        matcher: &mut Matcher,
        value_type: &Self,
        variance: Variance,
    ) -> Match {
        debug_assert_ne!(variance, Variance::Contravariant);
        match self {
            Type::Class(c) => Self::matches_class_against_type(
                i_s,
                matcher,
                &c.class(i_s.db),
                value_type,
                variance,
            ),
            Type::Type(t1) => match value_type {
                Type::Type(t2) => {
                    if matches!(t2.as_ref(), Type::NewType(_)) {
                        // NewType can never be subtyped as type[Any], because unlike all other
                        // types it is not an actual type and is more like a function.
                        Match::new_false()
                    } else {
                        let m = t1.matches(i_s, matcher, t2, variance);
                        if t2.is_union_like(i_s.db) {
                            m
                        } else {
                            m.similar_if_false()
                        }
                    }
                }
                Type::Union(_) => match t1.as_ref() {
                    Type::Union(u) => {
                        let repacked = Type::Union(UnionType::from_types(
                            u.iter().map(|t| Type::Type(Arc::new(t.clone()))).collect(),
                            u.might_have_type_vars,
                        ));
                        repacked.matches_internal(i_s, matcher, value_type, variance)
                    }
                    _ => Match::new_false(),
                },
                _ => match t1.as_ref() {
                    Type::Any(_)
                        if value_type
                            .maybe_class(i_s.db)
                            .is_some_and(|c| c.is_metaclass(i_s.db)) =>
                    {
                        Match::True {
                            with_any: matcher.is_matching_reverse(),
                        }
                    }
                    _ => Match::new_false(),
                },
            },
            Type::TypeVar(t1) => matcher.match_or_add_type_var(i_s, t1, value_type, variance),
            Type::Callable(c1) => {
                Self::matches_callable_against_arbitrary(i_s, matcher, c1, value_type, variance)
            }
            Type::None => (matches!(value_type, Type::None)
                || !i_s.flags().strict_optional && variance == Variance::Invariant)
                .into(),
            Type::Any(cause) => {
                matcher.set_all_contained_type_vars_to_any(value_type, *cause);
                Match::True {
                    with_any: matcher.is_matching_reverse() && !matches!(value_type, Type::Any(_)),
                }
            }
            Type::Never(_) => matches!(value_type, Type::Never(_)).into(),
            Type::Tuple(t1) => match value_type {
                Type::Tuple(t2) => {
                    match_tuple_type_arguments(i_s, matcher, &t1.args, &t2.args, variance)
                        .similar_if_false()
                }
                Type::NamedTuple(t2) => match_tuple_type_arguments(
                    i_s,
                    matcher,
                    &t1.args,
                    &t2.as_tuple().args,
                    variance,
                )
                .similar_if_false(),
                Type::ParamSpecArgs(_) => t1.args.is_any().into(),
                _ => Match::new_false(),
            },
            Type::Union(union_type1) => {
                self.matches_union(i_s, matcher, union_type1, value_type, variance)
            }
            Type::FunctionOverload(_) if variance == Variance::Invariant => self
                .matches_internal(i_s, matcher, value_type, Variance::Covariant)
                .or(|| value_type.matches_internal(i_s, matcher, self, Variance::Covariant)),
            Type::FunctionOverload(overload1) => match value_type {
                Type::FunctionOverload(overload2) => {
                    Self::matches_overload(i_s, matcher, overload1, overload2)
                }
                _ => Match::all(overload1.iter_functions(), |c1| {
                    Self::matches_callable_against_arbitrary(i_s, matcher, c1, value_type, variance)
                }),
            },
            Type::Literal(literal1) => match value_type {
                Type::Literal(literal2) => {
                    (literal1.value(i_s.db) == literal2.value(i_s.db)).into()
                }
                _ => Match::new_false(),
            },
            Type::NewType(new_type1) => match value_type {
                Type::NewType(new_type2) => (new_type1 == new_type2).into(),
                _ => Match::new_false(),
            },
            t1 @ Type::RecursiveType(rec1) => {
                match value_type {
                    t2 @ Type::Class(_) => {
                        // Classes like aliases can also be recursive in mypy, like `class B(List[B])`.
                        matcher.avoid_recursion(t1, t2, |matcher| {
                            if rec1.calculating(i_s.db) {
                                // Happens for example when creating the MRO of a class with a
                                // tuple base class.
                                return Match::new_false();
                            }
                            let g = rec1.calculated_type(i_s.db);
                            g.matches_internal(i_s, matcher, value_type, variance)
                        })
                    }
                    t2 @ Type::RecursiveType(rec2) => matcher.avoid_recursion(t1, t2, |matcher| {
                        let t1 = rec1.calculated_type(i_s.db);
                        let t2 = rec2.calculated_type(i_s.db);
                        t1.matches_internal(i_s, matcher, t2, variance)
                    }),
                    _ => {
                        let g = rec1.calculated_type(i_s.db);
                        g.matches_internal(i_s, matcher, value_type, variance)
                    }
                }
            }
            Type::Self_ => matcher.match_self(i_s, value_type, variance),
            Type::ParamSpecArgs(usage1) => match value_type {
                Type::ParamSpecArgs(usage2) => (usage1 == usage2).into(),
                _ => Match::new_false(),
            },
            Type::ParamSpecKwargs(usage1) => match value_type {
                Type::ParamSpecKwargs(usage2) => (usage1 == usage2).into(),
                _ => Match::new_false(),
            },
            Type::Dataclass(d1) => match value_type {
                Type::Dataclass(d2) => {
                    let c1 = d1.class(i_s.db);
                    let c2 = d2.class(i_s.db);
                    Self::matches_class(i_s, matcher, &c1, &c2, Variance::Covariant)
                }
                _ => Match::new_false(),
            },
            Type::TypedDict(d1) => match value_type {
                Type::TypedDict(d2) => {
                    let mut m = d1.matches(i_s, matcher, d2, false);
                    if variance == Variance::Invariant {
                        m &= d2.matches(i_s, matcher, d1, false);
                    }
                    m.similar_if_false()
                }
                _ => Match::new_false(),
            },
            Type::NamedTuple(nt1) => match value_type {
                Type::NamedTuple(nt2) => {
                    let c1 = &nt1.__new__;
                    let c2 = &nt2.__new__;
                    if c1.defined_at != c2.defined_at {
                        return Match::new_false();
                    }
                    matcher.avoid_recursion(self, value_type, |m| {
                        Type::Callable(c1.clone()).is_same_type(i_s, m, &Type::Callable(c2.clone()))
                    })
                }
                _ => Match::new_false(),
            },
            Type::Enum(e1) => match value_type {
                Type::Enum(e2) => (e1 == e2).into(),
                Type::EnumMember(member) => (e1 == &member.enum_).into(),
                _ => Match::new_false(),
            },
            Type::EnumMember(m1) => match value_type {
                Type::EnumMember(m2) => (m1.is_same_member(m2)).into(),
                _ => Match::new_false(),
            },
            Type::Module(file_index1) => {
                matches!(value_type, Type::Module(file_index2) if file_index1 == file_index2).into()
            }
            Type::Namespace(ns1) => matches!(value_type, Type::Namespace(ns2) if ns1 == ns2).into(),
            Type::Super { .. } => match value_type {
                Type::Super { .. } => (self == value_type).into(),
                _ => Match::new_false(),
            },
            Type::CustomBehavior(_) | Type::DataclassTransformObj(_) => Match::new_false(),
            Self::Intersection(intersection1) => Match::all(intersection1.iter_entries(), |t| {
                t.matches(i_s, matcher, value_type, variance)
            }),
            Self::LiteralString { .. } => match value_type {
                Self::LiteralString { .. } => Match::new_true(),
                Self::Literal(l) => match &l.kind {
                    LiteralKind::String(_) => Match::new_true(),
                    _ => Match::new_false(),
                },
                _ => Match::new_false(),
            },
        }
    }

    pub fn is_sub_type_of(
        &self,
        i_s: &InferenceState,
        matcher: &mut Matcher,
        value_type: &Self,
    ) -> Match {
        matcher.match_reverse(|matcher| value_type.is_super_type_of(i_s, matcher, self))
    }

    pub fn is_simple_sub_type_of(&self, i_s: &InferenceState, value_type: &Self) -> Match {
        self.is_sub_type_of(i_s, &mut Matcher::default(), value_type)
    }

    pub fn is_simple_super_type_of(&self, i_s: &InferenceState, value_type: &Self) -> Match {
        self.is_super_type_of(i_s, &mut Matcher::default(), value_type)
    }

    pub fn is_super_type_of(
        &self,
        i_s: &InferenceState,
        matcher: &mut Matcher,
        value_type: &Self,
    ) -> Match {
        // 1. Check if the type is part of the mro.
        let debug_message_for_result = |result| {
            if cfg!(feature = "zuban_debug") {
                let ErrorStrs { got, expected } = format_got_expected(i_s.db, self, value_type);
                debug!("Match covariant {got} :> {expected} -> {result:?}",)
            }
        };
        let mut m = Match::new_false();
        let mut mro = value_type.mro(i_s.db);
        // Protocols contain no object in its MRO, therefore we add that here.
        mro.returned_object = false;
        for (i, t2) in mro {
            m = match t2 {
                TypeOrClass::Class(c2) => match self.maybe_class(i_s.db) {
                    Some(c1) => Self::matches_class(i_s, matcher, &c1, &c2, Variance::Covariant),
                    None => {
                        // TODO performance: This might be slow, because it always
                        // allocates when e.g.  Foo is passed to def x(f: Foo | None): ...
                        // This is a bit unfortunate, especially because it loops over the
                        // mro and allocates every time.
                        let t2 = c2.as_type(i_s.db);
                        self.matches_internal(i_s, matcher, &t2, Variance::Covariant)
                    }
                },
                TypeOrClass::Type(t2) => {
                    self.matches_internal(i_s, matcher, &t2, Variance::Covariant)
                }
            };
            if !matches!(
                m,
                Match::False {
                    reason: MismatchReason::None,
                    similar: false
                }
            ) {
                if let Match::False {
                    reason: reason @ MismatchReason::ConstraintMismatch { .. },
                    ..
                } = &mut m
                    && i.0 != 0
                {
                    // If the constraint matched previously, but doesn't anymore, because we
                    // have a non-matching super class, the constraint was actually fine, but
                    // there were other issues.
                    *reason = MismatchReason::None;
                }
                debug_message_for_result(&m);
                return m;
            }
        }
        let result = m
            .or(|| {
                self.check_protocol_and_other_side(i_s, matcher, value_type, Variance::Covariant)
            })
            .or(|| {
                if let Some(class2) = value_type.maybe_class(i_s.db) {
                    if class2.incomplete_mro(i_s.db) && self.maybe_class(i_s.db).is_some() {
                        debug!(
                            "Match of class, because base class is incomplete: {}",
                            class2.format_short(i_s.db)
                        );
                        return Match::new_true();
                    }
                    if !matcher.ignore_promotions() {
                        return self.check_promotion(i_s, matcher, class2.node_ref);
                    }
                } else if let Type::Literal(literal) = value_type
                    && !matcher.ignore_promotions()
                {
                    return self.check_promotion(i_s, matcher, literal.fallback_node_ref(i_s.db));
                }
                Match::new_false()
            });
        debug_message_for_result(&result);
        result
    }

    #[inline]
    pub fn check_promotion(
        &self,
        i_s: &InferenceState,
        matcher: &mut Matcher,
        class2_node_ref: ClassNodeRef,
    ) -> Match {
        if matches!(self, Type::None) {
            // In no-strict optional cases we don't want to match.
            return Match::new_false();
        }
        let infos = class2_node_ref.use_cached_class_infos(i_s.db);
        if let Some(promote_to) = infos.promote_to() {
            let cls_node_ref = ClassNodeRef::from_link(i_s.db, promote_to);
            self.is_same_type(
                i_s,
                matcher,
                &Type::new_class(cls_node_ref.as_link(), ClassGenerics::None),
            )
            .or(|| self.check_promotion(i_s, matcher, cls_node_ref))
        } else {
            Match::new_false()
        }
    }

    pub fn is_simple_same_type(&self, i_s: &InferenceState, value_type: &Self) -> Match {
        self.is_same_type(i_s, &mut Matcher::default(), value_type)
    }

    pub fn is_same_type(
        &self,
        i_s: &InferenceState,
        matcher: &mut Matcher,
        value_type: &Self,
    ) -> Match {
        let m = self.matches_internal(i_s, matcher, value_type, Variance::Invariant);
        let result = m.or(|| {
            self.check_protocol_and_other_side(i_s, matcher, value_type, Variance::Invariant)
        });
        if cfg!(feature = "zuban_debug") {
            let ErrorStrs { got, expected } = format_got_expected(i_s.db, self, value_type);
            debug!("Match invariant {got} ≡ {expected} -> {result:?}");
        }
        result
    }

    pub fn simple_matches(
        &self,
        i_s: &InferenceState,
        value_type: &Self,
        variance: Variance,
    ) -> Match {
        self.matches(i_s, &mut Matcher::default(), value_type, variance)
    }

    pub fn matches(
        &self,
        i_s: &InferenceState,
        matcher: &mut Matcher,
        value_type: &Self,
        variance: Variance,
    ) -> Match {
        match variance {
            Variance::Covariant => self.is_super_type_of(i_s, matcher, value_type),
            Variance::Invariant => self.is_same_type(i_s, matcher, value_type),
            Variance::Contravariant => self.is_sub_type_of(i_s, matcher, value_type),
        }
    }

    fn check_protocol_and_other_side(
        &self,
        i_s: &InferenceState,
        matcher: &mut Matcher,
        value_type: &Self,
        variance: Variance,
    ) -> Match {
        let mut m = Match::new_false();
        // 2. Check if it is a class with a protocol
        if let Some(class1) = self.maybe_class(i_s.db)
            && class1.is_protocol(i_s.db)
            && variance == Variance::Covariant
        {
            m = avoid_protocol_mismatch(
                i_s.db,
                self,
                value_type,
                matcher.has_type_var_matcher(),
                || class1.check_protocol_match(i_s, matcher, value_type),
            );
            if m.bool() {
                return m;
            }
        }
        // 3. Check if the value_type is special like Any or a Typevar and needs to be checked
        //    again.
        match value_type {
            Type::Any(cause) => {
                matcher.set_all_contained_type_vars_to_any(self, *cause);
                return Match::True {
                    with_any: !matcher.is_matching_reverse(),
                };
            }
            Type::None if !i_s.flags().strict_optional => return Match::new_true(),
            Type::TypeVar(t2) => {
                if let Some(match_) =
                    matcher.match_or_add_type_var_reverse_if_responsible(i_s, t2, self, variance)
                {
                    return match_;
                }
                if variance == Variance::Covariant {
                    match t2.type_var.kind(i_s.db) {
                        TypeVarKind::Unrestricted => (),
                        TypeVarKind::Bound(bound) => {
                            let m = self.matches(i_s, matcher, bound, variance);
                            if m.bool() {
                                return m;
                            }
                        }
                        TypeVarKind::Constraints(mut constraints) => {
                            let m = constraints
                                .all(|r| self.simple_matches(i_s, r, variance).bool());
                            if m {
                                return Match::new_true();
                            }
                        }
                    }
                }
            }
            // Necessary to e.g. match int to Literal[1, 2]
            Type::Union(u2)
                // Union matching was already done.
                if !self.is_union_like(i_s.db) =>
            {
                return Match::all(u2.iter(), |t| self.matches(i_s, matcher, t, variance));
            }
            Type::Intersection(intersection2) => {
                return Match::any(intersection2.iter_entries(), |t| {
                    self.matches(i_s, matcher, t, variance)
                })
            }
            Type::NewType(n2) if variance == Variance::Covariant => {
                return self.matches(i_s, matcher, &n2.type_, variance);
            }
            Type::Never(_) if variance == Variance::Covariant => return Match::new_true(), // Never is assignable to anything
            Type::Self_ if variance == Variance::Covariant => {
                if matches!(self, Type::Self_) {
                    // This matching did already happen.
                    return Match::new_false()
                }
                if matcher.is_matching_reverse() {
                    if let Some(func_like) = matcher.func_like
                        && let Some(func_class) = func_like.class() {
                            return self.matches(
                                i_s,
                                matcher,
                                &func_class.as_type(i_s.db),
                                variance,
                            );
                        }
                } else if let Some(t) = i_s.current_type() {
                    return self.matches(i_s, matcher, &t, variance);
                }
            }
            Type::RecursiveType(rec2) => {
                if !rec2.calculating(i_s.db) {
                    return matcher.avoid_recursion(self, value_type, |matcher| {
                        let t2 = rec2.calculated_type(i_s.db);
                        self.matches(i_s, matcher, t2, variance)
                    });
                }
            }
            Type::Module(_) => {
                m = m.or(|| {
                    self.matches_internal(
                        i_s,
                        matcher,
                        &i_s.db.python_state.module_type(),
                        variance,
                    )
                })
            }
            _ => (),
        }
        m
    }

    fn matches_union(
        &self,
        i_s: &InferenceState,
        matcher: &mut Matcher,
        u1: &UnionType,
        value_type: &Self,
        variance: Variance,
    ) -> Match {
        let matches_true_and_false = || {
            // For covariance we want true and false to be present, for invariance, the entry count
            // has to match.
            u1.bool_literal_count() == 2
                && (variance == Variance::Covariant || u1.entries.len() == 2)
        };
        match value_type {
            Type::TypeVar(type_var2) if matcher.is_matching_reverse() => matcher
                .match_or_add_type_var_reverse_if_responsible(i_s, type_var2, self, variance)
                .unwrap_or(Match::new_false()),
            Type::Union(u2) => match variance {
                Variance::Covariant => Match::all(u2.iter(), |g2| {
                    self.matches_union(i_s, matcher, u1, g2, variance)
                }),
                Variance::Invariant => {
                    self.is_super_type_of(i_s, matcher, value_type)
                        & self.is_sub_type_of(i_s, matcher, value_type)
                }
                Variance::Contravariant => unreachable!(),
            },
            Type::Type(t) if matches!(t.as_ref(), Type::Union(_)) => {
                let Type::Union(u) = t.as_ref() else {
                    unreachable!();
                };
                let repacked = Type::Union(UnionType::from_types(
                    u.iter().map(|t| Type::Type(Arc::new(t.clone()))).collect(),
                    u.might_have_type_vars,
                ));
                self.matches_union(i_s, matcher, u1, &repacked, variance)
            }
            Type::Class(c2)
                if c2.link == i_s.db.python_state.bool_link() && matches_true_and_false() =>
            {
                Match::new_true()
            }
            _ => match variance {
                Variance::Covariant => {
                    Match::any(u1.iter(), |g| g.matches(i_s, matcher, value_type, variance))
                }
                Variance::Invariant => {
                    Match::all(u1.iter(), |g| g.matches(i_s, matcher, value_type, variance))
                }
                Variance::Contravariant => unreachable!(),
            },
        }
    }

    fn matches_class(
        i_s: &InferenceState,
        matcher: &mut Matcher,
        class1: &Class,
        class2: &Class,
        variance: Variance,
    ) -> Match {
        if class1.node_ref != class2.node_ref {
            return Match::new_false();
        }
        let type_vars = class1.type_vars(i_s);
        if !type_vars.is_empty() {
            class1.ensure_calculated_variance(i_s.db);
            let mut matches = Match::new_true();
            for ((t1, t2), tv) in class1
                .generics()
                .iter(i_s.db)
                .zip(class2.generics().iter(i_s.db))
                .zip(type_vars.iter())
            {
                let v = match tv {
                    TypeVarLike::TypeVar(t) if variance == Variance::Covariant => {
                        t.inferred_variance(i_s.db, class1)
                    }
                    TypeVarLike::TypeVar(t) if variance == Variance::Contravariant => {
                        t.inferred_variance(i_s.db, class1).invert()
                    }
                    TypeVarLike::TypeVar(_) => Variance::Invariant,
                    TypeVarLike::TypeVarTuple(_) | TypeVarLike::ParamSpec(_) => Variance::Covariant,
                };
                matches &= t1.matches(i_s, matcher, &t2, v);
            }

            if !matches.bool() {
                let mut check = |i_s: &InferenceState, n| {
                    let t1 = class1.nth_type_argument(i_s.db, n);
                    if matches!(t1, Type::Any(_)) {
                        return false;
                    }
                    let t2 = class2.nth_type_argument(i_s.db, n);
                    if matches!(t2, Type::Any(_)) {
                        return false;
                    }
                    t1.matches(i_s, matcher, &t2, variance).bool()
                };
                if class1.node_ref == i_s.db.python_state.list_node_ref() && check(i_s, 0) {
                    return Match::False {
                        similar: true,
                        reason: MismatchReason::SequenceInsteadOfListNeeded,
                    };
                } else if class1.node_ref == i_s.db.python_state.dict_node_ref()
                    && check(i_s, 0)
                    && check(i_s, 1)
                {
                    return Match::False {
                        similar: true,
                        reason: MismatchReason::MappingInsteadOfDictNeeded,
                    };
                }
            }
            return matches.similar_if_false();
        }
        Match::new_true()
    }

    fn matches_class_against_type(
        i_s: &InferenceState,
        matcher: &mut Matcher,
        class1: &Class,
        value_type: &Type,
        variance: Variance,
    ) -> Match {
        match value_type {
            Type::Class(c2) => {
                Self::matches_class(i_s, matcher, class1, &c2.class(i_s.db), variance)
            }
            Type::Type(t2) => {
                let result = match t2.as_ref() {
                    Type::TypeVar(tv) => match tv.type_var.kind(i_s.db) {
                        TypeVarKind::Bound(bound) => Self::matches_class_against_type(
                            i_s,
                            matcher,
                            class1,
                            &Type::Type(Arc::new(bound.clone())),
                            variance,
                        ),
                        TypeVarKind::Constraints(_) => {
                            debug!("TODO TypeVar constraint matching");
                            Match::new_true()
                        }
                        TypeVarKind::Unrestricted => Match::new_false(),
                    },
                    Type::Class(c2) => {
                        match c2.class(i_s.db).use_cached_class_infos(i_s.db).metaclass {
                            MetaclassState::Some(link) => {
                                // Protocols are handled separately
                                if class1.is_protocol(i_s.db) {
                                    return Match::new_false();
                                }
                                class1.as_type(i_s.db).matches(
                                    i_s,
                                    matcher,
                                    &Type::new_class(link, ClassGenerics::None),
                                    variance,
                                )
                            }
                            MetaclassState::Unknown => (class1.is_metaclass(i_s.db)
                                || class1.incomplete_mro(i_s.db))
                            .into(),
                            MetaclassState::None => Match::new_false(),
                        }
                    }
                    _ => Match::new_false(),
                };
                result.or(|| (class1.node_ref == i_s.db.python_state.bare_type_node_ref()).into())
            }
            Type::Literal(literal) if variance == Variance::Covariant => {
                Self::matches_class_against_type(
                    i_s,
                    matcher,
                    class1,
                    &literal.fallback_type(i_s.db),
                    variance,
                )
            }
            Type::NamedTuple(_)
                if class1.node_ref.as_link() == i_s.db.python_state.typinglike_namedtuple_link =>
            {
                Match::new_true()
            }
            Type::TypeVar(tv)
                if class1.node_ref == i_s.db.python_state.object_node_ref()
                    && tv.type_var.is_unrestricted() =>
            {
                // This is a bit special. We need to match object here, because object :> T and it
                // will not create the proper generics otherwise.
                matcher
                    .match_or_add_type_var_reverse_if_responsible(
                        i_s,
                        tv,
                        &i_s.db.python_state.object_type(),
                        variance,
                    )
                    .unwrap_or_else(Match::new_false)
            }
            Type::Union(u2) if class1.node_ref == i_s.db.python_state.bool_node_ref() => {
                (u2.bool_literal_count() == 2 && u2.entries.len() == 2).into()
            }
            Type::ParamSpecKwargs(_) if class1.is_dict_with_str_any(i_s.db) => Match::new_true(),
            Type::LiteralString { .. }
                if class1.node_ref == i_s.db.python_state.str_node_ref()
                    && variance == Variance::Covariant =>
            {
                Match::new_true()
            }
            Type::TypedDict(td) => {
                if class1.node_ref == i_s.db.python_state.dict_node_ref()
                    || class1.node_ref == i_s.db.python_state.mutable_mapping_node_ref()
                {
                    if let Some(got_value) = td.can_be_overwritten_with(i_s) {
                        return class1.nth_type_argument(i_s.db, 0).is_same_type(
                            i_s,
                            matcher,
                            &i_s.db.python_state.str_type(),
                        ) & class1
                            .nth_type_argument(i_s.db, 1)
                            .is_same_type(i_s, matcher, got_value);
                    }
                } else if class1.node_ref == i_s.db.python_state.mapping_node_ref() {
                    if td.has_extra_items(i_s.db) {
                        return class1.nth_type_argument(i_s.db, 0).is_same_type(
                            i_s,
                            matcher,
                            &i_s.db.python_state.str_type(),
                        ) & class1.nth_type_argument(i_s.db, 1).is_super_type_of(
                            i_s,
                            matcher,
                            &td.union_of_all_types(i_s),
                        );
                    }
                }
                Match::new_false()
            }
            _ => Match::new_false(),
        }
    }

    fn matches_callable_against_arbitrary(
        i_s: &InferenceState,
        matcher: &mut Matcher,
        c1: &CallableContent,
        value_type: &Self,
        variance: Variance,
    ) -> Match {
        debug_assert_ne!(variance, Variance::Contravariant);
        match value_type {
            Type::FunctionOverload(overload) if variance == Variance::Covariant => {
                // Since only one of the overloads is going to match, but all of them can change
                // the type var inference, we simply "backtrack" here.
                let old_matcher = matcher.clone();
                let mut need_matcher_backup = false;
                Match::any(overload.iter_functions(), |c2| {
                    if need_matcher_backup {
                        *matcher = old_matcher.clone();
                    }
                    need_matcher_backup = true;
                    matcher.matches_callable(i_s, c1, c2)
                })
            }
            Type::Type(t2) if matches!(c1.params, CallableParams::Any(_)) => {
                c1.return_type.matches(i_s, matcher, t2, variance)
            }
            Type::Type(t2) if t2.is_any() => {
                matcher.set_all_contained_type_vars_to_any(
                    &Type::Callable(Arc::new(c1.clone())),
                    AnyCause::Todo,
                );
                Match::new_true()
            }
            Type::Any(_) => {
                // Return false, because this case is handled in check_protocol_and_other_side.
                // We have to handle this to avoid expanding types below in maybe_callable and
                // recursing, if the return value is a recursive type definition.
                Match::new_false()
            }
            _ => match value_type.maybe_callable(i_s) {
                Some(CallableLike::Callable(c2)) => {
                    let mut m = matcher.matches_callable(i_s, c1, &c2);
                    if variance == Variance::Invariant {
                        m &= matcher.matches_callable(i_s, &c2, c1);
                    }
                    m
                }
                Some(CallableLike::Overload(overload)) if variance == Variance::Covariant => {
                    Self::matches_callable_against_arbitrary(
                        i_s,
                        matcher,
                        c1,
                        &Type::FunctionOverload(overload),
                        variance,
                    )
                }
                _ => Match::new_false(),
            },
        }
    }

    fn matches_overload(
        i_s: &InferenceState,
        matcher: &mut Matcher,
        overload1: &FunctionOverload,
        overload2: &FunctionOverload,
    ) -> Match {
        let mut previous_match_right_index: isize = -1;
        let mut matches = Match::new_true();
        'outer: for c1 in overload1.iter_functions() {
            for (right_index, c2) in overload2.iter_functions().enumerate() {
                let right_index = right_index as isize;
                let m = matcher.matches_callable(i_s, c1, c2);
                if m.bool() && right_index >= previous_match_right_index {
                    previous_match_right_index = right_index;
                    matches &= m;
                    continue 'outer;
                } else {
                    // An overload only matches if a params + return type match. However if only
                    // the return type differs and it's not a fallback, it might not match, see for
                    // example testSubtypeOverloadWithOverlappingArgumentsButWrongReturnType.
                    if right_index > previous_match_right_index
                        && (matches_params(i_s, &mut Matcher::default(), &c1.params, &c2.params)
                            .bool()
                            || matches_params(i_s, &mut Matcher::default(), &c2.params, &c1.params)
                                .bool())
                    {
                        return Match::new_false();
                    }
                }
            }
            return Match::new_false();
        }
        matches
    }
}

pub fn match_tuple_type_arguments(
    i_s: &InferenceState,
    matcher: &mut Matcher,
    tup1: &TupleArgs,
    tup2: &TupleArgs,
    variance: Variance,
) -> Match {
    let m = match_tuple_type_arguments_internal(i_s, matcher, tup1, tup2, variance);
    if !m.bool()
        && matcher.has_type_var_matcher()
        && matches!(
            tup2,
            TupleArgs::WithUnpack(WithUnpack {
                unpack: TupleUnpack::TypeVarTuple(_),
                ..
            })
        )
    {
        return m.or(|| {
            matcher.match_reverse(|matcher| {
                match_tuple_type_arguments_internal(i_s, matcher, tup2, tup1, variance.invert())
            })
        });
    }
    m
}

fn match_tuple_type_arguments_internal(
    i_s: &InferenceState,
    matcher: &mut Matcher,
    tup1: &TupleArgs,
    tup2: &TupleArgs,
    variance: Variance,
) -> Match {
    use TupleArgs::*;
    match (tup1, tup2) {
        (FixedLen(ts1), FixedLen(ts2)) => {
            if ts1.len() == ts2.len() {
                let mut matches = Match::new_true();
                for (t1, t2) in ts1.iter().zip(ts2.iter()) {
                    matches &= t1.matches(i_s, matcher, t2, variance);
                }
                matches
            } else {
                Match::new_false()
            }
        }
        (ArbitraryLen(t1), ArbitraryLen(t2)) => t1.matches(i_s, matcher, t2, variance),
        (WithUnpack(unpack), _) => {
            match_unpack_internal(i_s, matcher, unpack, tup2, variance, None, None)
        }
        (ArbitraryLen(t1), WithUnpack(u2)) => {
            match_arbitrary_len_vs_unpack(i_s, matcher, t1, u2, variance)
        }
        (FixedLen(_), WithUnpack(_)) => Match::new_false(),
        (FixedLen(_), ArbitraryLen(t2)) => t2.is_any().into(),
        (ArbitraryLen(t1), FixedLen(ts2)) => {
            if variance == Variance::Invariant {
                return matches!(t1.as_ref(), Type::Any(_)).into();
            }
            ts2.iter()
                .all(|t2| t1.matches(i_s, matcher, t2, variance).bool())
                .into()
        }
    }
}

pub fn match_arbitrary_len_vs_unpack(
    i_s: &InferenceState,
    matcher: &mut Matcher,
    t1: &Type,
    with_unpack: &WithUnpack,
    variance: Variance,
) -> Match {
    let mut matches = Match::new_true();
    for t2 in with_unpack.before.iter() {
        matches &= t1.matches(i_s, matcher, t2, variance)
    }
    match &with_unpack.unpack {
        TupleUnpack::TypeVarTuple(tvt) => {
            matches &= matcher.match_or_add_type_var_tuple(
                i_s,
                tvt,
                TupleArgs::ArbitraryLen(t1.clone().into()),
                variance,
            )
        }
        TupleUnpack::ArbitraryLen(inner_t2) => {
            matches &= t1.matches(i_s, matcher, inner_t2, variance);
        }
    }
    for t2 in with_unpack.after.iter() {
        matches &= t1.matches(i_s, matcher, t2, variance)
    }
    matches
}

type OnMismatch<'x> = &'x dyn Fn(ErrorTypes, isize);

pub fn match_unpack(
    i_s: &InferenceState,
    matcher: &mut Matcher,
    with_unpack1: &WithUnpack,
    tup2: &TupleArgs,
    variance: Variance,
    on_mismatch: Option<OnMismatch>,
    on_too_few_args: Option<&dyn Fn()>,
) -> Match {
    debug_assert!(!matcher.is_matching_reverse());
    match_unpack_internal(
        i_s,
        matcher,
        with_unpack1,
        tup2,
        variance,
        on_mismatch,
        on_too_few_args,
    )
}

fn match_unpack_internal(
    i_s: &InferenceState,
    matcher: &mut Matcher,
    with_unpack1: &WithUnpack,
    tuple2: &TupleArgs,
    variance: Variance,
    on_mismatch: Option<OnMismatch>,
    on_too_few_args: Option<&dyn Fn()>,
) -> Match {
    let mut matches = Match::new_true();

    let check_type = |matcher: &mut _, t1: &Type, t2, index| {
        let match_ = t1.matches(i_s, matcher, t2, variance);
        if let Match::False { reason, .. } = &match_
            && let Some(on_mismatch) = on_mismatch
        {
            on_mismatch(
                ErrorTypes {
                    matcher: Some(matcher),
                    reason,
                    expected: t1,
                    got: GotType::Type(t2),
                },
                index,
            );
        }
        match_
    };
    let check_type_var_tuple = |matcher: &mut Matcher, tvt, args: TupleArgs| {
        let m = matcher.match_or_add_type_var_tuple(i_s, tvt, args.clone(), variance);
        if !m.bool()
            && let Match::False { reason, .. } = &m
            && let Some(on_mismatch) = on_mismatch
        {
            on_mismatch(
                ErrorTypes {
                    matcher: Some(matcher),
                    reason,
                    expected: &Type::Tuple(Tuple::new(TupleArgs::WithUnpack(with_unpack1.clone()))),
                    got: GotType::Type(&Type::Tuple(Tuple::new(args))),
                },
                with_unpack1.before.len() as isize,
            );
        }
        m
    };

    match tuple2 {
        TupleArgs::FixedLen(ts2) => {
            let mut t2_iterator = ts2.iter().enumerate();
            for (t1, (i, t2)) in with_unpack1.before.iter().zip(t2_iterator.by_ref()) {
                matches &= check_type(matcher, t1, t2, i as isize);
            }
            for (t1, (i, t2)) in with_unpack1
                .after
                .iter()
                .rev()
                .zip(t2_iterator.by_ref().rev())
            {
                matches &= check_type(matcher, t1, t2, i as isize);
            }
            if (with_unpack1.before.len() + with_unpack1.after.len()) > ts2.len() {
                if let Some(on_too_few_args) = on_too_few_args {
                    on_too_few_args()
                }
                return Match::new_false();
            } else {
                match &with_unpack1.unpack {
                    TupleUnpack::TypeVarTuple(tvt) => {
                        matches &= check_type_var_tuple(
                            matcher,
                            tvt,
                            TupleArgs::FixedLen(t2_iterator.map(|(_, t2)| t2.clone()).collect()),
                        )
                    }
                    TupleUnpack::ArbitraryLen(inner_t1) => {
                        for (i, t2) in t2_iterator {
                            matches &= check_type(matcher, inner_t1, t2, i as isize)
                        }
                    }
                }
            }
        }
        TupleArgs::WithUnpack(with_unpack2) => {
            let mut before2_it = with_unpack2.before.iter();
            for (i, (t1, t2)) in with_unpack1
                .before
                .iter()
                .zip(before2_it.by_ref())
                .enumerate()
            {
                matches &= check_type(matcher, t1, t2, i as isize)
            }

            let mut after2_it = with_unpack2.after.iter();
            for (i, (t1, t2)) in with_unpack1
                .after
                .iter()
                .rev()
                .zip(after2_it.by_ref().rev())
                .enumerate()
            {
                matches &= check_type(matcher, t1, t2, -(i as isize) - 1)
            }

            match &with_unpack1.unpack {
                TupleUnpack::TypeVarTuple(tvt1) => {
                    let len_before_1 = with_unpack1.before.len();
                    let len_before_2 = with_unpack2.before.len();
                    if len_before_1 > len_before_2 {
                        if let Some(on_mismatch) = on_mismatch {
                            on_mismatch(
                                ErrorTypes {
                                    matcher: Some(matcher),
                                    reason: &MismatchReason::None,
                                    expected: &with_unpack1.before[len_before_2],
                                    got: GotType::Starred(Type::Tuple(Tuple::new(tuple2.clone()))),
                                },
                                len_before_1 as isize,
                            );
                            if let Some(on_too_few_args) = on_too_few_args {
                                on_too_few_args()
                            }
                        }
                        return Match::new_false();
                    } else if with_unpack1.after.len() > with_unpack2.after.len() {
                        if let Some(on_too_few_args) = on_too_few_args {
                            on_too_few_args()
                        }
                        return Match::new_false();
                    }
                    matches &= check_type_var_tuple(
                        matcher,
                        tvt1,
                        TupleArgs::WithUnpack(WithUnpack {
                            before: before2_it.cloned().collect(),
                            unpack: with_unpack2.unpack.clone(),
                            after: after2_it.cloned().collect(),
                        }),
                    )
                }
                TupleUnpack::ArbitraryLen(inner_t1) => {
                    for (i, t2) in before2_it.enumerate() {
                        matches &= check_type(matcher, inner_t1, t2, i as isize);
                    }
                    for (i, t2) in after2_it.enumerate() {
                        matches &= check_type(matcher, inner_t1, t2, -(i as isize));
                    }
                    match &with_unpack2.unpack {
                        TupleUnpack::TypeVarTuple(tvt2) => {
                            matches &= check_type_var_tuple(
                                matcher,
                                tvt2,
                                TupleArgs::ArbitraryLen(Arc::new(inner_t1.clone())),
                            )
                        }
                        TupleUnpack::ArbitraryLen(inner_t2) => {
                            matches &= inner_t1.matches(i_s, matcher, inner_t2, variance);
                        }
                    }
                }
            };
        }
        TupleArgs::ArbitraryLen(t2) => {
            if t2.is_any() {
                return Match::True { with_any: true };
            }
            if !with_unpack1.before.is_empty() || !with_unpack1.after.is_empty() {
                return Match::new_false();
            }
            match &with_unpack1.unpack {
                TupleUnpack::TypeVarTuple(tvt) => {
                    matches &=
                        check_type_var_tuple(matcher, tvt, TupleArgs::ArbitraryLen(t2.clone()))
                }
                TupleUnpack::ArbitraryLen(_) => {
                    recoverable_error!(
                        "Arbitrary len with unpacks should not exist without before and \
                                  after. They should be simplified to normal arbitrary len"
                    )
                }
            }
        }
    };
    matches
}
