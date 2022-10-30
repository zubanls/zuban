use std::borrow::Cow;

use super::params::has_overlapping_params;
use super::{
    matches_params, CalculatedTypeArguments, FormatData, Generics, Match, Matcher, MismatchReason,
};
use crate::database::{
    CallableContent, Database, DbType, TupleContent, TupleTypeArguments, TypeVarLike, UnionType,
    Variance,
};
use crate::debug;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::value::{Class, LookupResult, MroIterator, Value};

#[derive(Debug, Clone)]
#[allow(clippy::enum_variant_names)]
pub enum Type<'a> {
    // The reason why we do not use Class as a DbType as well is that this is an optimization to
    // avoid generating DbType for all possible cases (avoiding allocations).
    Class(Class<'a>),
    Type(Cow<'a, DbType>),
}

impl<'a> Type<'a> {
    pub fn new(t: &'a DbType) -> Self {
        Self::Type(Cow::Borrowed(t))
    }

    pub fn owned(t: DbType) -> Self {
        Self::Type(Cow::Owned(t))
    }

    pub fn union(self, i_s: &mut InferenceState, other: Self) -> Self {
        Self::owned(self.into_db_type(i_s).union(other.into_db_type(i_s)))
    }

    pub fn into_db_type(self, i_s: &mut InferenceState) -> DbType {
        match self {
            Self::Class(class) => class.as_db_type(i_s),
            Self::Type(t) => t.into_owned(),
        }
    }

    pub fn as_db_type(&self, i_s: &mut InferenceState) -> DbType {
        match self {
            Self::Class(class) => class.as_db_type(i_s),
            Self::Type(t) => t.clone().into_owned(),
        }
    }

    #[inline]
    pub fn maybe_class(&self, db: &'a Database) -> Option<Class<'_>> {
        match self {
            Self::Class(c) => Some(*c),
            Self::Type(t) => match t.as_ref() {
                DbType::Class(link, generics) => Some(Class::from_db_type(db, *link, generics)),
                _ => None,
            },
        }
    }

    pub fn maybe_db_type(&self) -> Option<&DbType> {
        match self {
            Self::Class(_) => None,
            Self::Type(t) => Some(t.as_ref()),
        }
    }

    pub fn overlaps(&self, i_s: &mut InferenceState, other: &Self) -> bool {
        match other.maybe_db_type() {
            Some(DbType::TypeVarLike(t2)) => match t2.type_var_like.as_ref() {
                TypeVarLike::TypeVar(t2_type_var) => {
                    return if let Some(bound) = &t2_type_var.bound {
                        self.overlaps(i_s, &Type::new(bound))
                    } else if !t2_type_var.restrictions.is_empty() {
                        t2_type_var
                            .restrictions
                            .iter()
                            .all(|r2| self.overlaps(i_s, &Type::new(r2)))
                    } else {
                        true
                    };
                }
                TypeVarLike::TypeVarTuple(_) => todo!(),
                TypeVarLike::ParamSpec(_) => todo!(),
            },
            Some(DbType::Union(union_type2)) => {
                return union_type2
                    .iter()
                    .any(|t| self.overlaps(i_s, &Type::new(t)))
            }
            Some(DbType::Any) => return false, // This is a fallback
            _ => (),
        }

        match self {
            Self::Class(class1) => match other {
                Self::Class(class2) => Self::overlaps_class(i_s, *class1, *class2),
                Self::Type(t2) => match t2.as_ref() {
                    DbType::Class(l, g) => {
                        Self::overlaps_class(i_s, *class1, Class::from_db_type(i_s.db, *l, g))
                    }
                    _ => false,
                },
            },
            Self::Type(t1) => match t1.as_ref() {
                DbType::Class(link, generics) => {
                    Type::Class(Class::from_db_type(i_s.db, *link, generics)).overlaps(i_s, other)
                }
                DbType::Type(t1) => match other {
                    Self::Type(ref t2) => match t2.as_ref() {
                        DbType::Type(t2) => Type::new(t1).overlaps(i_s, &Type::new(t2)),
                        _ => false,
                    },
                    _ => false,
                },
                DbType::Callable(c1) => match other {
                    Self::Type(ref t2) => match t2.as_ref() {
                        DbType::Callable(c2) => {
                            Type::new(&c1.result_type).overlaps(i_s, &Type::new(&c2.result_type))
                                && has_overlapping_params(i_s, &c1.params, &c2.params)
                        }
                        DbType::Type(t2) => Type::new(t1).overlaps(i_s, &Type::new(t2)),
                        _ => false,
                    },
                    _ => false,
                },
                DbType::Any => true,
                DbType::Never => todo!(),
                DbType::None => {
                    matches!(other, Self::Type(t2) if matches!(t2.as_ref(), DbType::None))
                }
                DbType::TypeVarLike(t1) => match t1.type_var_like.as_ref() {
                    TypeVarLike::TypeVar(t1_type_var) => {
                        if let Some(db_t) = &t1_type_var.bound {
                            Type::new(db_t).overlaps(i_s, other)
                        } else if !t1_type_var.restrictions.is_empty() {
                            todo!("{other:?}")
                        } else {
                            true
                        }
                    }
                    TypeVarLike::TypeVarTuple(_) => todo!(),
                    TypeVarLike::ParamSpec(_) => todo!(),
                },
                DbType::Tuple(t1) => match other {
                    Self::Type(t2) => match t2.as_ref() {
                        DbType::Tuple(t2) => Self::overlaps_tuple(i_s, t1, t2),
                        _ => false,
                    },
                    _ => false,
                },
                DbType::Union(union) => union.iter().any(|t| Type::new(t).overlaps(i_s, other)),
                DbType::Intersection(intersection) => todo!(),
                DbType::NewType(_) => todo!(),
                DbType::RecursiveAlias(_) => todo!(),
            },
        }
    }

    fn matches_internal(
        &self,
        i_s: &mut InferenceState,
        matcher: &mut Matcher,
        value_type: &Self,
        variance: Variance,
    ) -> Match {
        match self {
            Self::Class(class) => Self::matches_class(i_s, matcher, class, value_type),
            Self::Type(t1) => match t1.as_ref() {
                DbType::Class(link, generics) => Self::matches_class(
                    i_s,
                    matcher,
                    &Class::from_db_type(i_s.db, *link, generics),
                    value_type,
                ),
                DbType::Type(t1) => match value_type.maybe_db_type() {
                    Some(DbType::Type(t2)) => {
                        Type::new(t1).matches(i_s, matcher, &Type::new(t2), variance)
                    }
                    _ => Match::new_false(),
                },
                DbType::TypeVarLike(t1) => {
                    if matcher.is_matching_reverse() {
                        Match::new_false()
                    } else {
                        matcher.match_or_add_type_var(i_s, t1, value_type, variance)
                    }
                }
                DbType::Callable(c1) => match value_type {
                    Self::Type(ref t2) => match t2.as_ref() {
                        DbType::Type(t2) => match t2.as_ref() {
                            DbType::Class(link, generics) => {
                                let cls = Class::from_db_type(i_s.db, *link, generics);
                                // TODO the __init__ should actually be looked up on the original class, not
                                // the subclass
                                let lookup = cls.lookup_internal(i_s, "__init__");
                                if let LookupResult::GotoName(_, init) = lookup {
                                    let t2 = init.class_as_type(i_s);
                                    if let Some(DbType::Callable(c2)) = t2.maybe_db_type() {
                                        // Since __init__ does not have a return, We need to check the params
                                        // of the __init__ functions and the class as a return type separately.
                                        return Type::new(&c1.result_type).is_super_type_of(
                                            i_s,
                                            matcher,
                                            &Type::Class(cls),
                                        ) & matches_params(
                                            i_s,
                                            matcher,
                                            c1.params.as_ref().map(|p| p.iter()),
                                            c2.params.as_ref().map(|p| p.iter().skip(1)),
                                            Variance::Contravariant,
                                        );
                                    }
                                }
                                Match::new_false()
                            }
                            _ => {
                                if c1.params.is_none() {
                                    Type::new(&c1.result_type).is_super_type_of(
                                        i_s,
                                        matcher,
                                        &Type::new(t2.as_ref()),
                                    )
                                } else {
                                    Match::new_false()
                                }
                            }
                        },
                        DbType::Callable(c2) => Self::matches_callable(i_s, matcher, c1, c2),
                        _ => Match::new_false(),
                    },
                    _ => Match::new_false(),
                },
                DbType::None => {
                    matches!(value_type, Self::Type(ref t2) if matches!(t2.as_ref(), DbType::None))
                        .into()
                }
                DbType::Any => Match::new_true(),
                DbType::Never => Match::new_true(), // TODO is this correct?
                DbType::Tuple(t1) => match value_type {
                    Self::Type(t2) => match t2.as_ref() {
                        DbType::Tuple(t2) => {
                            let m: Match = Self::matches_tuple(i_s, matcher, t1, t2, variance);
                            m.similar_if_false()
                        }
                        _ => Match::new_false(),
                    },
                    _ => Match::new_false(),
                },
                DbType::Union(union_type1) => {
                    self.matches_union(i_s, matcher, union_type1, value_type, variance)
                }
                DbType::Intersection(intersection) => todo!(),
                DbType::NewType(new_type1) => match value_type.maybe_db_type() {
                    Some(DbType::NewType(new_type2)) => (new_type1 == new_type2).into(),
                    _ => Match::new_false(),
                },
                DbType::RecursiveAlias(rec1) => {
                    if let Some(class) = value_type.maybe_class(i_s.db) {
                        let g = rec1.calculated_db_type(i_s.db);
                        let cls_db_type = value_type.as_db_type(i_s);
                        // Classes like aliases can also be recursive in mypy, like `class B(List[B])`.
                        if matcher.has_already_matched_recursive_alias(rec1, &cls_db_type) {
                            return Match::new_true();
                        } else {
                            matcher.add_checked_type_recursion(rec1.clone(), cls_db_type);
                            return Type::new(g)
                                .matches_internal(i_s, matcher, value_type, variance);
                        }
                    }
                    match value_type.maybe_db_type() {
                        Some(t @ DbType::RecursiveAlias(rec2)) => {
                            if matcher.has_already_matched_recursive_alias(rec1, t) {
                                Match::new_true()
                            } else {
                                // We are going to check it, so we mark it as checked.
                                matcher.add_checked_type_recursion(rec1.clone(), t.clone());
                                let t1 = rec1.calculated_db_type(i_s.db);
                                let t2 = rec2.calculated_db_type(i_s.db);
                                Type::new(t1).matches_internal(
                                    i_s,
                                    matcher,
                                    &Type::new(t2),
                                    variance,
                                )
                            }
                        }
                        _ => {
                            let g = rec1.calculated_db_type(i_s.db);
                            Type::new(g).matches_internal(i_s, matcher, value_type, variance)
                        }
                    }
                }
            },
        }
    }

    pub fn is_sub_type_of(
        &self,
        i_s: &mut InferenceState,
        matcher: &mut Matcher,
        value_type: &Self,
    ) -> Match {
        matcher.match_reverse();
        let result = value_type.is_super_type_of(i_s, matcher, self);
        matcher.match_reverse();
        result
    }

    pub fn is_simple_sub_type_of(&self, i_s: &mut InferenceState, value_type: &Self) -> Match {
        self.is_sub_type_of(i_s, &mut Matcher::default(), value_type)
    }

    pub fn is_simple_super_type_of(&self, i_s: &mut InferenceState, value_type: &Self) -> Match {
        self.is_super_type_of(i_s, &mut Matcher::default(), value_type)
    }

    pub fn is_super_type_of(
        &self,
        i_s: &mut InferenceState,
        matcher: &mut Matcher,
        value_type: &Self,
    ) -> Match {
        // 1. Check if the type is part of the mro.
        let m = match value_type.mro(i_s) {
            Some(mro) => {
                for (_, t2) in mro {
                    let m = self.matches_internal(i_s, matcher, &t2, Variance::Covariant);
                    if !matches!(
                        m,
                        Match::False {
                            reason: MismatchReason::None,
                            similar: false
                        }
                    ) {
                        return m;
                    }
                }
                Match::new_false()
            }
            None => {
                let m = self.matches_internal(i_s, matcher, value_type, Variance::Covariant);
                m.or(|| self.matches_object_class(i_s.db, value_type))
            }
        };
        m.or(|| self.check_protocol_and_other_side(i_s, matcher, value_type, Variance::Covariant))
    }

    pub fn is_simple_same_type(&self, i_s: &mut InferenceState, value_type: &Self) -> Match {
        self.is_same_type(i_s, &mut Matcher::default(), value_type)
    }

    pub fn is_same_type(
        &self,
        i_s: &mut InferenceState,
        matcher: &mut Matcher,
        value_type: &Self,
    ) -> Match {
        let m = self.matches_internal(i_s, matcher, value_type, Variance::Invariant);
        m.or(|| self.check_protocol_and_other_side(i_s, matcher, value_type, Variance::Invariant))
    }

    pub fn simple_matches(
        &self,
        i_s: &mut InferenceState,
        value_type: &Self,
        variance: Variance,
    ) -> Match {
        self.matches(i_s, &mut Matcher::default(), value_type, variance)
    }

    pub fn matches(
        &self,
        i_s: &mut InferenceState,
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
        i_s: &mut InferenceState,
        matcher: &mut Matcher,
        value_type: &Self,
        variance: Variance,
    ) -> Match {
        // 2. Check if it is a class with a protocol
        if let Some(class1) = self.maybe_class(i_s.db) {
            // TODO this should probably be checked before normal mro checking?!
            if class1.class_infos(i_s).is_protocol {
                if let Some(class2) = value_type.maybe_class(i_s.db) {
                    return class1.check_protocol_match(i_s, class2).into();
                }
            }
        }
        // 3. Check if the value_type is special like Any or a Typevar and needs to be checked
        //    again.
        if let Type::Type(t2) = value_type {
            match t2.as_ref() {
                DbType::Any => {
                    let t1 = match self {
                        Self::Class(c) => Cow::Owned(c.as_db_type(i_s)),
                        Self::Type(t) => Cow::Borrowed(t.as_ref()),
                    };
                    matcher.set_all_contained_type_vars_to_any(i_s, &t1);
                    return Match::True { with_any: true };
                }
                DbType::None => return Match::new_true(),
                DbType::TypeVarLike(t2) => {
                    if matcher.is_matching_reverse() {
                        return matcher.match_or_add_type_var(i_s, t2, self, variance.invert());
                    }
                    if variance == Variance::Covariant {
                        if let TypeVarLike::TypeVar(t2_type_var) = t2.type_var_like.as_ref() {
                            if let Some(bound) = &t2_type_var.bound {
                                let m = self.simple_matches(i_s, &Type::new(bound), variance);
                                if m.bool() {
                                    return m;
                                }
                            } else if !t2_type_var.restrictions.is_empty() {
                                let m = t2_type_var.restrictions.iter().all(|r| {
                                    self.simple_matches(i_s, &Type::new(r), variance).bool()
                                });
                                if m {
                                    todo!();
                                    //return Match::new_true();
                                }
                            }
                        }
                    }
                }
                DbType::Intersection(i2) if variance == Variance::Covariant => {
                    if matcher.is_matching_reverse() {
                        todo!()
                    }
                    return i2
                        .iter()
                        .any(|t2| self.simple_matches(i_s, &Type::new(t2), variance).bool())
                        .into();
                }
                DbType::NewType(n2) => {
                    let t = n2.type_(i_s);
                    return self.matches(i_s, matcher, &Type::new(t), variance);
                }
                DbType::Never => return Match::new_true(), // TODO is this correct?
                _ => (),
            }
        }
        Match::new_false()
    }

    pub fn mro<'db: 'x, 'x>(
        &'x self,
        i_s: &mut InferenceState<'db, '_>,
    ) -> Option<MroIterator<'db, '_>> {
        match self {
            Self::Class(c) => Some(c.mro(i_s)),
            Self::Type(t) => {
                match t.as_ref() {
                    DbType::Class(link, generics) => {
                        Some(Class::from_db_type(i_s.db, *link, generics).mro(i_s))
                    }
                    DbType::Tuple(tup) => Some({
                        let class_infos = i_s.db.python_state.tuple().class_infos(i_s);
                        MroIterator::new(
                            i_s.db,
                            Type::new(t),
                            Some(Generics::DbType(match &tup.args {
                                Some(TupleTypeArguments::FixedLength(ts)) => {
                                    debug!("TODO Only used TypeVarIndex #0 for tuple, and not all of them");
                                    ts.get(0).unwrap_or(&DbType::Never)
                                }
                                Some(TupleTypeArguments::ArbitraryLength(t)) => t.as_ref(),
                                None => &DbType::Any,
                            })),
                            class_infos.mro.iter(),
                        )
                    }),
                    _ => None,
                }
            }
        }
    }

    fn matches_object_class(&self, db: &Database, value_type: &Type) -> Match {
        self.maybe_class(db)
            .map(|c| {
                let m = c.is_object_class(db);
                if m.bool()
                    && value_type
                        .maybe_db_type()
                        .map(|t| matches!(t, DbType::Any))
                        .unwrap_or(false)
                {
                    Match::True { with_any: true }
                } else {
                    m
                }
            })
            .unwrap_or_else(Match::new_false)
    }

    fn matches_union(
        &self,
        i_s: &mut InferenceState,
        matcher: &mut Matcher,
        u1: &UnionType,
        value_type: &Self,
        variance: Variance,
    ) -> Match {
        let match_reverse = matcher.is_matching_reverse();
        match value_type.maybe_db_type() {
            // TODO this should use the variance argument
            Some(DbType::Union(u2)) => match variance {
                Variance::Covariant => {
                    let mut matches = true;
                    if match_reverse {
                        for g1 in u1.iter() {
                            let t1 = Type::new(g1);
                            matches &= u2
                                .iter()
                                .any(|g2| t1.matches(i_s, matcher, &Type::new(g2), variance).bool())
                        }
                    } else {
                        for g2 in u2.iter() {
                            let t2 = Type::new(g2);
                            matches &= u1
                                .iter()
                                .any(|g1| Type::new(g1).matches(i_s, matcher, &t2, variance).bool())
                        }
                    }
                    matches.into()
                }
                Variance::Invariant => {
                    self.is_super_type_of(i_s, matcher, value_type)
                        & self.is_sub_type_of(i_s, matcher, value_type)
                }
                Variance::Contravariant => unreachable!(),
            },
            // TODO doesn't match_reverse also matter here?
            _ => u1
                .iter()
                .any(|g| {
                    Type::new(g)
                        .matches(i_s, matcher, value_type, variance)
                        .bool()
                })
                .into(),
        }
    }

    fn matches_class(
        i_s: &mut InferenceState,
        matcher: &mut Matcher,
        class1: &Class,
        value_type: &Type,
    ) -> Match {
        if let Some(class2) = value_type.maybe_class(i_s.db) {
            if class1.node_ref == class2.node_ref {
                if let Some(type_vars) = class1.type_vars(i_s) {
                    return class1
                        .generics()
                        .matches(i_s, matcher, class2.generics(), type_vars)
                        .similar_if_false();
                }
                return Match::new_true();
            }
        }
        Match::new_false()
    }

    fn matches_callable(
        i_s: &mut InferenceState,
        matcher: &mut Matcher,
        c1: &CallableContent,
        c2: &CallableContent,
    ) -> Match {
        if !matcher.has_type_var_matcher() {
            if let Some(c2_type_vars) = c2.type_vars.as_ref() {
                let mut calculated_type_vars = vec![];
                calculated_type_vars.resize_with(c2_type_vars.len(), Default::default);
                let mut matcher =
                    Matcher::new_reverse_callable_matcher(c2, &mut calculated_type_vars);
                return Type::matches_callable(i_s, &mut matcher, c1, c2);
            }
        }
        Type::new(&c1.result_type).is_super_type_of(i_s, matcher, &Type::new(&c2.result_type))
            & matches_params(
                i_s,
                matcher,
                c1.params.as_ref().map(|params| params.iter()),
                c2.params.as_ref().map(|params| params.iter()),
                Variance::Contravariant,
            )
    }

    fn matches_tuple(
        i_s: &mut InferenceState,
        matcher: &mut Matcher,
        t1: &TupleContent,
        t2: &TupleContent,
        variance: Variance,
    ) -> Match {
        use TupleTypeArguments::*;
        if matcher.has_type_var_matcher() {
            if let Some(ts) = t1.has_type_var_tuple() {
                return matcher.match_type_var_tuple(
                    i_s,
                    ts,
                    t2.args.as_ref().unwrap_or_else(|| todo!()),
                    variance,
                );
            }
        }
        match (&t1.args, &t2.args, variance) {
            (Some(tup1_args @ FixedLength(ts1)), Some(tup2_args @ FixedLength(ts2)), _) => {
                if ts1.len() == ts2.len() {
                    let mut matches = Match::new_true();
                    for (t1, t2) in ts1.iter().zip(ts2.iter()) {
                        matches &= Type::new(t1).matches(i_s, matcher, &Type::new(t2), variance);
                    }
                    matches
                } else {
                    Match::new_false()
                }
            }
            (Some(ArbitraryLength(t1)), Some(ArbitraryLength(t2)), _) => {
                Type::new(t1).matches(i_s, matcher, &Type::new(t2), variance)
            }
            (
                Some(tup1_args @ FixedLength(ts1)),
                Some(tup2_args @ ArbitraryLength(t2)),
                Variance::Covariant,
            ) => Match::new_false(),
            (Some(ArbitraryLength(t1)), Some(FixedLength(ts2)), Variance::Invariant) => {
                todo!()
            }
            (Some(ArbitraryLength(t1)), Some(FixedLength(ts2)), Variance::Covariant) => {
                let t1 = Type::new(t1);
                ts2.iter()
                    .all(|g2| {
                        let t2 = Type::new(g2);
                        t1.is_super_type_of(i_s, matcher, &t2).bool()
                    })
                    .into()
            }
            (Some(_), Some(_), _) => unreachable!(),
            (None, _, _) | (_, None, _) => Match::new_true(),
        }
    }

    fn overlaps_tuple(i_s: &mut InferenceState, t1: &TupleContent, t2: &TupleContent) -> bool {
        use TupleTypeArguments::*;
        match (&t1.args, &t2.args) {
            (Some(FixedLength(ts1)), Some(FixedLength(ts2))) => {
                let mut value_generics = ts2.iter();
                let mut overlaps = true;
                for type1 in ts1.iter() {
                    /*
                    if matcher.has_type_var_matcher() {
                        match type1 {
                            DbType::TypeVarLike(t) if t.is_type_var_tuple() => {
                                todo!()
                            }
                            _ => (),
                        }
                    }
                    */
                    if let Some(type2) = value_generics.next() {
                        overlaps &= Type::new(type1).overlaps(i_s, &Type::new(type2));
                    } else {
                        overlaps = false;
                    }
                }
                if value_generics.next().is_some() {
                    overlaps = false;
                }
                overlaps
            }
            (Some(ArbitraryLength(t1)), Some(ArbitraryLength(t2))) => {
                Type::new(t1.as_ref()).overlaps(i_s, &Type::new(t2.as_ref()))
            }
            (Some(ArbitraryLength(t1)), Some(FixedLength(ts2))) => {
                let t1 = Type::new(t1.as_ref());
                ts2.iter().all(|t2| t1.overlaps(i_s, &Type::new(t2)))
            }
            (Some(FixedLength(ts1)), Some(ArbitraryLength(t2))) => {
                let t2 = Type::new(t2.as_ref());
                ts1.iter().all(|t1| Type::new(t1).overlaps(i_s, &t2))
            }
            _ => true,
        }
    }

    pub fn overlaps_class(i_s: &mut InferenceState, class1: Class, class2: Class) -> bool {
        let check = {
            #[inline]
            |i_s: &mut InferenceState, t1: &Type, t2: &Type| {
                t1.maybe_class(i_s.db)
                    .and_then(|c1| {
                        t2.maybe_class(i_s.db).map(|c2| {
                            c1.node_ref == c2.node_ref && {
                                let type_vars = c1.type_vars(i_s);
                                c1.generics().overlaps(i_s, c2.generics(), type_vars)
                            }
                        })
                    })
                    .unwrap_or(false)
            }
        };

        for (_, c1) in class1.mro(i_s) {
            if check(i_s, &c1, &Type::Class(class2)) {
                return true;
            }
        }
        for (_, c2) in class2.mro(i_s) {
            if check(i_s, &Type::Class(class1), &c2) {
                return true;
            }
        }
        false
    }

    pub fn error_if_not_matches(
        &self,
        i_s: &mut InferenceState,
        value: &Inferred,
        callback: impl FnOnce(&mut InferenceState, Box<str>, Box<str>),
    ) -> Match {
        self.error_if_not_matches_with_matcher(
            i_s,
            &mut Matcher::default(),
            value,
            Some(|i_s: &mut InferenceState, t1, t2, reason: &MismatchReason| callback(i_s, t1, t2)),
        )
    }

    pub fn error_if_not_matches_with_matcher<'db>(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        matcher: &mut Matcher,
        value: &Inferred,
        callback: Option<
            impl FnOnce(&mut InferenceState<'db, '_>, Box<str>, Box<str>, &MismatchReason),
        >,
    ) -> Match {
        let value_type = value.class_as_type(i_s);
        let matches = self.is_super_type_of(i_s, matcher, &value_type);
        if let Match::False { ref reason, .. } = matches {
            let value_type = value.class_as_type(i_s);
            let mut fmt1 = FormatData::new_short(i_s.db);
            let mut fmt2 = FormatData::with_matcher(i_s.db, matcher);
            let mut input = value_type.format(&fmt1);
            let mut wanted = self.format(&fmt2);
            if input == wanted {
                fmt1.enable_verbose();
                fmt2.enable_verbose();
                input = value_type.format(&fmt1);
                wanted = self.format(&fmt2);
            }
            debug!(
                "Mismatch between {input:?} and {wanted:?} -> {:?}",
                matches.clone()
            );
            if let Some(callback) = callback {
                callback(i_s, input, wanted, reason)
            }
        }
        matches
    }

    pub fn try_to_resemble_context(
        self,
        i_s: &mut InferenceState,
        matcher: &mut Matcher,
        t: &Self,
    ) -> DbType {
        if let Some(class) = t.maybe_class(i_s.db) {
            if let Some(mro) = self.mro(i_s) {
                for (_, value_type) in mro {
                    if Self::matches_class(i_s, &mut Matcher::default(), &class, &value_type).bool()
                    {
                        return value_type.into_db_type(i_s);
                    }
                }
            }
        }
        if let Some(db_type) = t.maybe_db_type() {
            use TupleTypeArguments::*;
            match db_type {
                DbType::Tuple(t1) => {
                    if let Some(DbType::Tuple(t2)) = self.maybe_db_type() {
                        match (&t1.args, &t2.args) {
                            (Some(FixedLength(ts1)), Some(FixedLength(ts2))) => {
                                return DbType::Tuple(TupleContent::new_fixed_length(
                                    ts1.iter()
                                        .zip(ts2.iter())
                                        .map(|(g1, g2)| {
                                            Type::new(g2).try_to_resemble_context(
                                                i_s,
                                                matcher,
                                                &Type::new(g1),
                                            )
                                        })
                                        .collect(),
                                ))
                            }
                            (Some(ArbitraryLength(t1)), Some(ArbitraryLength(t2))) => {
                                return DbType::Tuple(TupleContent::new_arbitrary_length(
                                    Type::new(t1.as_ref()).try_to_resemble_context(
                                        i_s,
                                        matcher,
                                        &Type::new(t2.as_ref()),
                                    ),
                                ))
                            }
                            (Some(ArbitraryLength(t1)), Some(FixedLength(ts2))) => {
                                /*
                                let t1 = Type::new(t1);
                                generics2
                                    .iter()
                                    .all(|g2| {
                                        let t2 = Type::new(g2);
                                        t1.is_super_type_of(i_s, matcher, &t2).bool()
                                    })
                                    .into()
                                */
                                todo!()
                            }
                            (Some(FixedLength(ts1)), Some(ArbitraryLength(t2))) => unreachable!(),
                            _ => (),
                        }
                    }
                }
                DbType::TypeVarLike(t) => {
                    if matcher.has_type_var_matcher() {
                        let t =
                            Type::owned(matcher.replace_type_vars_for_nested_context(i_s, db_type));
                        return self.try_to_resemble_context(i_s, &mut Matcher::default(), &t);
                    }
                }
                DbType::Type(t1) => todo!(),
                _ => (),
            }
        }
        self.into_db_type(i_s)
    }

    pub fn execute_and_resolve_type_vars(
        &self,
        i_s: &mut InferenceState,
        class: Option<&Class>,
        calculated_type_args: &CalculatedTypeArguments,
    ) -> Inferred {
        let db_type = self.internal_resolve_type_vars(i_s, class, calculated_type_args);
        debug!(
            "Resolved type vars: {}",
            db_type.format(&FormatData::new_short(i_s.db))
        );
        Inferred::execute_db_type(i_s, db_type)
    }

    fn internal_resolve_type_vars(
        &self,
        i_s: &mut InferenceState,
        class: Option<&Class>,
        calculated_type_args: &CalculatedTypeArguments,
    ) -> DbType {
        match self {
            Self::Class(c) => c.as_db_type(i_s).replace_type_vars(&mut |t| {
                calculated_type_args.lookup_type_var_usage(i_s, class, t)
            }),
            Self::Type(t) => t.replace_type_vars(&mut |t| {
                calculated_type_args.lookup_type_var_usage(i_s, class, t)
            }),
        }
    }

    pub fn on_any_class(
        &self,
        i_s: &mut InferenceState,
        matcher: &mut Matcher,
        callable: &mut impl FnMut(&mut InferenceState, &mut Matcher, &Class) -> bool,
    ) -> bool {
        if let Some(class) = self.maybe_class(i_s.db) {
            callable(i_s, matcher, &class)
        } else {
            match self.maybe_db_type() {
                Some(DbType::Union(union_type)) => union_type
                    .iter()
                    .any(|t| Type::new(t).on_any_class(i_s, matcher, callable)),
                Some(db_type @ DbType::TypeVarLike(_)) => {
                    if matcher.has_type_var_matcher() {
                        Type::owned(matcher.replace_type_vars_for_nested_context(i_s, db_type))
                            .on_any_class(i_s, matcher, callable)
                    } else {
                        false
                    }
                }
                _ => false,
            }
        }
    }

    pub fn common_base_class(&self, i_s: &mut InferenceState, other: &Self) -> DbType {
        match (self.maybe_class(i_s.db), other.maybe_class(i_s.db)) {
            (Some(c1), Some(c2)) => {
                for (_, c1) in c1.mro(i_s) {
                    for (_, c2) in c2.mro(i_s) {
                        if c1.is_simple_same_type(i_s, &c2).bool() {
                            return c1.as_db_type(i_s);
                        }
                    }
                }
            }
            _ => return i_s.db.python_state.object_db_type(),
        }
        unreachable!("object is always a common base class")
    }

    pub fn is_any(&self) -> bool {
        matches!(self, Type::Type(t) if matches!(t.as_ref(), DbType::Any))
    }

    pub fn has_any(&self, i_s: &mut InferenceState) -> bool {
        match self {
            // TODO this does not not need to generate a db type
            Self::Class(c) => c.as_db_type(i_s).has_any(),
            Self::Type(t) => t.has_any(),
        }
    }

    pub fn lookup_symbol(&self, i_s: &mut InferenceState, name: &str) -> LookupResult {
        match self {
            Self::Class(c) => c.lookup_symbol(i_s, name),
            Self::Type(t) => match t.as_ref() {
                DbType::Class(c, generics) => todo!(),
                DbType::Tuple(t) => LookupResult::None, // TODO this probably omits index/count
                _ => todo!("{name:?} {self:?}"),
            },
        }
    }

    pub fn format(&self, format_data: &FormatData) -> Box<str> {
        match self {
            Self::Class(c) => c.format(format_data),
            Self::Type(t) => t.format(format_data),
        }
    }
}

pub fn common_base_class<'x, I: Iterator<Item = &'x DbType>>(
    i_s: &mut InferenceState,
    mut ts: I,
) -> DbType {
    if let Some(first) = ts.next() {
        let mut result = Cow::Borrowed(first);
        for t in ts {
            result = Cow::Owned(Type::Type(result).common_base_class(i_s, &Type::new(t)));
        }
        result.into_owned()
    } else {
        todo!("should probably return never")
    }
}
