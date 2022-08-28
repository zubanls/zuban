use std::borrow::Cow;

use super::params::has_overlapping_params;
use super::{
    matches_params, CalculatedTypeArguments, Generics, Match, MismatchReason, TypeVarMatcher,
};
use crate::database::{
    CallableContent, Database, DbType, FormatStyle, TupleContent, UnionType, Variance,
};
use crate::debug;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::value::{Class, LookupResult, MroIterator, Value};

#[derive(Debug, Clone)]
#[allow(clippy::enum_variant_names)]
pub enum Type<'db, 'a> {
    // The reason why we do not use Class as a DbType as well is that this is an optimization to
    // avoid generating DbType for all possible cases (avoiding allocations).
    Class(Class<'db, 'a>),
    Type(Cow<'a, DbType>),
}

impl<'db, 'a> Type<'db, 'a> {
    pub fn new(t: &'a DbType) -> Self {
        Self::Type(Cow::Borrowed(t))
    }

    pub fn owned(t: DbType) -> Self {
        Self::Type(Cow::Owned(t))
    }

    pub fn union(self, i_s: &mut InferenceState<'db, '_>, other: Self) -> Self {
        Self::owned(self.into_db_type(i_s).union(other.into_db_type(i_s)))
    }

    pub fn into_db_type(self, i_s: &mut InferenceState<'db, '_>) -> DbType {
        match self {
            Self::Class(class) => class.as_db_type(i_s),
            Self::Type(t) => t.into_owned(),
        }
    }

    pub fn as_db_type(&self, i_s: &mut InferenceState<'db, '_>) -> DbType {
        match self {
            Self::Class(class) => class.as_db_type(i_s),
            Self::Type(t) => t.clone().into_owned(),
        }
    }

    #[inline]
    pub fn maybe_class(&self, db: &'db Database) -> Option<Class<'db, '_>> {
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

    pub fn overlaps(&self, i_s: &mut InferenceState<'db, '_>, other: &Self) -> bool {
        match other.maybe_db_type() {
            Some(DbType::TypeVar(t2)) => {
                return if let Some(bound) = &t2.type_var.bound {
                    self.overlaps(i_s, &Type::new(bound))
                } else if !t2.type_var.restrictions.is_empty() {
                    t2.type_var
                        .restrictions
                        .iter()
                        .all(|r2| self.overlaps(i_s, &Type::new(r2)))
                } else {
                    true
                };
            }
            Some(DbType::Union(union_type2)) => {
                return union_type2
                    .iter()
                    .any(|t| self.overlaps(i_s, &Type::new(t)))
            }
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
                DbType::TypeVar(t1) => {
                    if let Some(db_t) = &t1.type_var.bound {
                        Type::new(db_t).overlaps(i_s, other)
                    } else if !t1.type_var.restrictions.is_empty() {
                        todo!("{other:?}")
                    } else {
                        true
                    }
                }
                DbType::Tuple(t1) => match other {
                    Self::Type(t2) => match t2.as_ref() {
                        DbType::Tuple(t2) => Self::overlaps_tuple(i_s, t1, t2),
                        _ => false,
                    },
                    _ => false,
                },
                DbType::Union(union_type) => {
                    union_type.iter().any(|t| Type::new(t).overlaps(i_s, other))
                }
            },
        }
    }

    fn is_same_type_internal(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        mut matcher: Option<&mut TypeVarMatcher<'db, '_>>,
        value_type: &Self,
        variance: Variance,
    ) -> Match {
        match self {
            Self::Class(class) => Self::matches_class(i_s, matcher, class, value_type, variance),
            Self::Type(t1) => match t1.as_ref() {
                DbType::Class(link, generics) => Self::matches_class(
                    i_s,
                    matcher,
                    &Class::from_db_type(i_s.db, *link, generics),
                    value_type,
                    variance,
                ),
                DbType::Type(t1) => match value_type.maybe_db_type() {
                    Some(DbType::Type(t2)) => {
                        Type::new(t1).matches(i_s, matcher, &Type::new(t2), variance)
                    }
                    _ => Match::new_false(),
                },
                DbType::TypeVar(t1) => match matcher {
                    Some(matcher) => {
                        if matcher.match_reverse {
                            Match::new_false()
                        } else {
                            matcher.match_or_add_type_var(i_s, t1, value_type, variance)
                        }
                    }
                    None => match value_type.maybe_db_type() {
                        Some(DbType::TypeVar(t2)) => {
                            (t1.index == t2.index && t1.in_definition == t2.in_definition).into()
                        }
                        _ => Match::new_false(),
                    },
                },
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
                                        return Type::new(&c1.result_type).is_sub_type(
                                            i_s,
                                            matcher.as_deref_mut(),
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
                                    Type::new(&c1.result_type).is_sub_type(
                                        i_s,
                                        matcher.as_deref_mut(),
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
                DbType::Any => match value_type {
                    Self::Type(ref t2) if matches!(t2.as_ref(), DbType::Any) => Match::TrueWithAny,
                    _ => Match::True,
                },
                DbType::Never => todo!(),
                DbType::Tuple(t1) => match value_type {
                    Self::Type(t2) => match t2.as_ref() {
                        DbType::Tuple(t2) => {
                            let m: Match = Self::matches_tuple(i_s, matcher, t1, t2, variance);
                            m.similar_if_false()
                        }
                        _ => Match::new_false(),
                    },
                    _ => Match::False(MismatchReason::None),
                },
                DbType::Union(union_type1) => {
                    self.matches_union(i_s, matcher, union_type1, value_type, variance)
                }
            },
        }
    }

    pub fn is_super_type(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        matcher: Option<&mut TypeVarMatcher<'db, '_>>,
        value_type: &Self,
    ) -> Match {
        if let Some(matcher) = matcher {
            let old = matcher.match_reverse;
            matcher.match_reverse = !old;
            let result = value_type.is_sub_type(i_s, Some(matcher), self);
            matcher.match_reverse = old;
            result
        } else {
            value_type.is_sub_type(i_s, None, self)
        }
    }

    pub fn is_sub_type(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        mut matcher: Option<&mut TypeVarMatcher<'db, '_>>,
        value_type: &Self,
    ) -> Match {
        // 1. Check if the type is part of the mro.
        let m = match value_type.mro(i_s) {
            Some(mro) => {
                for (_, t2) in mro {
                    let m = self.is_same_type_internal(
                        i_s,
                        matcher.as_deref_mut(),
                        &t2,
                        Variance::Covariant,
                    );
                    if !matches!(m, Match::False(MismatchReason::None)) {
                        return m;
                    }
                }
                Match::new_false()
            }
            None => {
                let m = self.is_same_type_internal(
                    i_s,
                    matcher.as_deref_mut(),
                    value_type,
                    Variance::Covariant,
                );
                m.or(|| self.matches_object_class(i_s.db, value_type))
            }
        };
        m.or(|| {
            self.check_protocol_and_other_side(
                i_s,
                matcher.as_deref_mut(),
                value_type,
                Variance::Covariant,
            )
        })
    }

    pub fn is_same_type(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        mut matcher: Option<&mut TypeVarMatcher<'db, '_>>,
        value_type: &Self,
    ) -> Match {
        let m = self.is_same_type_internal(
            i_s,
            matcher.as_deref_mut(),
            value_type,
            Variance::Invariant,
        );
        m.or(|| {
            self.check_protocol_and_other_side(
                i_s,
                matcher.as_deref_mut(),
                value_type,
                Variance::Invariant,
            )
        })
    }

    pub fn matches(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        mut matcher: Option<&mut TypeVarMatcher<'db, '_>>,
        value_type: &Self,
        variance: Variance,
    ) -> Match {
        match variance {
            Variance::Covariant => self.is_sub_type(i_s, matcher, value_type),
            Variance::Invariant => self.is_same_type(i_s, matcher, value_type),
            Variance::Contravariant => {
                return self.is_super_type(i_s, matcher.as_deref_mut(), value_type);
            }
        }
    }

    fn check_protocol_and_other_side(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        mut matcher: Option<&mut TypeVarMatcher<'db, '_>>,
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
                    if let Some(matcher) = matcher.as_deref_mut() {
                        let t1 = match self {
                            Self::Class(c) => Cow::Owned(c.as_db_type(i_s)),
                            Self::Type(t) => Cow::Borrowed(t.as_ref()),
                        };
                        matcher.set_all_contained_type_vars_to_any(i_s, t1.as_ref())
                    }
                    return Match::TrueWithAny;
                }
                DbType::None => return Match::True,
                DbType::TypeVar(t2) => {
                    if let Some(matcher) = matcher {
                        if matcher.match_reverse {
                            return matcher.match_or_add_type_var(i_s, t2, self, variance.invert());
                        }
                    }
                    if variance == Variance::Covariant {
                        if let Some(bound) = &t2.type_var.bound {
                            let m = self.matches(i_s, None, &Type::new(bound), variance);
                            if m.bool() {
                                return m;
                            }
                        } else if !t2.type_var.restrictions.is_empty() {
                            let m =
                                t2.type_var.restrictions.iter().all(|r| {
                                    self.matches(i_s, None, &Type::new(r), variance).bool()
                                });
                            if m {
                                todo!();
                                //return Match::True;
                            }
                        }
                    }
                }
                DbType::Never => return Match::True, // TODO is this correct?
                _ => (),
            }
        }
        Match::new_false()
    }

    fn mro(&self, i_s: &mut InferenceState<'db, '_>) -> Option<MroIterator<'db, '_>> {
        match self {
            Self::Class(c) => Some(c.mro(i_s)),
            Self::Type(t) => match t.as_ref() {
                DbType::Class(link, generics) => {
                    Some(Class::from_db_type(i_s.db, *link, generics).mro(i_s))
                }
                DbType::Tuple(tup) => Some({
                    let class_infos = i_s.db.python_state.tuple().class_infos(i_s);
                    if !tup.arbitrary_length {
                        debug!("TODO Only used TypeVarIndex #0 for tuple, and not all of them");
                    }
                    MroIterator::new(
                        i_s.db,
                        Type::new(t),
                        Some(Generics::DbType(
                            tup.generics
                                .as_ref()
                                .map(|g| g.nth(0.into()).unwrap_or(&DbType::Never))
                                .unwrap_or(&DbType::Any),
                        )),
                        class_infos.mro.iter(),
                    )
                }),
                _ => None,
            },
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
                    Match::TrueWithAny
                } else {
                    m
                }
            })
            .unwrap_or_else(Match::new_false)
    }

    fn matches_union(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        mut matcher: Option<&mut TypeVarMatcher<'db, '_>>,
        u1: &UnionType,
        value_type: &Self,
        variance: Variance,
    ) -> Match {
        match value_type.maybe_db_type() {
            // TODO this should use the variance argument
            Some(DbType::Union(u2)) => match variance {
                Variance::Covariant => {
                    let mut matches = true;
                    for g2 in u2.iter() {
                        let t2 = Type::new(g2);
                        matches &= u1.iter().any(|g1| {
                            Type::new(g1)
                                .matches(i_s, matcher.as_deref_mut(), &t2, variance)
                                .bool()
                        })
                    }
                    matches.into()
                }
                Variance::Invariant => {
                    self.is_sub_type(i_s, matcher, value_type)
                        & self.is_super_type(i_s, None, value_type)
                }
                Variance::Contravariant => unreachable!(),
            },
            _ => u1
                .iter()
                .any(|g| {
                    Type::new(g)
                        .matches(i_s, matcher.as_deref_mut(), value_type, variance)
                        .bool()
                })
                .into(),
        }
    }

    fn matches_class(
        i_s: &mut InferenceState<'db, '_>,
        matcher: Option<&mut TypeVarMatcher<'db, '_>>,
        class1: &Class<'db, '_>,
        value_type: &Self,
        variance: Variance,
    ) -> Match {
        if let Some(class2) = value_type.maybe_class(i_s.db) {
            if class1.node_ref == class2.node_ref {
                let type_vars = class1.type_vars(i_s);
                return class1
                    .generics()
                    .matches(i_s, matcher, class2.generics(), variance, type_vars)
                    .similar_if_false();
            }
        }
        Match::new_false()
    }

    fn matches_callable(
        i_s: &mut InferenceState<'db, '_>,
        mut matcher: Option<&mut TypeVarMatcher<'db, '_>>,
        c1: &CallableContent,
        c2: &CallableContent,
    ) -> Match {
        if matcher.is_none() {
            if let Some(c2_type_vars) = c2.type_vars.as_ref() {
                let mut calculated_type_vars = vec![];
                calculated_type_vars.resize_with(c2_type_vars.len(), Default::default);
                let mut matcher = TypeVarMatcher::new_callable(c2, &mut calculated_type_vars);
                matcher.match_reverse = true;
                return Type::matches_callable(i_s, Some(&mut matcher), c1, c2);
            }
        }
        Type::new(&c1.result_type).is_sub_type(
            i_s,
            matcher.as_deref_mut(),
            &Type::new(&c2.result_type),
        ) & matches_params(
            i_s,
            matcher,
            c1.params.as_ref().map(|params| params.iter()),
            c2.params.as_ref().map(|params| params.iter()),
            Variance::Contravariant,
        )
    }

    fn matches_tuple(
        i_s: &mut InferenceState<'db, '_>,
        mut matcher: Option<&mut TypeVarMatcher<'db, '_>>,
        t1: &TupleContent,
        t2: &TupleContent,
        variance: Variance,
    ) -> Match {
        if let Some(generics1) = &t1.generics {
            if let Some(generics2) = &t2.generics {
                return match (t1.arbitrary_length, t2.arbitrary_length, variance) {
                    (false, false, _) | (true, true, _) => {
                        if generics1.len() != generics2.len() {
                            Match::new_false()
                        } else {
                            Generics::new_list(generics1).matches(
                                i_s,
                                matcher,
                                Generics::new_list(generics2),
                                variance,
                                None,
                            )
                        }
                    }
                    (false, true, Variance::Covariant) | (_, _, Variance::Invariant) => {
                        Match::new_false()
                    }
                    (true, false, Variance::Covariant) => {
                        let t1 = Type::new(&generics1[0.into()]);
                        generics2
                            .iter()
                            .all(|g2| {
                                let t2 = Type::new(g2);
                                t1.is_sub_type(i_s, matcher.as_deref_mut(), &t2).bool()
                            })
                            .into()
                    }
                    _ => unreachable!(),
                };
            }
        }
        Match::True
    }

    fn overlaps_tuple(
        i_s: &mut InferenceState<'db, '_>,
        t1: &TupleContent,
        t2: &TupleContent,
    ) -> bool {
        if let Some(generics1) = &t1.generics {
            if let Some(generics2) = &t2.generics {
                return match (t1.arbitrary_length, t2.arbitrary_length) {
                    (false, false) | (true, true) => {
                        generics1.len() == generics2.len()
                            && Generics::new_list(generics1).overlaps(
                                i_s,
                                Generics::new_list(generics2),
                                None,
                            )
                    }
                    (false, true) => {
                        let t2 = Type::new(&generics2[0.into()]);
                        for g in generics1.iter() {
                            let t1 = Type::new(g);
                            if !t1.overlaps(i_s, &t2) {
                                return false;
                            }
                        }
                        true
                    }
                    (true, false) => {
                        let t1 = Type::new(&generics1[0.into()]);
                        for g in generics2.iter() {
                            let t2 = Type::new(g);
                            if !t1.overlaps(i_s, &t2) {
                                return false;
                            }
                        }
                        true
                    }
                };
            }
        }
        true
    }

    pub fn overlaps_class(
        i_s: &mut InferenceState<'db, '_>,
        class1: Class<'db, '_>,
        class2: Class<'db, '_>,
    ) -> bool {
        let check = {
            #[inline]
            |i_s: &mut InferenceState<'db, '_>, t1: &Type<'db, '_>, t2: &Type<'db, '_>| {
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

    pub fn error_if_not_matches<'x>(
        &self,
        i_s: &mut InferenceState<'db, 'x>,
        value: &Inferred<'db>,
        mut callback: impl FnMut(&mut InferenceState<'db, 'x>, Box<str>, Box<str>),
    ) {
        self.error_if_not_matches_with_matcher(
            i_s,
            None,
            value,
            Some(
                |i_s: &mut InferenceState<'db, 'x>, t1, t2, reason: &MismatchReason| {
                    callback(i_s, t1, t2)
                },
            ),
        );
    }

    pub fn error_if_not_matches_with_matcher<'x>(
        &self,
        i_s: &mut InferenceState<'db, 'x>,
        mut matcher: Option<&mut TypeVarMatcher<'db, '_>>,
        value: &Inferred<'db>,
        callback: Option<
            impl FnMut(&mut InferenceState<'db, 'x>, Box<str>, Box<str>, &MismatchReason),
        >,
    ) -> Match {
        let value_type = value.class_as_type(i_s);
        let matches = self.is_sub_type(i_s, matcher.as_deref_mut(), &value_type);
        if let Match::False(ref reason) | Match::FalseButSimilar(ref reason) = matches {
            let value_type = value.class_as_type(i_s);
            debug!(
                "Mismatch between {value_type:?} and {self:?} -> {:?}",
                matches.clone()
            );
            let input = value_type.format(i_s, None, FormatStyle::Short);
            let wanted = self.format(i_s, matcher.as_deref(), FormatStyle::Short);
            if let Some(mut callback) = callback {
                callback(i_s, input, wanted, reason)
            }
        }
        matches
    }

    pub fn execute_and_resolve_type_vars(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        class: Option<&Class<'db, '_>>,
        calculated_type_args: &CalculatedTypeArguments,
    ) -> Inferred<'db> {
        let db_type = self.internal_resolve_type_vars(i_s, class, calculated_type_args);
        debug!(
            "Resolved type vars: {}",
            db_type.format(i_s, None, FormatStyle::Short)
        );
        Inferred::execute_db_type(i_s, db_type)
    }

    fn internal_resolve_type_vars(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        class: Option<&Class<'db, '_>>,
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
        db: &'db Database,
        callable: &mut impl FnMut(&Class<'db, '_>) -> bool,
    ) -> bool {
        if let Some(class) = self.maybe_class(db) {
            callable(&class)
        } else if let Some(DbType::Union(union_type)) = self.maybe_db_type() {
            union_type
                .iter()
                .any(|t| Type::new(t).on_any_class(db, callable))
        } else {
            false
        }
    }

    pub fn common_base_class(&self, i_s: &mut InferenceState<'db, '_>, other: &Self) -> DbType {
        match (self.maybe_class(i_s.db), other.maybe_class(i_s.db)) {
            (Some(c1), Some(c2)) => {
                for (_, c1) in c1.mro(i_s) {
                    for (_, c2) in c2.mro(i_s) {
                        if c1.is_same_type(i_s, None, &c2).bool() {
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

    pub fn lookup_symbol(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        name: &str,
    ) -> LookupResult<'db> {
        match self {
            Self::Class(c) => c.lookup_symbol(i_s, name),
            _ => todo!("{name:?} {self:?}"),
        }
    }
    pub fn format(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        matcher: Option<&TypeVarMatcher<'db, '_>>,
        style: FormatStyle,
    ) -> Box<str> {
        match self {
            Self::Class(c) => c.format(i_s, matcher, style),
            Self::Type(t) => t.format(i_s, matcher, style),
        }
    }
}
