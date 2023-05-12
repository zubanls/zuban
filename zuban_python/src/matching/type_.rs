use std::borrow::Cow;
use std::rc::Rc;

use super::params::has_overlapping_params;
use super::{
    calculate_callable_type_vars_and_return, matches_params, CalculatedTypeArguments, FormatData,
    Generics, Match, Matcher, MismatchReason, ResultContext,
};
use crate::arguments::Arguments;
use crate::database::{
    CallableContent, CallableParams, ClassType, Database, DbType, MetaclassState, TupleContent,
    TupleTypeArguments, TypeOrTypeVarTuple, UnionType, Variance,
};
use crate::debug;
use crate::diagnostics::IssueType;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::node_ref::NodeRef;
use crate::value::{
    Callable, Class, Instance, IteratorContent, LookupResult, Module, MroIterator, NamedTupleValue,
    NoneInstance, OnLookupError, OnTypeError, Tuple, TypeVarInstance, TypingType,
};

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

    pub fn union(self, db: &Database, other: Self) -> Self {
        Self::owned(self.into_db_type(db).union(other.into_db_type(db)))
    }

    fn into_cow(self, db: &Database) -> Cow<'a, DbType> {
        match self {
            Self::Class(class) => Cow::Owned(class.as_db_type(db)),
            Self::Type(t) => t,
        }
    }

    pub fn into_db_type(self, db: &Database) -> DbType {
        self.into_cow(db).into_owned()
    }

    pub fn as_cow(&self, db: &Database) -> Cow<DbType> {
        match self {
            Self::Class(class) => Cow::Owned(class.as_db_type(db)),
            Self::Type(t) => Cow::Borrowed(t),
        }
    }

    pub fn as_db_type(&self, db: &Database) -> DbType {
        self.as_cow(db).into_owned()
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

    #[inline]
    pub fn maybe_borrowed_class(&self, db: &'a Database) -> Option<Class<'a>> {
        match self {
            Self::Class(c) => Some(*c),
            Self::Type(Cow::Borrowed(t)) => match t {
                DbType::Class(link, generics) => Some(Class::from_db_type(db, *link, generics)),
                _ => None,
            },
            Self::Type(Cow::Owned(_)) => unreachable!(),
        }
    }

    pub fn maybe_callable(&self, i_s: &InferenceState) -> Option<Cow<'a, CallableContent>> {
        match self {
            Self::Type(Cow::Borrowed(DbType::Callable(c))) => Some(Cow::Borrowed(c)),
            _ => match self.maybe_db_type() {
                Some(DbType::Callable(c)) => Some(Cow::Owned(c.as_ref().clone())),
                Some(DbType::Type(t)) => match t.as_ref() {
                    DbType::Class(link, generics) => {
                        todo!()
                    }
                    _ => None,
                },
                _ => self.maybe_class(i_s.db).and_then(|c| {
                    Instance::new(c, None)
                        .lookup(i_s, None, "__call__")
                        .into_maybe_inferred()
                        .and_then(|i| {
                            i.maybe_callable(i_s, true)
                                .map(|c| Cow::Owned(c.into_owned()))
                        })
                }),
            },
        }
    }

    #[inline]
    pub fn expect_borrowed_class(&self, db: &'a Database) -> Class<'a> {
        match self {
            Self::Class(c) => *c,
            Self::Type(Cow::Borrowed(DbType::Class(link, generics))) => {
                Class::from_db_type(db, *link, generics)
            }
            _ => unreachable!(),
        }
    }

    pub fn maybe_db_type(&self) -> Option<&DbType> {
        match self {
            Self::Class(_) => None,
            Self::Type(t) => Some(t.as_ref()),
        }
    }

    pub fn maybe_borrowed_db_type(&self) -> Option<&'a DbType> {
        match self {
            Self::Type(Cow::Borrowed(t)) => Some(t),
            _ => None,
        }
    }

    pub fn overlaps(&self, i_s: &InferenceState, other: &Self) -> bool {
        match other.maybe_db_type() {
            Some(DbType::TypeVar(t2_usage)) => {
                return if let Some(bound) = &t2_usage.type_var.bound {
                    self.overlaps(i_s, &Type::new(bound))
                } else if !t2_usage.type_var.restrictions.is_empty() {
                    t2_usage
                        .type_var
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
                DbType::Literal(literal1) => match other.maybe_db_type() {
                    Some(DbType::Literal(literal2)) => {
                        literal1.value(i_s.db) == literal2.value(i_s.db)
                    }
                    _ => Type::Class(i_s.db.python_state.literal_class(literal1.kind))
                        .overlaps(i_s, other),
                },
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
                DbType::Union(union) => union.iter().any(|t| Type::new(t).overlaps(i_s, other)),
                DbType::FunctionOverload(intersection) => todo!(),
                DbType::NewType(_) => todo!(),
                DbType::RecursiveAlias(_) => todo!(),
                DbType::Self_ => false, // TODO this is wrong
                DbType::ParamSpecArgs(usage) => todo!(),
                DbType::ParamSpecKwargs(usage) => todo!(),
                DbType::Module(file_index) => todo!(),
                DbType::NamedTuple(_) => todo!(),
            },
        }
    }

    fn matches_internal(
        &self,
        i_s: &InferenceState,
        matcher: &mut Matcher,
        value_type: &Self,
        variance: Variance,
    ) -> Match {
        let result = match self {
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
                    Some(DbType::Type(t2)) => Type::new(t1)
                        .matches(i_s, matcher, &Type::new(t2), variance)
                        .similar_if_false(),
                    _ => Match::new_false(),
                },
                DbType::TypeVar(t1) => {
                    if matcher.is_matching_reverse() {
                        Match::new_false()
                    } else {
                        matcher.match_or_add_type_var(i_s, t1, value_type, variance)
                    }
                }
                DbType::Callable(c1) => match value_type.maybe_db_type() {
                    Some(DbType::Type(t2)) => match t2.as_ref() {
                        DbType::Class(link, generics) => {
                            let cls = Class::from_db_type(i_s.db, *link, generics);
                            // TODO the __init__ should actually be looked up on the original class, not
                            // the subclass
                            let lookup = cls.lookup(i_s, None, "__init__");
                            if let LookupResult::GotoName(_, init) = lookup {
                                let t2 = init.as_type(i_s).into_db_type(i_s.db);
                                if let DbType::Callable(c2) = t2 {
                                    let type_vars2 = cls.type_vars(i_s);
                                    // Since __init__ does not have a return, We need to check the params
                                    // of the __init__ functions and the class as a return type separately.
                                    return Type::new(&c1.result_type).is_super_type_of(
                                        i_s,
                                        matcher,
                                        &Type::Class(cls),
                                    ) & matches_params(
                                        i_s,
                                        matcher,
                                        &c1.params,
                                        &c2.params,
                                        type_vars2.map(|t| (t, cls.node_ref.as_link())),
                                        Variance::Contravariant,
                                        true, // Ignore the first param
                                    );
                                }
                            }
                            Match::new_false()
                        }
                        _ => {
                            if matches!(&c1.params, CallableParams::Any) {
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
                    Some(DbType::Callable(c2)) => Self::matches_callable(i_s, matcher, c1, c2),
                    Some(DbType::FunctionOverload(overload)) if variance == Variance::Covariant => {
                        if matcher.is_matching_reverse() {
                            todo!()
                        }
                        overload
                            .iter()
                            .any(|c2| Self::matches_callable(i_s, matcher, c1, c2).bool())
                            .into()
                    }
                    _ => Match::new_false(),
                },
                DbType::None => {
                    matches!(value_type, Self::Type(ref t2) if matches!(t2.as_ref(), DbType::None))
                        .into()
                }
                DbType::Any if matcher.is_matching_reverse() => {
                    debug!("TODO write a test for this.");
                    let t1 = self.as_cow(i_s.db);
                    matcher.set_all_contained_type_vars_to_any(i_s, &t1);
                    Match::True { with_any: true }
                }
                DbType::Any => Match::new_true(),
                DbType::Never => Match::new_false(),
                DbType::Tuple(t1) => match value_type.maybe_db_type() {
                    Some(DbType::Tuple(t2)) => {
                        Self::matches_tuple(i_s, matcher, t1, t2, variance).similar_if_false()
                    }
                    Some(DbType::NamedTuple(t2)) => {
                        Self::matches_tuple(i_s, matcher, t1, t2.as_tuple(), variance)
                            .similar_if_false()
                    }
                    _ => Match::new_false(),
                },
                DbType::Union(union_type1) => {
                    self.matches_union(i_s, matcher, union_type1, value_type, variance)
                }
                DbType::FunctionOverload(intersection) => todo!(),
                DbType::Literal(literal1) => {
                    debug_assert!(!literal1.implicit);
                    match value_type.maybe_db_type() {
                        Some(DbType::Literal(literal2)) => {
                            (literal1.value(i_s.db) == literal2.value(i_s.db)).into()
                        }
                        _ => Match::new_false(),
                    }
                }
                DbType::NewType(new_type1) => match value_type.maybe_db_type() {
                    Some(DbType::NewType(new_type2)) => (new_type1 == new_type2).into(),
                    _ => Match::new_false(),
                },
                DbType::RecursiveAlias(rec1) => {
                    if let Some(class) = value_type.maybe_class(i_s.db) {
                        let cls_db_type = value_type.as_db_type(i_s.db);
                        // Classes like aliases can also be recursive in mypy, like `class B(List[B])`.
                        matcher.avoid_recursion(rec1, cls_db_type, |matcher| {
                            let g = rec1.calculated_db_type(i_s.db);
                            Type::new(g).matches_internal(i_s, matcher, value_type, variance)
                        })
                    } else {
                        match value_type.maybe_db_type() {
                            Some(t @ DbType::RecursiveAlias(rec2)) => {
                                matcher.avoid_recursion(rec1, t.clone(), |matcher| {
                                    let t1 = rec1.calculated_db_type(i_s.db);
                                    let t2 = rec2.calculated_db_type(i_s.db);
                                    Type::new(t1).matches_internal(
                                        i_s,
                                        matcher,
                                        &Type::new(t2),
                                        variance,
                                    )
                                })
                            }
                            _ => {
                                let g = rec1.calculated_db_type(i_s.db);
                                Type::new(g).matches_internal(i_s, matcher, value_type, variance)
                            }
                        }
                    }
                }
                DbType::Self_ => match value_type.maybe_db_type() {
                    Some(DbType::Self_) => Match::new_true(),
                    _ => Match::new_false(),
                },
                DbType::ParamSpecArgs(usage1) => match value_type.maybe_db_type() {
                    Some(DbType::ParamSpecArgs(usage2)) => (usage1 == usage2).into(),
                    _ => Match::new_false(),
                },
                DbType::ParamSpecKwargs(usage1) => match value_type.maybe_db_type() {
                    Some(DbType::ParamSpecKwargs(usage2)) => (usage1 == usage2).into(),
                    _ => Match::new_false(),
                },
                DbType::NamedTuple(nt1) => match value_type.maybe_db_type() {
                    Some(DbType::NamedTuple(nt2)) => {
                        let c1 = &nt1.constructor;
                        let c2 = &nt2.constructor;
                        if c1.type_vars.is_some() || c2.type_vars.is_some() {
                            todo!()
                        } else {
                            (c1.defined_at == c2.defined_at).into()
                        }
                    }
                    _ => Match::new_false(),
                },
                DbType::Module(file_index) => Match::new_false(),
            },
        };
        result
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
        let m = match value_type.mro(i_s.db) {
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
        let result = m
            .or(|| {
                self.check_protocol_and_other_side(i_s, matcher, value_type, Variance::Covariant)
            })
            .or(|| {
                if let Some(class2) = value_type.maybe_class(i_s.db) {
                    if !matcher.ignore_promotions() {
                        return self.check_promotion(i_s, matcher, class2);
                    }
                }
                Match::new_false()
            });
        debug!(
            "Match covariant {} against {} -> {:?}",
            self.format_short(i_s.db),
            value_type.format_short(i_s.db),
            result
        );
        result
    }

    #[inline]
    pub fn check_promotion(
        &self,
        i_s: &InferenceState,
        matcher: &mut Matcher,
        class2: Class,
    ) -> Match {
        if let Some(promote_to) = class2.class_storage.promote_to.get() {
            let cls =
                Class::from_position(NodeRef::from_link(i_s.db, promote_to), Generics::None, None);
            self.is_same_type(i_s, matcher, &Type::Class(cls))
                .or(|| self.check_promotion(i_s, matcher, cls))
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
        debug!(
            "Match invariant {} against {} -> {:?}",
            self.format_short(i_s.db),
            value_type.format_short(i_s.db),
            result
        );
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
        // 2. Check if it is a class with a protocol
        if let Some(class1) = self.maybe_class(i_s.db) {
            // TODO this should probably be checked before normal mro checking?!
            if class1.use_cached_class_infos(i_s.db).class_type == ClassType::Protocol {
                if let Some(class2) = value_type.maybe_class(i_s.db) {
                    return class1.check_protocol_match(i_s, class2).into();
                }
            }
        }
        // 3. Check if the value_type is special like Any or a Typevar and needs to be checked
        //    again.
        if let Type::Type(t2) = value_type {
            match t2.as_ref() {
                DbType::Any if matcher.is_matching_reverse() => return Match::new_true(),
                DbType::Any => {
                    let t1 = self.as_cow(i_s.db);
                    matcher.set_all_contained_type_vars_to_any(i_s, &t1);
                    return Match::True { with_any: true };
                }
                DbType::None if !i_s.db.python_state.project.strict_optional => {
                    return Match::new_true()
                }
                DbType::TypeVar(t2) => {
                    if matcher.is_matching_reverse() {
                        return matcher.match_or_add_type_var(i_s, t2, self, variance.invert());
                    }
                    if variance == Variance::Covariant {
                        if let Some(bound) = &t2.type_var.bound {
                            let m = self.simple_matches(i_s, &Type::new(bound), variance);
                            if m.bool() {
                                return m;
                            }
                        } else if !t2.type_var.restrictions.is_empty() {
                            let m =
                                t2.type_var.restrictions.iter().all(|r| {
                                    self.simple_matches(i_s, &Type::new(r), variance).bool()
                                });
                            if m {
                                return Match::new_true();
                            }
                        }
                    }
                }
                // Necessary to e.g. match int to Literal[1, 2]
                DbType::Union(u2)
                    if variance == Variance::Covariant
                    // Union matching was already done.
                    && !self.is_union() =>
                {
                    if matcher.is_matching_reverse() {
                        debug!("TODO matching reverse?");
                    }
                    let mut result: Option<Match> = None;
                    for t in u2.iter() {
                        let r = self.matches(i_s, matcher, &Type::new(t), variance);
                        if !r.bool() {
                            return r.bool().into();
                        } else {
                            if let Some(old) = result {
                                result = Some(old & r)
                            } else {
                                result = Some(r)
                            }
                        }
                    }
                    return result.unwrap();
                }
                DbType::NewType(n2) => {
                    let t = n2.type_(i_s);
                    return self.matches(i_s, matcher, &Type::new(t), variance);
                }
                DbType::Never if variance == Variance::Covariant => return Match::new_true(), // Never is assignable to anything
                DbType::Self_ if variance == Variance::Covariant => {
                    return self.simple_matches(
                        i_s,
                        &Type::Class(*i_s.current_class().unwrap()),
                        variance,
                    )
                }
                DbType::Module(_) => {
                    return self.matches(
                        i_s,
                        matcher,
                        &Type::Class(i_s.db.python_state.module_type()),
                        variance,
                    )
                }
                _ => (),
            }
        }
        Match::new_false()
    }

    pub fn mro<'db: 'x, 'x>(&'x self, db: &'db Database) -> Option<MroIterator<'db, '_>> {
        match self {
            Self::Class(c) => Some(c.mro(db)),
            Self::Type(t) => match t.as_ref() {
                DbType::Class(link, generics) => {
                    Some(Class::from_db_type(db, *link, generics).mro(db))
                }
                DbType::Tuple(tup) => Some({
                    let tuple_class = db.python_state.tuple_class(db, tup);
                    MroIterator::new(
                        db,
                        Type::new(t),
                        tuple_class.generics,
                        tuple_class.use_cached_class_infos(db).mro.iter(),
                        false,
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
                    Match::True { with_any: true }
                } else {
                    m
                }
            })
            .unwrap_or_else(Match::new_false)
    }

    fn matches_union(
        &self,
        i_s: &InferenceState,
        matcher: &mut Matcher,
        u1: &UnionType,
        value_type: &Self,
        variance: Variance,
    ) -> Match {
        let match_reverse = matcher.is_matching_reverse();
        match value_type.maybe_db_type() {
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
            _ => match variance {
                Variance::Covariant => u1
                    .iter()
                    .any(|g| {
                        Type::new(g)
                            .matches(i_s, matcher, value_type, variance)
                            .bool()
                    })
                    .into(),
                Variance::Invariant => u1
                    .iter()
                    .all(|g| {
                        Type::new(g)
                            .matches(i_s, matcher, value_type, variance)
                            .bool()
                    })
                    .into(),
                Variance::Contravariant => unreachable!(),
            },
        }
    }

    fn matches_class(
        i_s: &InferenceState,
        matcher: &mut Matcher,
        class1: &Class,
        value_type: &Type,
        variance: Variance,
    ) -> Match {
        if let Some(class2) = value_type.maybe_class(i_s.db) {
            if class1.node_ref == class2.node_ref {
                if let Some(type_vars) = class1.type_vars(i_s) {
                    let c1_generics = class1.generics();
                    let c2_generics = class2.generics();
                    let result = c1_generics
                        .matches(i_s, matcher, c2_generics, type_vars)
                        .similar_if_false();
                    if !result.bool() {
                        let mut check = |i_s: &InferenceState, n| {
                            let type_var_like = &type_vars[n];
                            let t1 = c1_generics.nth_type_argument(i_s.db, type_var_like, n);
                            if t1.is_any() {
                                return false;
                            }
                            let t2 = c2_generics.nth_type_argument(i_s.db, type_var_like, n);
                            if t2.is_any() {
                                return false;
                            }
                            t1.is_super_type_of(i_s, matcher, &t2).bool()
                        };
                        if class1.node_ref == i_s.db.python_state.list_node_ref() && check(i_s, 0) {
                            return Match::False {
                                similar: true,
                                reason: MismatchReason::SequenceInsteadOfListNeeded,
                            };
                        } else if class1.node_ref == i_s.db.python_state.dict_node_ref()
                            && check(i_s, 1)
                        {
                            return Match::False {
                                similar: true,
                                reason: MismatchReason::MappingInsteadOfDictNeeded,
                            };
                        }
                    }
                    return result;
                }
                return Match::new_true();
            }
        } else if let Some(DbType::Type(t2)) = value_type.maybe_db_type() {
            if let DbType::Class(c2, generics2) = t2.as_ref() {
                let class2 = Class::from_db_type(i_s.db, *c2, generics2);
                match class2.use_cached_class_infos(i_s.db).metaclass {
                    MetaclassState::Some(link) => {
                        let meta = Class::from_db_type(i_s.db, link, &None);
                        return Type::Class(*class1).matches(
                            i_s,
                            matcher,
                            &Type::Class(meta),
                            variance,
                        );
                    }
                    MetaclassState::Unknown => {
                        todo!()
                    }
                    MetaclassState::None => (),
                }
            }
        } else if variance == Variance::Covariant {
            if let Some(DbType::Literal(literal)) = value_type.maybe_db_type() {
                return Self::matches_class(
                    i_s,
                    matcher,
                    class1,
                    &Type::Class(i_s.db.python_state.literal_class(literal.kind)),
                    variance,
                );
            }
        }
        Match::new_false()
    }

    fn matches_callable(
        i_s: &InferenceState,
        matcher: &mut Matcher,
        c1: &CallableContent,
        c2: &CallableContent,
    ) -> Match {
        // TODO This if is weird.
        if !matcher.has_type_var_matcher() {
            if let Some(c2_type_vars) = c2.type_vars.as_ref() {
                let mut matcher = Matcher::new_reverse_callable_matcher(c2, c2_type_vars.len());
                return Type::matches_callable(i_s, &mut matcher, c1, c2);
            }
        }
        Type::new(&c1.result_type).is_super_type_of(i_s, matcher, &Type::new(&c2.result_type))
            & matches_params(
                i_s,
                matcher,
                &c1.params,
                &c2.params,
                c2.type_vars.as_ref().map(|t| (t, c2.defined_at)),
                Variance::Contravariant,
                false,
            )
    }

    fn matches_tuple(
        i_s: &InferenceState,
        matcher: &mut Matcher,
        t1: &TupleContent,
        t2: &TupleContent,
        variance: Variance,
    ) -> Match {
        if let Some(t1_args) = &t1.args {
            if let Some(t2_args) = &t2.args {
                return match_tuple_type_arguments(i_s, matcher, t1_args, t2_args, variance);
            } else {
                // TODO maybe set generics to any?
            }
        }
        Match::new_true()
    }

    fn overlaps_tuple(i_s: &InferenceState, t1: &TupleContent, t2: &TupleContent) -> bool {
        use TupleTypeArguments::*;
        match (&t1.args, &t2.args) {
            (Some(FixedLength(ts1)), Some(FixedLength(ts2))) => {
                let mut value_generics = ts2.iter();
                let mut overlaps = true;
                for type1 in ts1.iter() {
                    /*
                    if matcher.might_have_defined_type_vars() {
                        match type1 {
                            DbType::TypeVarLike(t) if t.is_type_var_tuple() => {
                                todo!()
                            }
                            _ => (),
                        }
                    }
                    */
                    if let Some(type2) = value_generics.next() {
                        match (type1, type2) {
                            (TypeOrTypeVarTuple::Type(t1), TypeOrTypeVarTuple::Type(t2)) => {
                                overlaps &= Type::new(t1).overlaps(i_s, &Type::new(t2));
                            }
                            _ => todo!(),
                        }
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
                ts2.iter().all(|t2| match t2 {
                    TypeOrTypeVarTuple::Type(t2) => t1.overlaps(i_s, &Type::new(t2)),
                    TypeOrTypeVarTuple::TypeVarTuple(t2) => {
                        todo!()
                    }
                })
            }
            (Some(FixedLength(ts1)), Some(ArbitraryLength(t2))) => {
                let t2 = Type::new(t2.as_ref());
                ts1.iter().all(|t1| match t1 {
                    TypeOrTypeVarTuple::Type(t1) => Type::new(t1).overlaps(i_s, &t2),
                    TypeOrTypeVarTuple::TypeVarTuple(t1) => {
                        todo!()
                    }
                })
            }
            _ => true,
        }
    }

    pub fn overlaps_class(i_s: &InferenceState, class1: Class, class2: Class) -> bool {
        let check = {
            #[inline]
            |i_s: &InferenceState, t1: &Type, t2: &Type| {
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

        for (_, c1) in class1.mro(i_s.db) {
            if check(i_s, &c1, &Type::Class(class2)) {
                return true;
            }
        }
        for (_, c2) in class2.mro(i_s.db) {
            if check(i_s, &Type::Class(class1), &c2) {
                return true;
            }
        }
        false
    }

    pub fn error_if_not_matches<'db>(
        &self,
        i_s: &InferenceState<'db, '_>,
        value: &Inferred,
        callback: impl FnOnce(&InferenceState<'db, '_>, Box<str>, Box<str>) -> NodeRef<'db>,
    ) -> Match {
        self.error_if_not_matches_with_matcher(
            i_s,
            &mut Matcher::default(),
            value,
            Some(
                |i_s: &InferenceState<'db, '_>, t1, t2, reason: &MismatchReason| {
                    callback(i_s, t1, t2)
                },
            ),
        )
    }

    pub fn error_if_not_matches_with_matcher<'db>(
        &self,
        i_s: &InferenceState<'db, '_>,
        matcher: &mut Matcher,
        value: &Inferred,
        callback: Option<
            impl FnOnce(&InferenceState<'db, '_>, Box<str>, Box<str>, &MismatchReason) -> NodeRef<'db>,
        >,
    ) -> Match {
        let value_type = value.as_type(i_s);
        let matches = self.is_super_type_of(i_s, matcher, &value_type);
        if let Match::False { ref reason, .. } = matches {
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
                let node_ref = callback(i_s, input, wanted, reason);
                match reason {
                    MismatchReason::SequenceInsteadOfListNeeded => {
                        node_ref.add_typing_issue(
                            i_s,
                            IssueType::InvariantNote {
                                actual: "List",
                                maybe: "Sequence",
                            },
                        );
                    }
                    MismatchReason::MappingInsteadOfDictNeeded => {
                        node_ref.add_typing_issue(
                            i_s,
                            IssueType::InvariantNote {
                                actual: "Dict",
                                maybe: "Mapping",
                            },
                        );
                    }
                    _ => (),
                }
            }
        }
        matches
    }

    pub fn try_to_resemble_context(
        self,
        i_s: &InferenceState,
        matcher: &mut Matcher,
        t: &Self,
    ) -> DbType {
        if let Some(class) = t.maybe_class(i_s.db) {
            if let Some(mro) = self.mro(i_s.db) {
                for (_, value_type) in mro {
                    if Self::matches_class(
                        i_s,
                        &mut Matcher::default(),
                        &class,
                        &value_type,
                        Variance::Covariant,
                    )
                    .bool()
                    {
                        return value_type.into_db_type(i_s.db);
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
                                return DbType::Tuple(Rc::new(TupleContent::new_fixed_length(
                                    ts1.iter()
                                        .zip(ts2.iter())
                                        .map(|(g1, g2)| match (g1, g2) {
                                            (
                                                TypeOrTypeVarTuple::Type(g1),
                                                TypeOrTypeVarTuple::Type(g2),
                                            ) => TypeOrTypeVarTuple::Type(
                                                Type::new(g2).try_to_resemble_context(
                                                    i_s,
                                                    matcher,
                                                    &Type::new(g1),
                                                ),
                                            ),
                                            _ => todo!(),
                                        })
                                        .collect(),
                                )))
                            }
                            (Some(ArbitraryLength(t1)), Some(ArbitraryLength(t2))) => {
                                return DbType::Tuple(Rc::new(TupleContent::new_arbitrary_length(
                                    Type::new(t1.as_ref()).try_to_resemble_context(
                                        i_s,
                                        matcher,
                                        &Type::new(t2.as_ref()),
                                    ),
                                )))
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
                DbType::TypeVar(_) => {
                    if matcher.might_have_defined_type_vars() {
                        let t = Type::owned(
                            matcher.replace_type_var_likes_for_nested_context(i_s.db, db_type),
                        );
                        return self.try_to_resemble_context(i_s, &mut Matcher::default(), &t);
                    }
                }
                DbType::Type(t1) => todo!(),
                _ => (),
            }
        }
        self.into_db_type(i_s.db)
    }

    pub fn execute_and_resolve_type_vars(
        &self,
        i_s: &InferenceState,
        class: Option<&Class>,
        self_class: Option<&Class>,
        calculated_type_args: &CalculatedTypeArguments,
    ) -> Inferred {
        let db_type = self.internal_resolve_type_vars(i_s, class, self_class, calculated_type_args);
        debug!(
            "Resolved type vars: {}",
            Type::new(&db_type).format_short(i_s.db)
        );
        Inferred::execute_db_type(i_s, db_type)
    }

    fn internal_resolve_type_vars(
        &self,
        i_s: &InferenceState,
        class: Option<&Class>,
        self_class: Option<&Class>,
        calculated_type_args: &CalculatedTypeArguments,
    ) -> DbType {
        let mut replace_self = || {
            self_class
                .map(|c| c.as_db_type(i_s.db))
                .unwrap_or(DbType::Self_)
        };
        self.as_cow(i_s.db).replace_type_var_likes_and_self(
            i_s.db,
            &mut |t| calculated_type_args.lookup_type_var_usage(i_s, class, t),
            &mut replace_self,
        )
    }

    pub fn execute<'db>(
        &self,
        i_s: &InferenceState<'db, '_>,
        inferred_from: Option<&Inferred>,
        args: &dyn Arguments<'db>,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError<'db, '_>,
    ) -> Inferred {
        if let Some(cls) = self.maybe_class(i_s.db) {
            return Instance::new(cls, inferred_from).execute(
                i_s,
                args,
                result_context,
                on_type_error,
            );
        }
        match self.maybe_db_type().unwrap() {
            DbType::Type(cls) => {
                execute_type_of_type(i_s, args, result_context, on_type_error, cls.as_ref())
            }
            DbType::Union(union) => Inferred::gather_union(i_s, |gather| {
                for entry in union.iter() {
                    gather(Type::new(entry).execute(i_s, None, args, result_context, on_type_error))
                }
            }),
            t @ DbType::Callable(content) => Callable::new(t, content).execute_internal(
                i_s,
                args,
                on_type_error,
                None,
                result_context,
            ),
            DbType::Any | DbType::Never => {
                args.iter().calculate_diagnostics(i_s);
                Inferred::new_unknown()
            }
            _ => {
                let t = self.format_short(i_s.db);
                args.as_node_ref().add_typing_issue(
                    i_s,
                    IssueType::NotCallable {
                        type_: format!("\"{}\"", t).into(),
                    },
                );
                Inferred::new_unknown()
            }
        }
    }

    pub fn iter_on_borrowed<'slf>(
        &self,
        i_s: &InferenceState<'a, '_>,
        from: NodeRef,
    ) -> IteratorContent<'a> {
        if let Some(cls) = self.maybe_borrowed_class(i_s.db) {
            return Instance::new(cls, None).iter(i_s, from);
        }
        match self.maybe_borrowed_db_type().unwrap() {
            t @ DbType::Tuple(content) => Tuple::new(t, content).iter(i_s, from),
            DbType::NamedTuple(nt) => NamedTupleValue::new(i_s.db, nt).iter(i_s, from),
            DbType::Any | DbType::Never => IteratorContent::Any,
            _ => {
                let t = self.format_short(i_s.db);
                from.add_typing_issue(
                    i_s,
                    IssueType::NotIterable {
                        type_: format!("\"{}\"", t).into(),
                    },
                );
                IteratorContent::Any
            }
        }
    }

    pub fn on_any_class(
        &self,
        i_s: &InferenceState,
        matcher: &mut Matcher,
        callable: &mut impl FnMut(&InferenceState, &mut Matcher, &Class) -> bool,
    ) -> bool {
        if let Some(class) = self.maybe_class(i_s.db) {
            callable(i_s, matcher, &class)
        } else {
            match self.maybe_db_type() {
                Some(DbType::Union(union_type)) => union_type
                    .iter()
                    .any(|t| Type::new(t).on_any_class(i_s, matcher, callable)),
                Some(db_type @ DbType::TypeVar(_)) => {
                    if matcher.might_have_defined_type_vars() {
                        Type::owned(
                            matcher.replace_type_var_likes_for_nested_context(i_s.db, db_type),
                        )
                        .on_any_class(i_s, matcher, callable)
                    } else {
                        false
                    }
                }
                _ => false,
            }
        }
    }

    pub fn common_base_type(&self, i_s: &InferenceState, other: &Self) -> DbType {
        match (self.maybe_class(i_s.db), other.maybe_class(i_s.db)) {
            (Some(c1), Some(c2)) => {
                for (_, c1) in c1.mro(i_s.db) {
                    for (_, c2) in c2.mro(i_s.db) {
                        if c1.is_simple_same_type(i_s, &c2).bool() {
                            return c1.as_db_type(i_s.db);
                        }
                    }
                }
                unreachable!("object is always a common base class")
            }
            (None, None) => {
                // TODO this should also be done for function/callable and callable/function and
                // not only callable/callable
                if let Some(DbType::Callable(c1)) = self.maybe_db_type() {
                    if let Some(DbType::Callable(c2)) = other.maybe_db_type() {
                        return DbType::Class(i_s.db.python_state.function_point_link(), None);
                    }
                }
            }
            _ => (),
        }
        i_s.db.python_state.object_db_type()
    }

    pub fn check_duplicate_base_class(&self, db: &Database, other: &Self) -> Option<Box<str>> {
        if let (Some(c1), Some(c2)) = (self.maybe_class(db), other.maybe_class(db)) {
            (c1.node_ref == c2.node_ref).then(|| Box::from(c1.name()))
        } else {
            match (self.maybe_db_type(), other.maybe_db_type()) {
                (Some(DbType::Type(_)), Some(DbType::Type(_))) => Some(Box::from("type")),
                (Some(DbType::Tuple(_)), Some(DbType::Tuple(_))) => Some(Box::from("tuple")),
                (Some(DbType::Callable(_)), Some(DbType::Callable(_))) => {
                    Some(Box::from("callable"))
                }
                _ => None,
            }
        }
    }

    pub fn is_union(&self) -> bool {
        matches!(self.maybe_db_type(), Some(DbType::Union(_)))
    }

    pub fn is_any(&self) -> bool {
        matches!(self, Type::Type(t) if matches!(t.as_ref(), DbType::Any))
    }

    pub fn has_any(&self, i_s: &InferenceState) -> bool {
        match self {
            // TODO this does not not need to generate a db type
            Self::Class(c) => c.as_db_type(i_s.db).has_any(i_s),
            Self::Type(t) => t.has_any(i_s),
        }
    }

    pub fn has_explicit_self_type(&self, db: &Database) -> bool {
        match self {
            // TODO this does not not need to generate a db type
            Self::Class(c) => c.as_db_type(db).has_self_type(),
            Self::Type(t) => t.has_self_type(),
        }
    }

    #[inline]
    pub fn run_after_lookup_on_each_union_member<'db>(
        &self,
        i_s: &InferenceState<'db, '_>,
        from_inferred: Option<&Inferred>,
        from: Option<NodeRef>,
        name: &str,
        callable: &mut impl FnMut(LookupResult),
    ) {
        if let Some(cls) = self.maybe_class(i_s.db) {
            return callable(Instance::new(cls, from_inferred).lookup(i_s, from, name));
        }
        match self.maybe_db_type().unwrap() {
            DbType::Any => callable(LookupResult::any()),
            DbType::None => callable(NoneInstance().lookup(i_s, from, name)),
            DbType::Literal(literal) => {
                let v = Instance::new(i_s.db.python_state.literal_class(literal.kind), None);
                callable(v.lookup(i_s, from, name))
            }
            t @ DbType::TypeVar(tv) => {
                callable(TypeVarInstance::new(i_s.db, t, tv).lookup(i_s, from, name))
            }
            t @ DbType::Tuple(tup) => callable(Tuple::new(t, tup).lookup(i_s, from, name)),
            DbType::Union(union) => {
                for t in union.iter() {
                    Type::new(t)
                        .run_after_lookup_on_each_union_member(i_s, None, from, name, callable)
                }
            }
            DbType::Type(t) => match t.as_ref() {
                DbType::Union(union) => {
                    debug_assert!(!union.entries.is_empty());
                    for t in union.iter() {
                        callable(TypingType::new(i_s.db, t).lookup(i_s, None, name))
                    }
                }
                DbType::Any => callable(LookupResult::any()),
                _ => callable(TypingType::new(i_s.db, t).lookup(i_s, from, name)),
            },
            t @ DbType::Callable(c) => callable(Callable::new(t, c).lookup(i_s, from, name)),
            DbType::Module(file_index) => {
                let file = i_s.db.loaded_python_file(*file_index);
                callable(Module::new(i_s.db, file).lookup(i_s, from, name))
            }
            DbType::Self_ => {
                let current_class = i_s.current_class().unwrap();
                let type_var_likes = current_class.type_vars(i_s);
                callable(
                    Instance::new(
                        Class::from_position(
                            current_class.node_ref.to_db_lifetime(i_s.db),
                            Generics::Self_ {
                                class_definition: current_class.node_ref.as_link(),
                                type_var_likes: unsafe { std::mem::transmute(type_var_likes) },
                            },
                            None,
                        ),
                        from_inferred,
                    )
                    .lookup(i_s, from, name),
                )
            }
            DbType::NamedTuple(nt) => {
                callable(NamedTupleValue::new(i_s.db, nt).lookup(i_s, from, name))
            }
            DbType::Class(..) => unreachable!(),
            DbType::NewType(new_type) => Type::new(&new_type.type_(i_s))
                .run_after_lookup_on_each_union_member(i_s, None, from, name, callable),
            _ => todo!("{self:?}"),
        }
    }

    pub fn lookup_without_error<'db>(
        &self,
        i_s: &InferenceState<'db, '_>,
        from: Option<NodeRef>,
        name: &str,
    ) -> LookupResult {
        self.lookup_helper(i_s, from, name, &|_, _| ())
    }

    pub fn lookup_with_error<'db>(
        &self,
        i_s: &InferenceState<'db, '_>,
        from: NodeRef,
        name: &str,
        on_lookup_error: OnLookupError<'db, '_>,
    ) -> LookupResult {
        self.lookup_helper(i_s, Some(from), name, on_lookup_error)
    }

    #[inline]
    fn lookup_helper<'db>(
        &self,
        i_s: &InferenceState<'db, '_>,
        from: Option<NodeRef>,
        name: &str,
        on_lookup_error: OnLookupError<'db, '_>,
    ) -> LookupResult {
        let mut result: Option<LookupResult> = None;
        self.run_after_lookup_on_each_union_member(i_s, None, from, name, &mut |lookup_result| {
            if matches!(lookup_result, LookupResult::None) {
                on_lookup_error(i_s, self);
            }
            result = Some(if let Some(l) = result.take() {
                LookupResult::UnknownName(
                    l.into_inferred().union(i_s, lookup_result.into_inferred()),
                )
            } else {
                lookup_result
            })
        });
        result.unwrap_or_else(|| todo!())
    }

    pub fn lookup_symbol(&self, i_s: &InferenceState, name: &str) -> LookupResult {
        match self {
            Self::Class(c) => c.lookup_symbol(i_s, name),
            Self::Type(t) => match t.as_ref() {
                DbType::Class(c, generics) => todo!(),
                DbType::Tuple(t) => LookupResult::None, // TODO this probably omits index/count
                DbType::NamedTuple(nt) => NamedTupleValue::new(i_s.db, nt).lookup(i_s, None, name),
                DbType::Callable(t) => todo!(),
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

    pub fn format_short(&self, db: &Database) -> Box<str> {
        self.format(&FormatData::new_short(db))
    }
}

pub fn match_tuple_type_arguments(
    i_s: &InferenceState,
    matcher: &mut Matcher,
    t1: &TupleTypeArguments,
    t2: &TupleTypeArguments,
    variance: Variance,
) -> Match {
    if matcher.is_matching_reverse() {
        return matcher.match_reverse(|matcher| {
            match_tuple_type_arguments(i_s, matcher, t2, t1, variance.invert())
        });
    }
    use TupleTypeArguments::*;
    if matcher.might_have_defined_type_vars() {
        if let Some(ts) = t1.has_type_var_tuple() {
            return matcher.match_type_var_tuple(i_s, ts, t2, variance);
        }
    }
    match (t1, t2, variance) {
        (tup1_args @ FixedLength(ts1), tup2_args @ FixedLength(ts2), _) => {
            if ts1.len() == ts2.len() {
                let mut matches = Match::new_true();
                for (t1, t2) in ts1.iter().zip(ts2.iter()) {
                    match (t1, t2) {
                        (TypeOrTypeVarTuple::Type(t1), TypeOrTypeVarTuple::Type(t2)) => {
                            matches &=
                                Type::new(t1).matches(i_s, matcher, &Type::new(t2), variance);
                        }
                        (
                            TypeOrTypeVarTuple::TypeVarTuple(t1),
                            TypeOrTypeVarTuple::TypeVarTuple(t2),
                        ) => matches &= (t1 == t2).into(),
                        _ => todo!("{t1:?} {t2:?}"),
                    }
                }
                matches
            } else {
                Match::new_false()
            }
        }
        (ArbitraryLength(t1), ArbitraryLength(t2), _) => {
            Type::new(t1).matches(i_s, matcher, &Type::new(t2), variance)
        }
        (tup1_args @ FixedLength(ts1), tup2_args @ ArbitraryLength(t2), Variance::Covariant) => {
            Match::new_false()
        }
        (ArbitraryLength(t1), FixedLength(ts2), Variance::Invariant) => {
            todo!()
        }
        (ArbitraryLength(t1), FixedLength(ts2), Variance::Covariant) => {
            let t1 = Type::new(t1);
            ts2.iter()
                .all(|g2| match g2 {
                    TypeOrTypeVarTuple::Type(t2) => {
                        t1.is_super_type_of(i_s, matcher, &Type::new(t2)).bool()
                    }
                    TypeOrTypeVarTuple::TypeVarTuple(_) => {
                        todo!()
                    }
                })
                .into()
        }
        (_, _, _) => unreachable!(),
    }
}

pub fn common_base_type<'x, I: Iterator<Item = &'x TypeOrTypeVarTuple>>(
    i_s: &InferenceState,
    mut ts: I,
) -> DbType {
    if let Some(first) = ts.next() {
        let mut result = match first {
            TypeOrTypeVarTuple::Type(t) => Cow::Borrowed(t),
            TypeOrTypeVarTuple::TypeVarTuple(_) => return i_s.db.python_state.object_db_type(),
        };
        for t in ts {
            let t = match t {
                TypeOrTypeVarTuple::Type(t) => t,
                TypeOrTypeVarTuple::TypeVarTuple(_) => return i_s.db.python_state.object_db_type(),
            };
            result = Cow::Owned(Type::Type(result).common_base_type(i_s, &Type::new(t)));
        }
        result.into_owned()
    } else {
        DbType::Never
    }
}

pub fn execute_type_of_type<'db>(
    i_s: &InferenceState<'db, '_>,
    args: &dyn Arguments<'db>,
    result_context: &mut ResultContext,
    on_type_error: OnTypeError<'db, '_>,
    type_: &DbType,
) -> Inferred {
    match type_ {
        #![allow(unreachable_code)]
        // TODO remove this
        tuple @ DbType::Tuple(tuple_content) => {
            debug!("TODO this does not check the arguments");
            return Inferred::execute_db_type(i_s, tuple.clone());
            // TODO reenable this
            let mut args_iterator = args.iter();
            let (arg, inferred_tup) = if let Some(arg) = args_iterator.next() {
                let inf = arg.infer(i_s, &mut ResultContext::Known(&Type::new(tuple)));
                (arg, inf)
            } else {
                debug!("TODO this does not check the arguments");
                return Inferred::execute_db_type(i_s, tuple.clone());
            };
            if args_iterator.next().is_some() {
                todo!()
            }
            Type::new(tuple).error_if_not_matches(
                i_s,
                &inferred_tup,
                |i_s: &InferenceState<'db, '_>, t1, t2| {
                    (on_type_error.callback)(i_s, None, &|_| todo!(), &arg, t1, t2);
                    args.as_node_ref().to_db_lifetime(i_s.db)
                },
            );
            Inferred::execute_db_type(i_s, tuple.clone())
        }
        DbType::Class(link, generics_list) => Class::from_db_type(i_s.db, *link, generics_list)
            .execute(i_s, args, result_context, on_type_error),
        DbType::TypeVar(t) => {
            if let Some(bound) = &t.type_var.bound {
                execute_type_of_type(i_s, args, result_context, on_type_error, bound);
                Inferred::execute_db_type(i_s, type_.clone())
            } else {
                todo!("{t:?}")
            }
        }
        DbType::NewType(n) => {
            let mut iterator = args.iter();
            if let Some(first) = iterator.next() {
                if iterator.next().is_some() {
                    todo!()
                }
                // TODO match
                Inferred::execute_db_type(i_s, type_.clone())
            } else {
                todo!()
            }
        }
        DbType::Self_ => {
            i_s.current_class()
                .unwrap()
                .execute(i_s, args, result_context, on_type_error);
            Inferred::execute_db_type(i_s, DbType::Self_)
        }
        DbType::Any => Inferred::new_any(),
        DbType::NamedTuple(nt) => {
            let calculated_type_vars = calculate_callable_type_vars_and_return(
                i_s,
                None,
                &nt.constructor,
                args.iter(),
                &|| args.as_node_ref(),
                &mut ResultContext::Unknown,
                on_type_error,
            );
            debug!("TODO use generics for namedtuple");
            Inferred::execute_db_type(i_s, DbType::NamedTuple(nt.clone()))
        }
        _ => todo!("{:?}", type_),
    }
}
