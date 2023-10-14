use std::borrow::Cow;
use std::rc::Rc;

use super::params::has_overlapping_params;
use super::{
    matches_params, maybe_class_usage, CalculatedTypeArguments, FormatData, Generics, Match,
    Matcher, MismatchReason,
};
use crate::database::{ComplexPoint, Database, MetaclassState, PointLink, TypeAlias};
use crate::debug;
use crate::diagnostics::IssueType;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::node_ref::NodeRef;
use crate::type_::{
    simplified_union_from_iterators, CallableContent, CallableParam, CallableParams, ClassGenerics,
    Dataclass, DbType, DoubleStarredParamSpecific, FunctionOverload, GenericClass, GenericItem,
    GenericsList, NamedTuple, ParamSpecArgument, ParamSpecTypeVars, ParamSpecUsage, ParamSpecific,
    RecursiveAlias, StarredParamSpecific, TupleContent, TupleTypeArguments, TypeArguments,
    TypeOrTypeVarTuple, TypeVarKind, TypeVarLike, TypeVarLikeUsage, TypeVarLikes, TypeVarManager,
    TypeVarTupleUsage, TypeVarUsage, TypedDict, TypedDictGenerics, UnionEntry, UnionType, Variance,
};
use crate::type_helpers::{Class, TypeOrClass};
use crate::utils::{join_with_commas, rc_unwrap_or_clone};

pub type ReplaceTypeVarLike<'x> = &'x mut dyn FnMut(TypeVarLikeUsage) -> GenericItem;
pub type ReplaceSelf<'x> = &'x dyn Fn() -> DbType;

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum LookupKind {
    Normal,
    // In CPython there is PyTypeObject (for documentation see CPython's `Doc/c-api/typeobj.rst`).
    // This type object is used to access __and__, when a user types `int & int`. Note that int
    // defines __and__ as well, but the type of int does not, hence it should lead to an error.
    OnlyType,
}

#[derive(Debug, Clone)]
#[allow(clippy::enum_variant_names)]
pub struct Type<'a>(Cow<'a, DbType>);

impl<'x> From<&'x DbType> for Type<'x> {
    fn from(item: &'x DbType) -> Self {
        Self(Cow::Borrowed(item))
    }
}

impl From<DbType> for Type<'static> {
    fn from(item: DbType) -> Self {
        Self(Cow::Owned(item))
    }
}

impl std::ops::Deref for Type<'_> {
    type Target = DbType;

    fn deref(&self) -> &Self::Target {
        self.0.as_ref()
    }
}

impl<'a> Type<'a> {
    pub fn new(t: &'a DbType) -> Self {
        Self(Cow::Borrowed(t))
    }

    pub fn owned(t: DbType) -> Self {
        Self(Cow::Owned(t))
    }

    pub fn into_db_type(self) -> DbType {
        self.0.into_owned()
    }

    pub fn as_db_type(&self) -> DbType {
        self.0.as_ref().clone()
    }

    pub fn as_ref(&self) -> &DbType {
        self
    }

    #[inline]
    pub fn expect_borrowed_class(&self, db: &'a Database) -> Class<'a> {
        match self.0 {
            Cow::Borrowed(t) => {
                let DbType::Class(c) = t else {
                    unreachable!();
                };
                c.class(db)
            }
            Cow::Owned(DbType::Class(ref c)) => Class::from_position(
                NodeRef::from_link(db, c.link),
                Generics::from_non_list_class_generics(db, &c.generics),
                None,
            ),
            _ => unreachable!(),
        }
    }

    pub fn expect_borrowed_db_type(&self) -> &'a DbType {
        match self.0 {
            Cow::Borrowed(t) => t,
            _ => unreachable!(),
        }
    }

    pub fn overlaps(&self, i_s: &InferenceState, other: &Self) -> bool {
        match other.as_ref() {
            DbType::TypeVar(t2_usage) => {
                return match &t2_usage.type_var.kind {
                    TypeVarKind::Unrestricted => true,
                    TypeVarKind::Bound(bound) => self.overlaps(i_s, &bound.into()),
                    TypeVarKind::Constraints(constraints) => {
                        constraints.iter().all(|r2| self.overlaps(i_s, &r2.into()))
                    }
                }
            }
            DbType::Union(union_type2) => {
                return union_type2.iter().any(|t| self.overlaps(i_s, &t.into()))
            }
            DbType::Any => return false, // This is a fallback
            _ => (),
        }

        match self.as_ref() {
            DbType::Class(c) => match other.as_ref() {
                DbType::Class(c) => Self::overlaps_class(i_s, c.class(i_s.db), c.class(i_s.db)),
                _ => false,
            },
            DbType::Type(t1) => match other.as_ref() {
                DbType::Type(t2) => Type::new(t1).overlaps(i_s, &Type::new(t2)),
                _ => false,
            },
            DbType::Callable(c1) => match other.as_ref() {
                DbType::Callable(c2) => {
                    Type::new(&c1.result_type).overlaps(i_s, &Type::new(&c2.result_type))
                        && has_overlapping_params(i_s, &c1.params, &c2.params)
                }
                DbType::Type(t2) => Type::new(self.as_ref()).overlaps(i_s, &Type::new(t2)),
                _ => false,
            },
            DbType::Any => true,
            DbType::Never => todo!(),
            DbType::Literal(literal1) => match other.as_ref() {
                DbType::Literal(literal2) => literal1.value(i_s.db) == literal2.value(i_s.db),
                _ => i_s
                    .db
                    .python_state
                    .literal_type(&literal1.kind)
                    .overlaps(i_s, other),
            },
            DbType::None => matches!(other.as_ref(), DbType::None),
            DbType::TypeVar(t1) => match &t1.type_var.kind {
                TypeVarKind::Unrestricted => true,
                TypeVarKind::Bound(bound) => Type::new(bound).overlaps(i_s, other),
                TypeVarKind::Constraints(constraints) => todo!("{other:?}"),
            },
            DbType::Tuple(t1) => match other.as_ref() {
                DbType::Tuple(t2) => Self::overlaps_tuple(i_s, t1, t2),
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
            DbType::Namespace(file_index) => todo!(),
            DbType::Dataclass(_) => todo!(),
            DbType::TypedDict(_) => todo!(),
            DbType::NamedTuple(_) => todo!(),
            DbType::Enum(_) => todo!(),
            DbType::EnumMember(_) => todo!(),
            DbType::Super { .. } => todo!(),
            DbType::CustomBehavior(_) => false,
        }
    }

    fn matches_internal(
        &self,
        i_s: &InferenceState,
        matcher: &mut Matcher,
        value_type: &Self,
        variance: Variance,
    ) -> Match {
        match self.as_ref() {
            DbType::Class(c) => Self::matches_class_against_type(
                i_s,
                matcher,
                &c.class(i_s.db),
                value_type,
                variance,
            ),
            DbType::Type(t1) => match value_type.as_ref() {
                DbType::Type(t2) => Type::new(t1)
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
            DbType::Callable(c1) => {
                Self::matches_callable_against_arbitrary(i_s, matcher, c1, value_type, variance)
            }
            DbType::None => matches!(value_type.as_ref(), DbType::None).into(),
            DbType::Any if matcher.is_matching_reverse() => {
                debug!("TODO write a test for this. (reverse matching any)");
                matcher.set_all_contained_type_vars_to_any(i_s, self.as_ref());
                Match::True { with_any: true }
            }
            DbType::Any => Match::new_true(),
            DbType::Never => matches!(value_type.as_ref(), DbType::Never).into(),
            DbType::Tuple(t1) => match value_type.as_ref() {
                DbType::Tuple(t2) => {
                    Self::matches_tuple(i_s, matcher, t1, t2, variance).similar_if_false()
                }
                DbType::NamedTuple(t2) => {
                    Self::matches_tuple(i_s, matcher, t1, &t2.as_tuple(), variance)
                        .similar_if_false()
                }
                _ => Match::new_false(),
            },
            DbType::Union(union_type1) => {
                self.matches_union(i_s, matcher, union_type1, value_type, variance)
            }
            DbType::FunctionOverload(overload) if variance == Variance::Invariant => self
                .matches_internal(i_s, matcher, value_type, Variance::Covariant)
                .or(|| value_type.matches_internal(i_s, matcher, self, Variance::Covariant)),
            DbType::FunctionOverload(overload) => Match::all(overload.iter_functions(), |c1| {
                Self::matches_callable_against_arbitrary(i_s, matcher, c1, value_type, variance)
            }),
            DbType::Literal(literal1) => match value_type.as_ref() {
                DbType::Literal(literal2) => {
                    (literal1.value(i_s.db) == literal2.value(i_s.db)).into()
                }
                _ => Match::new_false(),
            },
            DbType::NewType(new_type1) => match value_type.as_ref() {
                DbType::NewType(new_type2) => (new_type1 == new_type2).into(),
                _ => Match::new_false(),
            },
            t1 @ DbType::RecursiveAlias(rec1) => {
                match value_type.as_ref() {
                    t2 @ DbType::Class(_) => {
                        // Classes like aliases can also be recursive in mypy, like `class B(List[B])`.
                        matcher.avoid_recursion(t1, t2, |matcher| {
                            let g = rec1.calculated_db_type(i_s.db);
                            Type::new(g).matches_internal(i_s, matcher, value_type, variance)
                        })
                    }
                    t @ DbType::RecursiveAlias(rec2) => matcher.avoid_recursion(t1, t, |matcher| {
                        let t1 = rec1.calculated_db_type(i_s.db);
                        let t2 = rec2.calculated_db_type(i_s.db);
                        Type::new(t1).matches_internal(i_s, matcher, &Type::new(t2), variance)
                    }),
                    _ => {
                        let g = rec1.calculated_db_type(i_s.db);
                        Type::new(g).matches_internal(i_s, matcher, value_type, variance)
                    }
                }
            }
            DbType::Self_ => match value_type.as_ref() {
                DbType::Self_ => Match::new_true(),
                _ => Match::new_false(),
            },
            DbType::ParamSpecArgs(usage1) => match value_type.as_ref() {
                DbType::ParamSpecArgs(usage2) => (usage1 == usage2).into(),
                _ => Match::new_false(),
            },
            DbType::ParamSpecKwargs(usage1) => match value_type.as_ref() {
                DbType::ParamSpecKwargs(usage2) => (usage1 == usage2).into(),
                _ => Match::new_false(),
            },
            DbType::Dataclass(d1) => match value_type.as_ref() {
                DbType::Dataclass(d2) => {
                    let c1 = d1.class(i_s.db);
                    let c2 = d2.class(i_s.db);
                    Self::matches_class(i_s, matcher, &c1, &c2, Variance::Covariant)
                }
                _ => Match::new_false(),
            },
            DbType::TypedDict(d1) => match value_type.as_ref() {
                DbType::TypedDict(d2) => {
                    let mut matches = Match::new_true();
                    for m1 in d1.members.iter() {
                        if let Some(m2) = d2.find_member(i_s.db, m1.name.as_str(i_s.db)) {
                            if m1.required != m2.required {
                                return Match::new_false().similar_if_false();
                            }
                            matches &= Type::new(&m1.type_).is_same_type(
                                i_s,
                                matcher,
                                &Type::new(&m2.type_),
                            );
                        } else {
                            return Match::new_false().similar_if_false();
                        }
                    }
                    matches.similar_if_false()
                }
                _ => Match::new_false(),
            },
            DbType::NamedTuple(nt1) => match value_type.as_ref() {
                DbType::NamedTuple(nt2) => {
                    let c1 = &nt1.__new__;
                    let c2 = &nt2.__new__;
                    if !c1.type_vars.is_empty() || !c2.type_vars.is_empty() {
                        todo!()
                    } else {
                        (c1.defined_at == c2.defined_at).into()
                    }
                }
                _ => Match::new_false(),
            },
            DbType::Enum(e1) => match value_type.as_ref() {
                DbType::Enum(e2) => (e1 == e2).into(),
                DbType::EnumMember(member) => (e1 == &member.enum_).into(),
                _ => Match::new_false(),
            },
            DbType::EnumMember(m1) => match value_type.as_ref() {
                DbType::EnumMember(m2) => (m1.is_same_member(m2)).into(),
                _ => Match::new_false(),
            },
            DbType::Module(file_index) => Match::new_false(),
            DbType::Namespace(file_index) => todo!(),
            DbType::Super { .. } => todo!(),
            DbType::CustomBehavior(_) => Match::new_false(),
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
        let mut m = Match::new_false();
        for (_, t2) in value_type.mro(i_s.db) {
            m = match t2 {
                TypeOrClass::Class(c2) => match self.maybe_class(i_s.db) {
                    Some(c1) => Self::matches_class(i_s, matcher, &c1, &c2, Variance::Covariant),
                    None => {
                        // TODO performance: This might be slow, because it always
                        // allocates when e.g.  Foo is passed to def x(f: Foo | None): ...
                        // This is a bit unfortunate, especially because it loops over the
                        // mro and allocates every time.
                        let t2 = Type::owned(c2.as_db_type(i_s.db));
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
                } else if let DbType::Literal(literal) = value_type.as_ref() {
                    if !matcher.ignore_promotions() {
                        return self.check_promotion(
                            i_s,
                            matcher,
                            i_s.db
                                .python_state
                                .literal_instance(&literal.kind)
                                .class
                                .node_ref,
                        );
                    }
                }
                Match::new_false()
            });
        debug!(
            "Match covariant {} :> {} -> {:?}",
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
        class2_node_ref: NodeRef,
    ) -> Match {
        let ComplexPoint::Class(storage) = class2_node_ref.complex().unwrap() else {
            unreachable!()
        };
        if let Some(promote_to) = storage.promote_to.get() {
            let cls_node_ref = NodeRef::from_link(i_s.db, promote_to);
            self.is_same_type(
                i_s,
                matcher,
                &Type::owned(DbType::new_class(
                    cls_node_ref.as_link(),
                    ClassGenerics::None,
                )),
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
        debug!(
            "Match invariant {} ≡ {} -> {:?}",
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
        let mut m = Match::new_false();
        // 2. Check if it is a class with a protocol
        if let Some(class1) = self.maybe_class(i_s.db) {
            // TODO this should probably be checked before normal mro checking?!
            if class1.is_protocol(i_s.db) {
                m = matcher.avoid_recursion(self, value_type, |matcher| {
                    class1.check_protocol_match(i_s, matcher, value_type, variance)
                });
                if m.bool() {
                    return m;
                }
            }
        }
        // 3. Check if the value_type is special like Any or a Typevar and needs to be checked
        //    again.
        match value_type.as_ref() {
            DbType::Any if matcher.is_matching_reverse() => return Match::new_true(),
            DbType::Any => {
                matcher.set_all_contained_type_vars_to_any(i_s, self);
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
                    match &t2.type_var.kind {
                        TypeVarKind::Unrestricted => (),
                        TypeVarKind::Bound(bound) => {
                            let m = self.simple_matches(i_s, &Type::new(bound), variance);
                            if m.bool() {
                                return m;
                            }
                        }
                        TypeVarKind::Constraints(constraints) => {
                            let m = constraints
                                .iter()
                                .all(|r| self.simple_matches(i_s, &Type::new(r), variance).bool());
                            if m {
                                return Match::new_true();
                            }
                        }
                    }
                }
            }
            // Necessary to e.g. match int to Literal[1, 2]
            DbType::Union(u2)
                if variance == Variance::Covariant
                // Union matching was already done.
                && !self.is_union_like() =>
            {
                if matcher.is_matching_reverse() {
                    debug!("TODO matching reverse?");
                }
                let mut result: Option<Match> = None;
                for t in u2.iter() {
                    let r = self.matches(i_s, matcher, &Type::new(t), variance);
                    if !r.bool() {
                        return r.bool().into();
                    } else if let Some(old) = result {
                        result = Some(old & r)
                    } else {
                        result = Some(r)
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
                if let Some(cls) = i_s.current_class() {
                    return self.simple_matches(
                        i_s,
                        &Type::owned(cls.as_db_type(i_s.db)),
                        variance,
                    );
                }
            }
            DbType::Module(_) => {
                m = m.or(|| {
                    self.matches(
                        i_s,
                        matcher,
                        &i_s.db.python_state.module_db_type().into(),
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
        match value_type.as_ref() {
            DbType::TypeVar(type_var2) if matcher.is_matching_reverse() => {
                matcher.match_or_add_type_var(i_s, type_var2, self, variance.invert())
            }
            DbType::Union(u2) => match variance {
                Variance::Covariant => {
                    let mut matches = Match::new_true();
                    for g2 in u2.iter() {
                        let t2 = Type::new(g2);
                        matches &= Match::any(u1.iter(), |g1| {
                            Type::new(g1).matches(i_s, matcher, &t2, variance)
                        })
                    }
                    matches
                }
                Variance::Invariant => {
                    self.is_super_type_of(i_s, matcher, value_type)
                        & self.is_sub_type_of(i_s, matcher, value_type)
                }
                Variance::Contravariant => unreachable!(),
            },
            _ => match variance {
                Variance::Covariant => Match::any(u1.iter(), |g| {
                    Type::new(g).matches(i_s, matcher, value_type, variance)
                }),
                Variance::Invariant => Match::all(u1.iter(), |g| {
                    Type::new(g).matches(i_s, matcher, value_type, variance)
                }),
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
            let result = class1
                .generics()
                .matches(i_s, matcher, class2.generics(), type_vars, variance)
                .similar_if_false();
            if !result.bool() {
                let mut check = |i_s: &InferenceState, n| {
                    let t1 = class1.nth_type_argument(i_s.db, n);
                    if matches!(t1, DbType::Any) {
                        return false;
                    }
                    let t2 = class2.nth_type_argument(i_s.db, n);
                    if matches!(t2, DbType::Any) {
                        return false;
                    }
                    Type::owned(t1)
                        .matches(i_s, matcher, &Type::owned(t2), variance)
                        .bool()
                };
                if class1.node_ref == i_s.db.python_state.list_node_ref() && check(i_s, 0) {
                    return Match::False {
                        similar: true,
                        reason: MismatchReason::SequenceInsteadOfListNeeded,
                    };
                } else if class1.node_ref == i_s.db.python_state.dict_node_ref() && check(i_s, 1) {
                    return Match::False {
                        similar: true,
                        reason: MismatchReason::MappingInsteadOfDictNeeded,
                    };
                }
            }
            return result;
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
        match value_type.as_ref() {
            DbType::Class(c2) => {
                Self::matches_class(i_s, matcher, class1, &c2.class(i_s.db), variance)
            }
            DbType::Type(t2) => {
                if let DbType::Class(c2) = t2.as_ref() {
                    match c2.class(i_s.db).use_cached_class_infos(i_s.db).metaclass {
                        MetaclassState::Some(link) => {
                            return Type::owned(class1.as_db_type(i_s.db)).matches(
                                i_s,
                                matcher,
                                &Type::owned(DbType::new_class(link, ClassGenerics::None)),
                                variance,
                            );
                        }
                        MetaclassState::Unknown => {
                            todo!()
                        }
                        MetaclassState::None => (),
                    }
                }
                Match::new_false()
            }
            DbType::Literal(literal) if variance == Variance::Covariant => {
                Self::matches_class_against_type(
                    i_s,
                    matcher,
                    class1,
                    &i_s.db.python_state.literal_type(&literal.kind),
                    variance,
                )
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
        match value_type.as_ref() {
            DbType::FunctionOverload(overload) if variance == Variance::Covariant => {
                if matcher.is_matching_reverse() {
                    todo!()
                }
                Match::any(overload.iter_functions(), |c2| {
                    Self::matches_callable(i_s, matcher, c1, c2)
                })
            }
            DbType::Type(t2) if c1.params == CallableParams::Any => {
                Type::new(&c1.result_type).is_super_type_of(i_s, matcher, &Type::new(t2.as_ref()))
            }
            _ => match value_type.maybe_callable(i_s) {
                Some(CallableLike::Callable(c2)) => Self::matches_callable(i_s, matcher, c1, &c2),
                Some(CallableLike::Overload(overload)) if variance == Variance::Covariant => {
                    Self::matches_callable_against_arbitrary(
                        i_s,
                        matcher,
                        c1,
                        &Type::owned(DbType::FunctionOverload(overload)),
                        variance,
                    )
                }
                _ => Match::new_false(),
            },
        }
    }

    fn matches_callable(
        i_s: &InferenceState,
        matcher: &mut Matcher,
        c1: &CallableContent,
        c2: &CallableContent,
    ) -> Match {
        // TODO This if is weird.
        if !matcher.has_type_var_matcher() {
            if !c2.type_vars.is_empty() {
                let mut matcher = Matcher::new_reverse_callable_matcher(c2);
                return Type::matches_callable(i_s, &mut matcher, c1, c2);
            }
        }
        Type::new(&c1.result_type).is_super_type_of(i_s, matcher, &Type::new(&c2.result_type))
            & matches_params(
                i_s,
                matcher,
                &c1.params,
                &c2.params,
                (!c2.type_vars.is_empty()).then(|| (&c2.type_vars, c2.defined_at)),
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
        match_tuple_type_arguments(i_s, matcher, &t1.args, &t2.args, variance)
    }

    fn overlaps_tuple(i_s: &InferenceState, t1: &TupleContent, t2: &TupleContent) -> bool {
        use TupleTypeArguments::*;
        match (&t1.args, &t2.args) {
            (FixedLength(ts1), FixedLength(ts2)) => {
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
            (ArbitraryLength(t1), ArbitraryLength(t2)) => {
                Type::new(t1).overlaps(i_s, &Type::new(t2))
            }
            (ArbitraryLength(t1), FixedLength(ts2)) => {
                let t1 = Type::new(t1);
                ts2.iter().all(|t2| match t2 {
                    TypeOrTypeVarTuple::Type(t2) => t1.overlaps(i_s, &Type::new(t2)),
                    TypeOrTypeVarTuple::TypeVarTuple(t2) => {
                        todo!()
                    }
                })
            }
            (FixedLength(ts1), ArbitraryLength(t2)) => {
                let t2 = Type::new(t2);
                ts1.iter().all(|t1| match t1 {
                    TypeOrTypeVarTuple::Type(t1) => Type::new(t1).overlaps(i_s, &t2),
                    TypeOrTypeVarTuple::TypeVarTuple(t1) => {
                        todo!()
                    }
                })
            }
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
            if let TypeOrClass::Class(c1) = c1 {
                if Self::overlaps_class(i_s, c1, class2) {
                    return true;
                }
            }
        }
        for (_, c2) in class2.mro(i_s.db) {
            if let TypeOrClass::Class(c2) = c2 {
                if Self::overlaps_class(i_s, class1, c2) {
                    return true;
                }
            }
        }
        false
    }

    pub fn error_if_not_matches<'db>(
        &self,
        i_s: &InferenceState<'db, '_>,
        value: &Inferred,
        callback: impl FnOnce(Box<str>, Box<str>) -> NodeRef<'db>,
    ) {
        self.error_if_not_matches_with_matcher(
            i_s,
            &mut Matcher::default(),
            value,
            Some(|t1, t2, reason: &MismatchReason| callback(t1, t2)),
        );
    }

    pub fn error_if_not_matches_with_matcher<'db>(
        &self,
        i_s: &InferenceState<'db, '_>,
        matcher: &mut Matcher,
        value: &Inferred,
        callback: Option<impl FnOnce(Box<str>, Box<str>, &MismatchReason) -> NodeRef<'db>>,
    ) -> Match {
        let value_type = value.as_type(i_s);
        let matches = self.is_super_type_of(i_s, matcher, &value_type);
        if let Match::False { ref reason, .. } = matches {
            let mut fmt1 = FormatData::new_short(i_s.db);
            let mut fmt2 = FormatData::with_matcher(i_s.db, matcher);
            if self.is_literal_or_literal_in_tuple() {
                fmt1.hide_implicit_literals = false;
                fmt2.hide_implicit_literals = false;
            }
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
                &matches
            );
            if let Some(callback) = callback {
                let node_ref = callback(input, wanted, reason);
                match reason {
                    MismatchReason::SequenceInsteadOfListNeeded => {
                        node_ref.add_issue(
                            i_s,
                            IssueType::InvariantNote {
                                actual: "List",
                                maybe: "Sequence",
                            },
                        );
                    }
                    MismatchReason::MappingInsteadOfDictNeeded => {
                        node_ref.add_issue(
                            i_s,
                            IssueType::InvariantNote {
                                actual: "Dict",
                                maybe: "Mapping",
                            },
                        );
                    }
                    MismatchReason::ProtocolMismatches { notes } => {
                        for note in notes.iter() {
                            node_ref.add_issue(i_s, IssueType::Note(note.clone()));
                        }
                    }
                    _ => (),
                }
            }
        }
        matches
    }

    pub fn execute_and_resolve_type_vars(
        &self,
        i_s: &InferenceState,
        calculated_type_args: &CalculatedTypeArguments,
        class: Option<&Class>,
        replace_self_type: ReplaceSelf,
    ) -> Inferred {
        let db_type =
            self.internal_resolve_type_vars(i_s, calculated_type_args, class, replace_self_type);
        debug!(
            "Resolved type vars: {}",
            Type::new(&db_type).format_short(i_s.db)
        );
        Inferred::from_type(db_type)
    }

    fn internal_resolve_type_vars(
        &self,
        i_s: &InferenceState,
        calculated_type_args: &CalculatedTypeArguments,
        class: Option<&Class>,
        replace_self_type: ReplaceSelf,
    ) -> DbType {
        self.replace_type_var_likes_and_self(
            i_s.db,
            &mut |usage| {
                if let Some(c) = class {
                    if let Some(generic_item) = maybe_class_usage(i_s.db, c, &usage) {
                        return generic_item;
                    }
                }
                calculated_type_args.lookup_type_var_usage(i_s, usage)
            },
            replace_self_type,
        )
    }

    pub fn replace_type_var_likes(
        &self,
        db: &Database,
        callable: &mut impl FnMut(TypeVarLikeUsage) -> GenericItem,
    ) -> DbType {
        self.replace_type_var_likes_and_self(db, callable, &|| DbType::Self_)
    }

    pub fn replace_type_var_likes_and_self(
        &self,
        db: &Database,
        callable: ReplaceTypeVarLike,
        replace_self: ReplaceSelf,
    ) -> DbType {
        let replace_tuple_likes = |args: &TupleTypeArguments,
                                   callable: ReplaceTypeVarLike,
                                   replace_self: ReplaceSelf| {
            match args {
                TupleTypeArguments::FixedLength(ts) => {
                    let mut new_args = vec![];
                    for g in ts.iter() {
                        match g {
                            TypeOrTypeVarTuple::Type(t) => new_args.push(TypeOrTypeVarTuple::Type(
                                Type::new(t).replace_type_var_likes_and_self(
                                    db,
                                    callable,
                                    replace_self,
                                ),
                            )),
                            TypeOrTypeVarTuple::TypeVarTuple(t) => {
                                match callable(TypeVarLikeUsage::TypeVarTuple(Cow::Borrowed(t))) {
                                    GenericItem::TypeArguments(new) => {
                                        match new.args {
                                            TupleTypeArguments::FixedLength(fixed) => {
                                                // Performance issue: clone could probably be removed. Rc -> Vec check
                                                // https://github.com/rust-lang/rust/issues/93610#issuecomment-1528108612
                                                new_args.extend(fixed.iter().cloned())
                                            }
                                            TupleTypeArguments::ArbitraryLength(t) => {
                                                match ts.len() {
                                                    // TODO this might be wrong with different data types??
                                                    1 => {
                                                        return TupleTypeArguments::ArbitraryLength(
                                                            t,
                                                        )
                                                    }
                                                    _ => todo!(),
                                                }
                                            }
                                        }
                                    }
                                    x => unreachable!("{x:?}"),
                                }
                            }
                        }
                    }
                    TupleTypeArguments::FixedLength(new_args.into())
                }
                TupleTypeArguments::ArbitraryLength(t) => {
                    TupleTypeArguments::ArbitraryLength(Box::new(
                        Type::new(t).replace_type_var_likes_and_self(db, callable, replace_self),
                    ))
                }
            }
        };
        let mut replace_generics = |generics: &GenericsList| {
            GenericsList::new_generics(
                generics
                    .iter()
                    .map(|g| match g {
                        GenericItem::TypeArgument(t) => {
                            GenericItem::TypeArgument(Type::new(t).replace_type_var_likes_and_self(
                                db,
                                callable,
                                replace_self,
                            ))
                        }
                        GenericItem::TypeArguments(ts) => {
                            GenericItem::TypeArguments(TypeArguments {
                                args: replace_tuple_likes(&ts.args, callable, replace_self),
                            })
                        }
                        GenericItem::ParamSpecArgument(p) => {
                            let mut type_vars = p.type_vars.clone().map(|t| t.type_vars.as_vec());
                            GenericItem::ParamSpecArgument(ParamSpecArgument::new(
                                Self::replace_callable_param_type_var_likes_and_self(
                                    db,
                                    &p.params,
                                    &mut type_vars,
                                    p.type_vars.as_ref().map(|t| t.in_definition),
                                    callable,
                                    replace_self,
                                )
                                .0,
                                type_vars.map(|t| ParamSpecTypeVars {
                                    type_vars: TypeVarLikes::from_vec(t),
                                    in_definition: p.type_vars.as_ref().unwrap().in_definition,
                                }),
                            ))
                        }
                    })
                    .collect(),
            )
        };
        match self.as_ref() {
            DbType::Any => DbType::Any,
            DbType::None => DbType::None,
            DbType::Never => DbType::Never,
            DbType::Class(c) => DbType::new_class(c.link, c.generics.map_list(replace_generics)),
            DbType::FunctionOverload(overload) => {
                DbType::FunctionOverload(overload.map_functions(|functions| {
                    functions
                        .iter()
                        .map(|c| {
                            Self::replace_type_var_likes_and_self_for_callable(
                                c,
                                db,
                                callable,
                                replace_self,
                            )
                        })
                        .collect()
                }))
            }
            DbType::Union(u) => {
                let new_entries = u
                    .entries
                    .iter()
                    .map(|u| {
                        (
                            u.format_index,
                            Type::new(&u.type_).replace_type_var_likes_and_self(
                                db,
                                callable,
                                replace_self,
                            ),
                        )
                    })
                    .collect::<Vec<_>>();
                let i_s = InferenceState::new(db);
                let highest_union_format_index = new_entries
                    .iter()
                    .map(|e| e.1.highest_union_format_index())
                    .max()
                    .unwrap();
                simplified_union_from_iterators(
                    &i_s,
                    new_entries.into_iter(),
                    highest_union_format_index,
                    u.format_as_optional,
                )
            }
            DbType::TypeVar(t) => match callable(TypeVarLikeUsage::TypeVar(Cow::Borrowed(t))) {
                GenericItem::TypeArgument(t) => t,
                GenericItem::TypeArguments(ts) => unreachable!(),
                GenericItem::ParamSpecArgument(params) => todo!(),
            },
            DbType::Type(t) => DbType::Type(Rc::new(Type::new(t).replace_type_var_likes_and_self(
                db,
                callable,
                replace_self,
            ))),
            DbType::Tuple(content) => DbType::Tuple(Rc::new(TupleContent::new(
                replace_tuple_likes(&content.args, callable, replace_self),
            ))),
            DbType::Callable(content) => {
                DbType::Callable(Rc::new(Self::replace_type_var_likes_and_self_for_callable(
                    content,
                    db,
                    callable,
                    replace_self,
                )))
            }
            DbType::Literal { .. } => self.as_db_type(),
            DbType::NewType(t) => DbType::NewType(t.clone()),
            DbType::RecursiveAlias(rec) => DbType::RecursiveAlias(Rc::new(RecursiveAlias::new(
                rec.link,
                rec.generics.as_ref().map(replace_generics),
            ))),
            DbType::Module(file_index) => DbType::Module(*file_index),
            DbType::Namespace(namespace) => DbType::Namespace(namespace.clone()),
            DbType::Self_ => replace_self(),
            DbType::ParamSpecArgs(usage) => todo!(),
            DbType::ParamSpecKwargs(usage) => todo!(),
            DbType::Dataclass(d) => DbType::Dataclass({
                if matches!(d.class.generics, ClassGenerics::List(_)) {
                    Dataclass::new(
                        GenericClass {
                            link: d.class.link,
                            generics: d.class.generics.map_list(replace_generics),
                        },
                        d.options,
                    )
                } else {
                    d.clone()
                }
            }),
            DbType::TypedDict(td) => {
                let generics = match &td.generics {
                    TypedDictGenerics::None => TypedDictGenerics::None,
                    TypedDictGenerics::NotDefinedYet(tvs) => {
                        TypedDictGenerics::NotDefinedYet(tvs.clone())
                    }
                    TypedDictGenerics::Generics(generics) => {
                        TypedDictGenerics::Generics(replace_generics(generics))
                    }
                };
                DbType::TypedDict(TypedDict::new(
                    td.name,
                    td.members
                        .iter()
                        .map(|m| {
                            m.replace_type(|t| {
                                Type::new(t).replace_type_var_likes_and_self(
                                    db,
                                    callable,
                                    replace_self,
                                )
                            })
                        })
                        .collect(),
                    td.defined_at,
                    generics,
                ))
            }
            DbType::NamedTuple(nt) => {
                let mut constructor = nt.__new__.as_ref().clone();
                constructor.params = CallableParams::Simple(
                    constructor
                        .expect_simple_params()
                        .iter()
                        .map(|param| {
                            let ParamSpecific::PositionalOrKeyword(t) = &param.param_specific else {
                                return param.clone()
                            };
                            CallableParam {
                                param_specific: ParamSpecific::PositionalOrKeyword(
                                    Type::new(t).replace_type_var_likes_and_self(
                                        db,
                                        callable,
                                        replace_self,
                                    ),
                                ),
                                has_default: param.has_default,
                                name: param.name,
                            }
                        })
                        .collect(),
                );
                DbType::NamedTuple(Rc::new(NamedTuple::new(nt.name, constructor)))
            }
            t @ (DbType::Enum(_) | DbType::EnumMember(_)) => t.clone(),
            DbType::Super { .. } => todo!(),
            DbType::CustomBehavior(_) => todo!(),
        }
    }

    pub fn replace_type_var_likes_and_self_for_callable(
        c: &CallableContent,
        db: &Database,
        callable: ReplaceTypeVarLike,
        replace_self: ReplaceSelf,
    ) -> CallableContent {
        let has_type_vars = !c.type_vars.is_empty();
        let mut type_vars = has_type_vars.then(|| c.type_vars.clone().as_vec());
        let (params, remap_data) = Self::replace_callable_param_type_var_likes_and_self(
            db,
            &c.params,
            &mut type_vars,
            Some(c.defined_at),
            callable,
            replace_self,
        );
        let mut result_type =
            Type::new(&c.result_type).replace_type_var_likes_and_self(db, callable, replace_self);
        if let Some(remap_data) = remap_data {
            result_type = Type::new(&result_type).replace_type_var_likes_and_self(
                db,
                &mut |usage| {
                    Self::replace_param_spec_inner_type_var_likes_and_self(
                        usage,
                        c.defined_at,
                        remap_data,
                    )
                },
                replace_self,
            );
        }
        CallableContent {
            name: c.name,
            class_name: c.class_name,
            defined_at: c.defined_at,
            kind: c.kind,
            type_vars: type_vars
                .map(TypeVarLikes::from_vec)
                .unwrap_or_else(|| db.python_state.empty_type_var_likes.clone()),
            params,
            result_type,
        }
    }

    fn rewrite_late_bound_callables_for_callable(
        c: &CallableContent,
        manager: &TypeVarManager,
    ) -> CallableContent {
        let type_vars = manager
            .iter()
            .filter_map(|t| {
                (t.most_outer_callable == Some(c.defined_at)).then(|| t.type_var_like.clone())
            })
            .collect::<Rc<_>>();
        CallableContent {
            name: c.name,
            class_name: c.class_name,
            defined_at: c.defined_at,
            kind: c.kind,
            type_vars: TypeVarLikes::new(type_vars),
            params: match &c.params {
                CallableParams::Simple(params) => CallableParams::Simple(
                    params
                        .iter()
                        .map(|p| CallableParam {
                            param_specific: match &p.param_specific {
                                ParamSpecific::PositionalOnly(t) => ParamSpecific::PositionalOnly(
                                    Type::new(t).rewrite_late_bound_callables(manager),
                                ),
                                ParamSpecific::PositionalOrKeyword(t) => {
                                    ParamSpecific::PositionalOrKeyword(
                                        Type::new(t).rewrite_late_bound_callables(manager),
                                    )
                                }
                                ParamSpecific::KeywordOnly(t) => ParamSpecific::KeywordOnly(
                                    Type::new(t).rewrite_late_bound_callables(manager),
                                ),
                                ParamSpecific::Starred(s) => ParamSpecific::Starred(match s {
                                    StarredParamSpecific::ArbitraryLength(t) => {
                                        StarredParamSpecific::ArbitraryLength(
                                            Type::new(t).rewrite_late_bound_callables(manager),
                                        )
                                    }
                                    StarredParamSpecific::ParamSpecArgs(_) => todo!(),
                                }),
                                ParamSpecific::DoubleStarred(d) => {
                                    ParamSpecific::DoubleStarred(match d {
                                        DoubleStarredParamSpecific::ValueType(t) => {
                                            DoubleStarredParamSpecific::ValueType(
                                                Type::new(t).rewrite_late_bound_callables(manager),
                                            )
                                        }
                                        DoubleStarredParamSpecific::ParamSpecKwargs(_) => {
                                            todo!()
                                        }
                                    })
                                }
                            },
                            has_default: p.has_default,
                            name: p.name,
                        })
                        .collect(),
                ),
                CallableParams::Any => CallableParams::Any,
                CallableParams::WithParamSpec(types, param_spec) => CallableParams::WithParamSpec(
                    types
                        .iter()
                        .map(|t| Type::new(t).rewrite_late_bound_callables(manager))
                        .collect(),
                    manager.remap_param_spec(param_spec),
                ),
            },
            result_type: Type::new(&c.result_type).rewrite_late_bound_callables(manager),
        }
    }

    fn replace_callable_param_type_var_likes_and_self(
        db: &Database,
        params: &CallableParams,
        type_vars: &mut Option<Vec<TypeVarLike>>,
        in_definition: Option<PointLink>,
        callable: ReplaceTypeVarLike,
        replace_self: ReplaceSelf,
    ) -> (CallableParams, Option<(PointLink, usize)>) {
        let mut replace_data = None;
        let new_params = match params {
            CallableParams::Simple(params) => CallableParams::Simple(
                params
                    .iter()
                    .map(|p| CallableParam {
                        param_specific: match &p.param_specific {
                            ParamSpecific::PositionalOnly(t) => ParamSpecific::PositionalOnly(
                                Type::new(t).replace_type_var_likes_and_self(
                                    db,
                                    callable,
                                    replace_self,
                                ),
                            ),
                            ParamSpecific::PositionalOrKeyword(t) => {
                                ParamSpecific::PositionalOrKeyword(
                                    Type::new(t).replace_type_var_likes_and_self(
                                        db,
                                        callable,
                                        replace_self,
                                    ),
                                )
                            }
                            ParamSpecific::KeywordOnly(t) => ParamSpecific::KeywordOnly(
                                Type::new(t).replace_type_var_likes_and_self(
                                    db,
                                    callable,
                                    replace_self,
                                ),
                            ),
                            ParamSpecific::Starred(s) => ParamSpecific::Starred(match s {
                                StarredParamSpecific::ArbitraryLength(t) => {
                                    StarredParamSpecific::ArbitraryLength(
                                        Type::new(t).replace_type_var_likes_and_self(
                                            db,
                                            callable,
                                            replace_self,
                                        ),
                                    )
                                }
                                StarredParamSpecific::ParamSpecArgs(_) => todo!(),
                            }),
                            ParamSpecific::DoubleStarred(d) => {
                                ParamSpecific::DoubleStarred(match d {
                                    DoubleStarredParamSpecific::ValueType(t) => {
                                        DoubleStarredParamSpecific::ValueType(
                                            Type::new(t).replace_type_var_likes_and_self(
                                                db,
                                                callable,
                                                replace_self,
                                            ),
                                        )
                                    }
                                    DoubleStarredParamSpecific::ParamSpecKwargs(_) => {
                                        todo!()
                                    }
                                })
                            }
                        },
                        has_default: p.has_default,
                        name: p.name,
                    })
                    .collect(),
            ),
            CallableParams::Any => CallableParams::Any,
            CallableParams::WithParamSpec(types, param_spec) => {
                let result = callable(TypeVarLikeUsage::ParamSpec(Cow::Borrowed(param_spec)));
                let GenericItem::ParamSpecArgument(mut new) = result else {
                    unreachable!()
                };
                if let Some(new_spec_type_vars) = new.type_vars {
                    if let Some(in_definition) = in_definition {
                        let type_var_len = type_vars.as_ref().map(|t| t.len()).unwrap_or(0);
                        replace_data = Some((new_spec_type_vars.in_definition, type_var_len));
                        let new_params = Type::replace_callable_param_type_var_likes_and_self(
                            db,
                            &new.params,
                            &mut None,
                            None,
                            &mut |usage| {
                                Type::replace_param_spec_inner_type_var_likes_and_self(
                                    usage,
                                    in_definition,
                                    replace_data.unwrap(),
                                )
                            },
                            replace_self,
                        );
                        if let Some(type_vars) = type_vars.as_mut() {
                            type_vars.extend(new_spec_type_vars.type_vars.as_vec());
                        } else {
                            *type_vars = Some(new_spec_type_vars.type_vars.as_vec());
                        }
                        new.params = new_params.0;
                    } else {
                        debug_assert!(type_vars.is_none());
                        *type_vars = Some(new_spec_type_vars.type_vars.as_vec());
                        todo!("Can probably just be removed")
                    }
                }
                if types.is_empty() {
                    new.params
                } else {
                    match new.params {
                        CallableParams::Simple(params) => {
                            // Performance issue: Rc -> Vec check https://github.com/rust-lang/rust/issues/93610#issuecomment-1528108612
                            let mut params = Vec::from(params.as_ref());
                            params.splice(
                                0..0,
                                types.iter().map(|t| CallableParam {
                                    param_specific: ParamSpecific::PositionalOnly(
                                        Type::new(t).replace_type_var_likes_and_self(
                                            db,
                                            callable,
                                            replace_self,
                                        ),
                                    ),
                                    name: None,
                                    has_default: false,
                                }),
                            );
                            CallableParams::Simple(Rc::from(params))
                        }
                        CallableParams::Any => CallableParams::Any,
                        CallableParams::WithParamSpec(new_types, p) => {
                            let mut types: Vec<DbType> = types
                                .iter()
                                .map(|t| {
                                    Type::new(t).replace_type_var_likes_and_self(
                                        db,
                                        callable,
                                        replace_self,
                                    )
                                })
                                .collect();
                            // Performance issue: Rc -> Vec check https://github.com/rust-lang/rust/issues/93610#issuecomment-1528108612
                            types.extend(new_types.iter().cloned());
                            CallableParams::WithParamSpec(types.into(), p)
                        }
                    }
                }
            }
        };
        (new_params, replace_data)
    }

    fn replace_param_spec_inner_type_var_likes_and_self(
        mut usage: TypeVarLikeUsage,
        in_definition: PointLink,
        replace_data: (PointLink, usize),
    ) -> GenericItem {
        if usage.in_definition() == replace_data.0 {
            usage.update_in_definition_and_index(
                in_definition,
                (usage.index().as_usize() + replace_data.1).into(),
            );
        }
        usage.into_generic_item()
    }

    pub fn rewrite_late_bound_callables(&self, manager: &TypeVarManager) -> DbType {
        let rewrite_generics = |generics: &GenericsList| {
            GenericsList::new_generics(
                generics
                    .iter()
                    .map(|g| match g {
                        GenericItem::TypeArgument(t) => GenericItem::TypeArgument(
                            Type::new(t).rewrite_late_bound_callables(manager),
                        ),
                        GenericItem::TypeArguments(ts) => todo!(),
                        GenericItem::ParamSpecArgument(p) => GenericItem::ParamSpecArgument({
                            debug_assert!(p.type_vars.is_none());
                            ParamSpecArgument {
                                params: match &p.params {
                                    CallableParams::WithParamSpec(types, param_spec) => {
                                        CallableParams::WithParamSpec(
                                            types
                                                .iter()
                                                .map(|t| {
                                                    Type::new(t)
                                                        .rewrite_late_bound_callables(manager)
                                                })
                                                .collect(),
                                            manager.remap_param_spec(param_spec),
                                        )
                                    }
                                    CallableParams::Simple(x) => unreachable!(),
                                    CallableParams::Any => unreachable!(),
                                },
                                type_vars: p.type_vars.clone(),
                            }
                        }),
                    })
                    .collect(),
            )
        };
        match self.as_ref() {
            DbType::Any => DbType::Any,
            DbType::None => DbType::None,
            DbType::Never => DbType::Never,
            DbType::Class(c) => DbType::Class(GenericClass {
                link: c.link,
                generics: c.generics.map_list(rewrite_generics),
            }),
            DbType::Union(u) => DbType::Union(UnionType {
                entries: u
                    .entries
                    .iter()
                    .map(|e| UnionEntry {
                        type_: Type::new(&e.type_).rewrite_late_bound_callables(manager),
                        format_index: e.format_index,
                    })
                    .collect(),
                format_as_optional: u.format_as_optional,
            }),
            DbType::FunctionOverload(overload) => {
                DbType::FunctionOverload(overload.map_functions(|functions| {
                    functions
                        .iter()
                        .map(|e| Self::rewrite_late_bound_callables_for_callable(e, manager))
                        .collect()
                }))
            }
            DbType::TypeVar(t) => DbType::TypeVar(manager.remap_type_var(t)),
            DbType::Type(db_type) => DbType::Type(Rc::new(
                Type::new(db_type).rewrite_late_bound_callables(manager),
            )),
            DbType::Tuple(content) => DbType::Tuple(match &content.args {
                TupleTypeArguments::FixedLength(ts) => Rc::new(TupleContent::new_fixed_length(
                    ts.iter()
                        .map(|g| match g {
                            TypeOrTypeVarTuple::Type(t) => TypeOrTypeVarTuple::Type(
                                Type::new(t).rewrite_late_bound_callables(manager),
                            ),
                            TypeOrTypeVarTuple::TypeVarTuple(t) => {
                                TypeOrTypeVarTuple::TypeVarTuple(manager.remap_type_var_tuple(t))
                            }
                        })
                        .collect(),
                )),
                TupleTypeArguments::ArbitraryLength(t) => {
                    Rc::new(TupleContent::new_arbitrary_length(
                        Type::new(t).rewrite_late_bound_callables(manager),
                    ))
                }
            }),
            DbType::Literal { .. } => self.as_db_type(),
            DbType::Callable(content) => DbType::Callable(Rc::new(
                Self::rewrite_late_bound_callables_for_callable(content, manager),
            )),
            DbType::NewType(_) => todo!(),
            DbType::RecursiveAlias(recursive_alias) => {
                DbType::RecursiveAlias(Rc::new(RecursiveAlias::new(
                    recursive_alias.link,
                    recursive_alias.generics.as_ref().map(rewrite_generics),
                )))
            }
            DbType::ParamSpecArgs(usage) => todo!(),
            DbType::ParamSpecKwargs(usage) => todo!(),
            DbType::Dataclass(d) => DbType::Dataclass(Dataclass::new(
                GenericClass {
                    link: d.class.link,
                    generics: d.class.generics.map_list(rewrite_generics),
                },
                d.options,
            )),
            DbType::TypedDict(_) => todo!(),
            DbType::NamedTuple(_) => todo!(),
            DbType::Enum(_) => todo!(),
            DbType::EnumMember(_) => todo!(),
            DbType::Super { .. } => todo!(),
            t @ (DbType::Module(_)
            | DbType::Namespace(_)
            | DbType::Self_
            | DbType::CustomBehavior(_)) => t.clone(),
        }
    }

    pub fn on_any_resolved_context_type(
        &self,
        i_s: &InferenceState,
        matcher: &mut Matcher,
        callable: &mut impl FnMut(&mut Matcher, &DbType) -> bool,
    ) -> bool {
        match self.as_ref() {
            DbType::Union(union_type) => union_type
                .iter()
                .any(|t| Type::new(t).on_any_resolved_context_type(i_s, matcher, callable)),
            DbType::RecursiveAlias(r) => Type::new(r.calculated_db_type(i_s.db))
                .on_any_resolved_context_type(i_s, matcher, callable),
            db_type @ DbType::TypeVar(_) => {
                if matcher.might_have_defined_type_vars() {
                    Type::owned(matcher.replace_type_var_likes_for_nested_context(i_s.db, db_type))
                        .on_any_resolved_context_type(i_s, matcher, callable)
                } else {
                    false
                }
            }
            t => callable(matcher, t),
        }
    }

    pub fn on_any_class(
        &self,
        i_s: &InferenceState,
        matcher: &mut Matcher,
        callable: &mut impl FnMut(&mut Matcher, &Class) -> bool,
    ) -> bool {
        self.on_any_resolved_context_type(i_s, matcher, &mut |matcher, t| match t {
            DbType::Class(c) => callable(matcher, &c.class(i_s.db)),
            _ => false,
        })
    }

    pub fn on_any_typed_dict(
        &self,
        i_s: &InferenceState,
        matcher: &mut Matcher,
        callable: &mut impl FnMut(&mut Matcher, Rc<TypedDict>) -> bool,
    ) -> bool {
        self.on_any_resolved_context_type(i_s, matcher, &mut |matcher, t| match t {
            DbType::TypedDict(td) => callable(matcher, td.clone()),
            _ => false,
        })
    }

    pub fn check_duplicate_base_class(&self, db: &Database, other: &Self) -> Option<Box<str>> {
        match (self.as_ref(), other.as_ref()) {
            (DbType::Class(c1), DbType::Class(c2)) => {
                (c1.link == c2.link).then(|| Box::from(c1.class(db).name()))
            }
            (DbType::Type(_), DbType::Type(_)) => Some(Box::from("type")),
            (DbType::Tuple(_), DbType::Tuple(_)) => Some(Box::from("tuple")),
            (DbType::Callable(_), DbType::Callable(_)) => Some(Box::from("callable")),
            (DbType::TypedDict(td1), DbType::TypedDict(td2))
                if td1.defined_at == td2.defined_at =>
            {
                Some(td1.name_or_fallback(&FormatData::new_short(db)).into())
            }
            _ => None,
        }
    }

    pub fn merge_matching_parts(self, db: &Database, other: Self) -> Self {
        // TODO performance there's a lot of into_db_type here, that should not really be
        /*
        if self.as_ref() == other.as_ref() {
            return self;
        }
        */
        // necessary.
        let merge_generics = |g1: ClassGenerics, g2: ClassGenerics| {
            if matches!(g1, ClassGenerics::None) {
                return ClassGenerics::None;
            }
            ClassGenerics::List(GenericsList::new_generics(
                // Performance issue: clone could probably be removed. Rc -> Vec check
                // https://github.com/rust-lang/rust/issues/93610#issuecomment-1528108612
                Generics::from_class_generics(db, &g1)
                    .iter(db)
                    .zip(Generics::from_class_generics(db, &g2).iter(db))
                    .map(|(gi1, gi2)| gi1.merge_matching_parts(db, gi2))
                    .collect(),
            ))
        };
        use TupleTypeArguments::*;
        Type::owned(match self.into_db_type() {
            DbType::Class(c1) => match other.into_db_type() {
                DbType::Class(c2) if c1.link == c2.link => {
                    DbType::new_class(c1.link, merge_generics(c1.generics, c2.generics))
                }
                _ => DbType::Any,
            },
            DbType::Union(u1) => match other.into_db_type() {
                DbType::Union(u2) if u1.iter().all(|x| u2.iter().any(|y| x == y)) => {
                    DbType::Union(u1)
                }
                _ => DbType::Any,
            },
            DbType::Tuple(c1) => match other.into_db_type() {
                DbType::Tuple(c2) => {
                    let c1 = rc_unwrap_or_clone(c1);
                    let c2 = rc_unwrap_or_clone(c2);
                    DbType::Tuple(match (c1.args, c2.args) {
                        (FixedLength(ts1), FixedLength(ts2)) if ts1.len() == ts2.len() => {
                            Rc::new(TupleContent::new_fixed_length(
                                // Performance issue: Same as above
                                ts1.iter()
                                    .zip(ts2.iter())
                                    .map(|(t1, t2)| match (t1, t2) {
                                        (
                                            TypeOrTypeVarTuple::Type(t1),
                                            TypeOrTypeVarTuple::Type(t2),
                                        ) => TypeOrTypeVarTuple::Type(
                                            Type::new(t1)
                                                .merge_matching_parts(db, Type::new(t2))
                                                .into_db_type(),
                                        ),
                                        (t1, t2) => match t1 == t2 {
                                            true => t1.clone(),
                                            false => todo!(),
                                        },
                                    })
                                    .collect(),
                            ))
                        }
                        (ArbitraryLength(t1), ArbitraryLength(t2)) => {
                            Rc::new(TupleContent::new_arbitrary_length(
                                Type::owned(*t1)
                                    .merge_matching_parts(db, t2.as_ref().into())
                                    .into_db_type(),
                            ))
                        }
                        _ => TupleContent::new_empty(),
                    })
                }
                _ => DbType::Any,
            },
            DbType::Callable(content1) => match other.into_db_type() {
                DbType::Callable(content2) => {
                    DbType::Callable(db.python_state.any_callable.clone())
                }
                _ => DbType::Any,
            },
            _ => DbType::Any,
        })
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
        (tup1_args @ FixedLength(ts1), tup2_args @ ArbitraryLength(t2), _) => Match::new_false(),
        (ArbitraryLength(t1), FixedLength(ts2), Variance::Invariant) => {
            todo!()
        }
        (ArbitraryLength(t1), FixedLength(ts2), _) => {
            let t1 = Type::new(t1);
            ts2.iter()
                .all(|g2| match g2 {
                    TypeOrTypeVarTuple::Type(t2) => {
                        t1.matches(i_s, matcher, &Type::new(t2), variance).bool()
                    }
                    TypeOrTypeVarTuple::TypeVarTuple(_) => {
                        todo!()
                    }
                })
                .into()
        }
    }
}

impl TypeAlias {
    pub fn as_db_type_and_set_type_vars_any(&self, db: &Database) -> DbType {
        if self.is_recursive() {
            return DbType::RecursiveAlias(Rc::new(RecursiveAlias::new(
                self.location,
                (!self.type_vars.is_empty()).then(|| {
                    GenericsList::new_generics(
                        self.type_vars
                            .iter()
                            .map(|tv| tv.as_any_generic_item())
                            .collect(),
                    )
                }),
            )));
        }
        let db_type = self.db_type_if_valid();
        if self.type_vars.is_empty() {
            db_type.clone()
        } else {
            Type::new(db_type).replace_type_var_likes(db, &mut |t| match t.in_definition()
                == self.location
            {
                true => t.as_type_var_like().as_any_generic_item(),
                false => t.into_generic_item(),
            })
        }
    }

    pub fn replace_type_var_likes(
        &self,
        db: &Database,
        remove_recursive_wrapper: bool,
        callable: &mut impl FnMut(TypeVarLikeUsage) -> GenericItem,
    ) -> Cow<DbType> {
        if self.is_recursive() && !remove_recursive_wrapper {
            return Cow::Owned(DbType::RecursiveAlias(Rc::new(RecursiveAlias::new(
                self.location,
                (!self.type_vars.is_empty()).then(|| {
                    GenericsList::new_generics(
                        self.type_vars
                            .iter()
                            .enumerate()
                            .map(|(i, type_var_like)| match type_var_like {
                                TypeVarLike::TypeVar(type_var) => {
                                    callable(TypeVarLikeUsage::TypeVar(Cow::Owned(TypeVarUsage {
                                        type_var: type_var.clone(),
                                        index: i.into(),
                                        in_definition: self.location,
                                    })))
                                }
                                TypeVarLike::TypeVarTuple(t) => callable(
                                    TypeVarLikeUsage::TypeVarTuple(Cow::Owned(TypeVarTupleUsage {
                                        type_var_tuple: t.clone(),
                                        index: i.into(),
                                        in_definition: self.location,
                                    })),
                                ),
                                TypeVarLike::ParamSpec(p) => callable(TypeVarLikeUsage::ParamSpec(
                                    Cow::Owned(ParamSpecUsage {
                                        param_spec: p.clone(),
                                        index: i.into(),
                                        in_definition: self.location,
                                    }),
                                )),
                            })
                            .collect(),
                    )
                }),
            ))));
        }
        let db_type = self.db_type_if_valid();
        if self.type_vars.is_empty() {
            Cow::Borrowed(db_type)
        } else {
            Cow::Owned(Type::new(db_type).replace_type_var_likes(db, callable))
        }
    }
}

impl GenericItem {
    pub fn replace_type_var_likes(
        &self,
        db: &Database,
        callable: &mut impl FnMut(TypeVarLikeUsage) -> GenericItem,
        replace_self: ReplaceSelf,
    ) -> Self {
        match self {
            Self::TypeArgument(t) => Self::TypeArgument(
                Type::new(t).replace_type_var_likes_and_self(db, callable, replace_self),
            ),
            Self::TypeArguments(_) => todo!(),
            Self::ParamSpecArgument(_) => todo!(),
        }
    }
}

impl RecursiveAlias {
    pub fn calculated_db_type<'db: 'slf, 'slf>(&'slf self, db: &'db Database) -> &'slf DbType {
        let alias = self.type_alias(db);
        if self.generics.is_none() {
            alias.db_type_if_valid()
        } else {
            self.calculated_db_type.get_or_init(|| {
                self.type_alias(db)
                    .replace_type_var_likes(db, true, &mut |t| {
                        self.generics
                            .as_ref()
                            .map(|g| g.nth(t.index()).unwrap().clone())
                            .unwrap()
                    })
                    .into_owned()
            })
        }
    }
}

pub enum CallableLike {
    Callable(Rc<CallableContent>),
    Overload(Rc<FunctionOverload>),
}

impl CallableLike {
    pub fn format(self, format_data: &FormatData) -> String {
        match self {
            Self::Callable(c) => c.format(format_data),
            Self::Overload(overload) => format!(
                "Overload({})",
                join_with_commas(overload.iter_functions().map(|c| c.format(format_data)))
            ),
        }
    }
}
