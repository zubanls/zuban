use std::borrow::Cow;
use std::rc::Rc;

use parsa_python_ast::ParamKind;

use super::params::has_overlapping_params;
use super::{
    calculate_callable_type_vars_and_return, matches_params, maybe_class_usage,
    CalculatedTypeArguments, FormatData, Generics, IteratorContent, LookupResult, Match, Matcher,
    MismatchReason, OnLookupError, OnTypeError, ResultContext,
};
use crate::arguments::Arguments;
use crate::database::{
    CallableContent, CallableParam, CallableParams, ClassGenerics, ComplexPoint, Database,
    Dataclass, DbType, DoubleStarredParamSpecific, EnumMember, FunctionOverload, GenericClass,
    GenericItem, GenericsList, Literal, MetaclassState, NamedTuple, ParamSpecArgument,
    ParamSpecTypeVars, ParamSpecUsage, ParamSpecific, PointLink, RecursiveAlias,
    StarredParamSpecific, TupleContent, TupleTypeArguments, TypeAlias, TypeArguments,
    TypeOrTypeVarTuple, TypeVarKind, TypeVarLike, TypeVarLikeUsage, TypeVarLikes, TypeVarManager,
    TypeVarTupleUsage, TypeVarUsage, TypedDict, TypedDictGenerics, UnionEntry, UnionType, Variance,
};
use crate::debug;
use crate::diagnostics::IssueType;
use crate::getitem::SliceType;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::node_ref::NodeRef;
use crate::type_helpers::{
    lookup_in_namespace, lookup_on_enum_class, lookup_on_enum_instance,
    lookup_on_enum_member_instance, Callable, Class, DataclassHelper, Instance, Module,
    MroIterator, NamedTupleValue, OverloadedFunction, Tuple, TypeOrClass, TypedDictHelper,
};
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

    pub fn simplified_union(self, i_s: &InferenceState, other: Self) -> DbType {
        // Check out how mypy does it:
        // https://github.com/python/mypy/blob/ff81a1c7abc91d9984fc73b9f2b9eab198001c8e/mypy/typeops.py#L413-L486
        let highest_union_format_index = self
            .highest_union_format_index()
            .max(other.highest_union_format_index());
        simplified_union_from_iterators(
            i_s,
            [(0, self.into_db_type()), (1, other.into_db_type())].into_iter(),
            highest_union_format_index,
            false,
        )
    }

    #[inline]
    pub fn maybe_class(&self, db: &'a Database) -> Option<Class<'_>> {
        match self.as_ref() {
            DbType::Class(c) => Some(c.class(db)),
            _ => None,
        }
    }

    #[inline]
    pub fn maybe_type_of_class(&self, db: &'a Database) -> Option<Class<'_>> {
        if let DbType::Type(t) = self.as_ref() {
            if let DbType::Class(c) = t.as_ref() {
                return Some(c.class(db));
            }
        }
        None
    }

    pub fn maybe_typed_dict(&self, db: &'a Database) -> Option<Rc<TypedDict>> {
        match self.as_ref() {
            DbType::TypedDict(td) => Some(td.clone()),
            _ => None,
        }
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

    pub fn is_func_or_overload(&self) -> bool {
        matches!(
            self.as_ref(),
            DbType::Callable(_) | DbType::FunctionOverload(_)
        )
    }

    pub fn maybe_callable(&self, i_s: &InferenceState) -> Option<CallableLike> {
        match self.as_ref() {
            DbType::Callable(c) => Some(CallableLike::Callable(c.clone())),
            DbType::Type(t) => match t.as_ref() {
                DbType::Class(c) => {
                    let cls = c.class(i_s.db);
                    return cls.find_relevant_constructor(i_s).maybe_callable(i_s, cls);
                }
                DbType::Dataclass(d) => {
                    let cls = d.class(i_s.db);
                    if d.options.init {
                        let mut init = Dataclass::__init__(d, i_s.db).clone();
                        if d.class.generics != ClassGenerics::NotDefinedYet
                            || cls.use_cached_type_vars(i_s.db).is_empty()
                        {
                            init.result_type = t.as_ref().clone();
                        } else {
                            let mut type_var_dataclass = (**d).clone();
                            type_var_dataclass.class =
                                Class::with_self_generics(i_s.db, cls.node_ref)
                                    .as_generic_class(i_s.db);
                            init.result_type = DbType::Dataclass(Rc::new(type_var_dataclass));
                        }
                        return Some(CallableLike::Callable(Rc::new(init)));
                    }
                    return cls.find_relevant_constructor(i_s).maybe_callable(i_s, cls);
                }
                DbType::TypedDict(_) => {
                    todo!("Once this is implemented remove the reveal_type formatting")
                }
                DbType::NamedTuple(nt) => {
                    let mut callable = nt.__new__.remove_first_param().unwrap();
                    callable.result_type = (**t).clone();
                    return Some(CallableLike::Callable(Rc::new(callable)));
                }
                _ => {
                    /*
                    if matches!(&c1.params, CallableParams::Any) {
                        Type::new(&c1.result_type).is_super_type_of(
                            i_s,
                            matcher,
                            &Type::new(t2.as_ref()),
                        )
                    } else {
                        None
                    }
                    */
                    None
                }
            },
            DbType::Any => Some(CallableLike::Callable(
                i_s.db.python_state.any_callable.clone(),
            )),
            DbType::Class(c) => {
                let cls = c.class(i_s.db);
                debug!("TODO this from is completely wrong and should never be used.");
                let hack = cls.node_ref;
                Instance::new(cls, None)
                    .type_lookup(i_s, hack, "__call__")
                    .into_maybe_inferred()
                    .and_then(|i| i.as_type(i_s).maybe_callable(i_s))
            }
            DbType::FunctionOverload(overload) => Some(CallableLike::Overload(overload.clone())),
            _ => None,
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

    pub fn mro<'db: 'x, 'x>(&'x self, db: &'db Database) -> MroIterator<'db, '_> {
        match self.as_ref() {
            DbType::Class(c) => c.class(db).mro(db),
            DbType::Tuple(tup) => {
                let tuple_class = db.python_state.tuple_class(db, tup);
                MroIterator::new(
                    db,
                    TypeOrClass::Type(Type::new(self)),
                    tuple_class.generics,
                    tuple_class.use_cached_class_infos(db).mro.iter(),
                    false,
                )
            }
            // TODO? DbType::Dataclass(d) => Some(d.class(db).mro(db)),
            DbType::TypedDict(td) => MroIterator::new(
                db,
                TypeOrClass::Type(self.clone()),
                Generics::None,
                db.python_state.typing_typed_dict_bases.iter(),
                false,
            ),
            DbType::Enum(e) | DbType::EnumMember(EnumMember { enum_: e, .. }) => {
                let class = e.class(db);
                MroIterator::new(
                    db,
                    TypeOrClass::Type(self.clone()),
                    class.generics,
                    class.use_cached_class_infos(db).mro.iter(),
                    false,
                )
            }
            _ => MroIterator::new(
                db,
                TypeOrClass::Type(self.clone()),
                Generics::None,
                [].iter(),
                false,
            ),
        }
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
                Type::new(t1).overlaps(i_s, &Type::new(t2))
            }
            (Some(ArbitraryLength(t1)), Some(FixedLength(ts2))) => {
                let t1 = Type::new(t1);
                ts2.iter().all(|t2| match t2 {
                    TypeOrTypeVarTuple::Type(t2) => t1.overlaps(i_s, &Type::new(t2)),
                    TypeOrTypeVarTuple::TypeVarTuple(t2) => {
                        todo!()
                    }
                })
            }
            (Some(FixedLength(ts1)), Some(ArbitraryLength(t2))) => {
                let t2 = Type::new(t2);
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

    pub fn try_to_resemble_context(
        self,
        i_s: &InferenceState,
        matcher: &mut Matcher,
        t: &Self,
    ) -> DbType {
        use TupleTypeArguments::*;
        match t.as_ref() {
            DbType::Class(c) => {
                let class = c.class(i_s.db);
                for (_, type_or_class) in self.mro(i_s.db) {
                    match type_or_class {
                        TypeOrClass::Class(value_class) => {
                            if Self::matches_class(
                                i_s,
                                &mut Matcher::default(),
                                &class,
                                &value_class,
                                Variance::Covariant,
                            )
                            .bool()
                            {
                                return value_class.as_db_type(i_s.db);
                            }
                        }
                        TypeOrClass::Type(value_type) => {
                            if Self::matches_class_against_type(
                                i_s,
                                &mut Matcher::default(),
                                &class,
                                &value_type,
                                Variance::Covariant,
                            )
                            .bool()
                            {
                                return value_type.into_db_type();
                            }
                        }
                    }
                }
            }
            DbType::Tuple(t1) => {
                if let DbType::Tuple(t2) = self.as_ref() {
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
                                Type::new(t1).try_to_resemble_context(i_s, matcher, &Type::new(t2)),
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
                    let t =
                        Type::owned(matcher.replace_type_var_likes_for_nested_context(i_s.db, t));
                    return self.try_to_resemble_context(i_s, &mut Matcher::default(), &t);
                }
            }
            DbType::Type(t1) => todo!(),
            DbType::Union(union) => {
                if self.is_union_like() {
                    debug!("TODO we should try to resemble unions");
                } else {
                    let mut same_index = None;
                    for (i, union_item) in union.iter().enumerate() {
                        if self.is_simple_same_type(i_s, &Type::new(union_item)).bool() {
                            same_index = Some(i);
                            break;
                        }
                    }
                    // If no union entry matches, we do not want to return the full context type.
                    if let Some(same_index) = same_index {
                        return DbType::Union(UnionType {
                            entries: union
                                .entries
                                .iter()
                                .enumerate()
                                .map(|(i, entry)| UnionEntry {
                                    type_: {
                                        if i == same_index {
                                            self.as_db_type()
                                        } else {
                                            entry.type_.clone()
                                        }
                                    },
                                    format_index: entry.format_index,
                                })
                                .collect(),
                            format_as_optional: union.format_as_optional,
                        });
                    }
                }
            }
            _ => (),
        }
        self.into_db_type()
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
            DbType::Tuple(content) => DbType::Tuple(match &content.args {
                Some(args) => Rc::new(TupleContent::new(replace_tuple_likes(
                    args,
                    callable,
                    replace_self,
                ))),
                None => TupleContent::new_empty(),
            }),
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
                Some(TupleTypeArguments::FixedLength(ts)) => {
                    Rc::new(TupleContent::new_fixed_length(
                        ts.iter()
                            .map(|g| match g {
                                TypeOrTypeVarTuple::Type(t) => TypeOrTypeVarTuple::Type(
                                    Type::new(t).rewrite_late_bound_callables(manager),
                                ),
                                TypeOrTypeVarTuple::TypeVarTuple(t) => {
                                    TypeOrTypeVarTuple::TypeVarTuple(
                                        manager.remap_type_var_tuple(t),
                                    )
                                }
                            })
                            .collect(),
                    ))
                }
                Some(TupleTypeArguments::ArbitraryLength(t)) => {
                    Rc::new(TupleContent::new_arbitrary_length(
                        Type::new(t).rewrite_late_bound_callables(manager),
                    ))
                }
                None => TupleContent::new_empty(),
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

    pub fn execute<'db>(
        &self,
        i_s: &InferenceState<'db, '_>,
        inferred_from: Option<&Inferred>,
        args: &dyn Arguments<'db>,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError<'db, '_>,
    ) -> Inferred {
        match self.as_ref() {
            DbType::Class(c) => {
                let cls = c.class(i_s.db);
                Instance::new(cls, inferred_from).execute(i_s, args, result_context, on_type_error)
            }
            DbType::Type(cls) => {
                execute_type_of_type(i_s, args, result_context, on_type_error, cls.as_ref())
            }
            DbType::Union(union) => Inferred::gather_simplified_union(i_s, |gather| {
                for entry in union.iter() {
                    gather(Type::new(entry).execute(i_s, None, args, result_context, on_type_error))
                }
            }),
            DbType::Callable(content) => {
                Callable::new(content, None).execute(i_s, args, on_type_error, result_context)
            }
            DbType::FunctionOverload(overload) => OverloadedFunction::new(overload, None).execute(
                i_s,
                args,
                result_context,
                on_type_error,
            ),
            DbType::TypeVar(tv) => match &tv.type_var.kind {
                TypeVarKind::Bound(bound) => {
                    Type::new(bound).execute(i_s, None, args, result_context, on_type_error)
                }
                _ => todo!(),
            },
            DbType::Any | DbType::Never => {
                args.iter().calculate_diagnostics(i_s);
                Inferred::new_any()
            }
            DbType::CustomBehavior(custom) => {
                custom.execute(i_s, args, result_context, on_type_error)
            }
            _ => {
                let t = self
                    .as_db_type()
                    .avoid_implicit_literal(i_s.db)
                    .format_short(i_s.db);
                args.as_node_ref().add_issue(
                    i_s,
                    IssueType::NotCallable {
                        type_: format!("\"{}\"", t).into(),
                    },
                );
                Inferred::new_unknown()
            }
        }
    }

    pub fn iter(&self, i_s: &InferenceState, from: NodeRef) -> IteratorContent {
        let on_error = |t: &DbType| {
            let t = t.format_short(i_s.db);
            from.add_issue(
                i_s,
                IssueType::NotIterable {
                    type_: format!("\"{}\"", t).into(),
                },
            );
            IteratorContent::Any
        };
        match self.as_ref() {
            DbType::Class(c) => Instance::new(c.class(i_s.db), None).iter(i_s, from),
            DbType::Tuple(content) => Tuple::new(content).iter(i_s, from),
            DbType::NamedTuple(nt) => NamedTupleValue::new(i_s.db, nt).iter(i_s, from),
            DbType::Any | DbType::Never => IteratorContent::Any,
            DbType::Union(union) => {
                let mut items = vec![];
                for t in union.iter() {
                    items.push(Type::new(t).iter(i_s, from));
                }
                IteratorContent::Union(items)
            }
            DbType::TypeVar(tv) => match &tv.type_var.kind {
                TypeVarKind::Bound(bound) => Type::new(bound).iter(i_s, from),
                TypeVarKind::Constraints(_) => todo!(),
                TypeVarKind::Unrestricted => on_error(self),
            },
            DbType::NewType(n) => Type::new(n.type_(i_s)).iter(i_s, from),
            DbType::Self_ => Instance::new(*i_s.current_class().unwrap(), None).iter(i_s, from),
            DbType::Type(t) => iter_on_type(i_s, t, from, &on_error),
            _ => on_error(self),
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

    pub fn common_base_type(&self, i_s: &InferenceState, other: &Self) -> DbType {
        let is_same_literal = |literal1: &Literal, t: &_| match t {
            DbType::Literal(literal2) => literal1.value(i_s.db) == literal2.value(i_s.db),
            _ => false,
        };
        let check_both_sides = |t1: &_, t2: &DbType| match t1 {
            DbType::Literal(l) if l.implicit || !is_same_literal(l, t2) => Some(
                i_s.db
                    .python_state
                    .literal_type(&l.kind)
                    .common_base_type(i_s, &Type::new(t2)),
            ),
            /*
            DbType::Union(u) if u.iter().any(|t| matches!(t, DbType::None)) => {
                return self.clone().union(i_s.db, other.clone()).into_db_type()
            }
            */
            DbType::None | DbType::Union(_) => {
                return Some(self.clone().simplified_union(i_s, other.clone()))
            }
            DbType::Any => return Some(DbType::Any),
            _ => None,
        };

        if let Some(new) = check_both_sides(self, other) {
            return new;
        }
        if let Some(new) = check_both_sides(other, self) {
            return new;
        }
        for (_, c1) in self.mro(i_s.db) {
            for (_, c2) in other.mro(i_s.db) {
                match &c1 {
                    TypeOrClass::Type(t1) => {
                        let TypeOrClass::Type(t2) = c2 else {
                            continue
                        };
                        if let Some(base) = common_base_type_for_non_class(i_s, t1, t2.as_ref()) {
                            return base;
                        }
                    }
                    TypeOrClass::Class(c1) => {
                        let TypeOrClass::Class(c2) = c2 else {
                            continue
                        };
                        if let Some(t) = common_base_class(i_s, *c1, c2) {
                            return t;
                        }
                    }
                }
            }
        }
        unreachable!("object is always a common base class")
    }

    pub fn common_sub_type(&self, i_s: &InferenceState, other: &Self) -> Option<DbType> {
        match (self.as_ref(), other.as_ref()) {
            (DbType::Union(union), _) => {
                for t in union.iter() {
                    // TODO what about multiple items?
                    if let Some(found) = Type::new(t).common_sub_type(i_s, other) {
                        return Some(found);
                    }
                }
                None
            }
            (_, DbType::Union(union)) => {
                for t in union.iter() {
                    // TODO what about multiple items?
                    if let Some(found) = Type::new(t).common_sub_type(i_s, self) {
                        return Some(found);
                    }
                }
                None
            }
            (DbType::TypedDict(td1), DbType::TypedDict(td2)) => Some(td1.union(i_s, &td2)),
            (DbType::Callable(c1), DbType::Callable(c2)) => {
                Some(DbType::Callable(common_sub_type_for_callables(i_s, c1, c2)))
            }
            _ => {
                if self.is_simple_sub_type_of(i_s, other).bool() {
                    Some(self.as_db_type())
                } else if other.is_simple_sub_type_of(i_s, self).bool() {
                    Some(other.as_db_type())
                } else {
                    None
                }
            }
        }
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

    #[inline]
    pub fn run_on_each_union_type(&self, callable: &mut impl FnMut(&Type)) {
        match self.as_ref() {
            DbType::Union(union) => {
                for t in union.iter() {
                    Type::new(t).run_on_each_union_type(callable)
                }
            }
            DbType::Never => (),
            _ => callable(self),
        }
    }

    #[inline]
    pub fn run_after_lookup_on_each_union_member(
        &self,
        i_s: &InferenceState,
        from_inferred: Option<&Inferred>,
        from: NodeRef,
        name: &str,
        kind: LookupKind,
        result_context: &mut ResultContext,
        callable: &mut impl FnMut(&Type, LookupResult),
    ) {
        match self.as_ref() {
            DbType::Class(c) => callable(
                self,
                Instance::new(c.class(i_s.db), from_inferred).lookup(i_s, from, name, kind),
            ),
            DbType::Any => callable(self, LookupResult::any()),
            DbType::None => callable(
                self,
                i_s.db
                    .python_state
                    .none_instance()
                    .lookup(i_s, from, name, kind),
            ),
            DbType::Literal(literal) => {
                let instance = i_s.db.python_state.literal_instance(&literal.kind);
                let result = instance.lookup(i_s, from, name, kind);
                if literal.implicit {
                    callable(&i_s.db.python_state.literal_type(&literal.kind), result)
                } else {
                    callable(self, result)
                }
            }
            t @ DbType::TypeVar(usage) => match &usage.type_var.kind {
                TypeVarKind::Bound(bound) => {
                    Type::new(bound).run_after_lookup_on_each_union_member(
                        i_s,
                        None,
                        from,
                        name,
                        kind,
                        result_context,
                        callable,
                    );
                }
                TypeVarKind::Constraints(constraints) => {
                    debug!("TODO type var values");
                    /*
                    for db_type in constraints.iter() {
                        return match db_type {
                            DbType::Class(link) => Instance::new(
                                Class::with_undefined_generics(NodeRef::from_link(i_s.db, *link)),
                                &Inferred::from_type(DbType::Class(*link, None)),
                            )
                            .lookup(i_s, name),
                            _ => todo!("{:?}", db_type),
                        }
                    }
                    */
                    let s = &i_s.db.python_state;
                    // TODO it's kind of stupid that we recreate an instance object here all the time, we
                    // should just use a precreated object() from somewhere.
                    callable(
                        self,
                        Instance::new(s.object_class(), None).lookup(i_s, from, name, kind),
                    )
                }
                TypeVarKind::Unrestricted => {
                    let s = &i_s.db.python_state;
                    // TODO it's kind of stupid that we recreate an instance object here all the time, we
                    // should just use a precreated object() from somewhere.
                    callable(
                        self,
                        Instance::new(s.object_class(), None).lookup(i_s, from, name, kind),
                    )
                }
            },
            DbType::Tuple(tup) => callable(self, Tuple::new(tup).lookup(i_s, from, name)),
            DbType::Union(union) => {
                for t in union.iter() {
                    Type::new(t).run_after_lookup_on_each_union_member(
                        i_s,
                        None,
                        from,
                        name,
                        kind,
                        result_context,
                        callable,
                    )
                }
            }
            DbType::Type(t) => {
                attribute_access_of_type(i_s, from, name, kind, result_context, callable, t.clone())
            }
            DbType::Callable(_) | DbType::FunctionOverload(_) => callable(
                self,
                Instance::new(i_s.db.python_state.function_class(), None)
                    .lookup(i_s, from, name, kind),
            ),
            DbType::Module(file_index) => {
                let module = Module::from_file_index(i_s.db, *file_index);
                callable(self, module.lookup(i_s, from, name))
            }
            DbType::Namespace(namespace) => callable(
                self,
                lookup_in_namespace(i_s.db, from.file_index(), namespace, name),
            ),
            DbType::Self_ => {
                let current_class = i_s.current_class().unwrap();
                let type_var_likes = current_class.type_vars(i_s);
                callable(
                    self,
                    Instance::new(
                        Class::with_self_generics(
                            i_s.db,
                            current_class.node_ref.to_db_lifetime(i_s.db),
                        ),
                        from_inferred,
                    )
                    .lookup(i_s, from, name, kind),
                )
            }
            DbType::Super { class, mro_index } => {
                let instance = Instance::new(class.class(i_s.db), None);
                let result = instance
                    .lookup_and_maybe_ignore_super_count(
                        i_s,
                        from,
                        name,
                        LookupKind::OnlyType,
                        mro_index + 1,
                    )
                    .1;
                if matches!(&result, LookupResult::None) {
                    from.add_issue(i_s, IssueType::UndefinedInSuperclass { name: name.into() });
                    callable(self, LookupResult::UnknownName(Inferred::new_any()));
                    return;
                }
                callable(self, result)
            }
            DbType::Dataclass(d) => callable(self, DataclassHelper(d).lookup(i_s, from, name)),
            DbType::TypedDict(d) => {
                callable(self, TypedDictHelper(d).lookup(i_s, from, name, kind))
            }
            DbType::NamedTuple(nt) => {
                callable(self, NamedTupleValue::new(i_s.db, nt).lookup(i_s, name))
            }
            DbType::Never => (),
            DbType::NewType(new_type) => Type::new(new_type.type_(i_s))
                .run_after_lookup_on_each_union_member(
                    i_s,
                    None,
                    from,
                    name,
                    kind,
                    result_context,
                    callable,
                ),
            DbType::Enum(e) => callable(
                self,
                lookup_on_enum_instance(i_s, from, e, name, result_context),
            ),
            DbType::EnumMember(member) => callable(
                self,
                lookup_on_enum_member_instance(i_s, from, member, name),
            ),
            DbType::RecursiveAlias(r) => Type::new(r.calculated_db_type(i_s.db))
                .run_after_lookup_on_each_union_member(
                    i_s,
                    None,
                    from,
                    name,
                    kind,
                    result_context,
                    callable,
                ),
            _ => todo!("{self:?}"),
        }
    }

    pub fn lookup(
        &self,
        i_s: &InferenceState,
        from: NodeRef,
        name: &str,
        lookup_kind: LookupKind,
        result_context: &mut ResultContext,
        on_lookup_error: OnLookupError,
    ) -> LookupResult {
        let mut result: Option<LookupResult> = None;
        self.run_after_lookup_on_each_union_member(
            i_s,
            None,
            from,
            name,
            lookup_kind,
            result_context,
            &mut |t, lookup_result| {
                if matches!(lookup_result, LookupResult::None) {
                    on_lookup_error(t);
                }
                result = Some(if let Some(l) = result.take() {
                    LookupResult::UnknownName(
                        l.into_inferred()
                            .simplified_union(i_s, lookup_result.into_inferred()),
                    )
                } else {
                    lookup_result
                })
            },
        );
        result.unwrap_or_else(|| todo!())
    }

    pub fn lookup_symbol<'db: 'a>(
        &'a self,
        i_s: &InferenceState<'db, '_>,
        name: &str,
    ) -> (Option<Class<'a>>, LookupResult) {
        match self.as_ref() {
            DbType::Class(c) => todo!(),
            DbType::Dataclass(d) => DataclassHelper(d).lookup_symbol(i_s, name),
            DbType::TypedDict(_) => todo!(),
            DbType::Tuple(t) => (None, LookupResult::None),
            DbType::NamedTuple(nt) => (None, NamedTupleValue::new(i_s.db, nt).lookup(i_s, name)),
            DbType::Callable(t) => todo!(),
            _ => todo!("{name:?} {self:?}"),
        }
    }

    pub fn get_item(
        &self,
        i_s: &InferenceState,
        from_inferred: Option<&Inferred>,
        slice_type: &SliceType,
        result_context: &mut ResultContext,
    ) -> Inferred {
        let inf = match self.as_ref() {
            DbType::Class(c) => Instance::new(c.class(i_s.db), from_inferred).get_item(
                i_s,
                slice_type,
                result_context,
            ),
            DbType::Any => Inferred::new_any(),
            DbType::Tuple(tup) => Tuple::new(tup).get_item(i_s, slice_type, result_context),
            DbType::NamedTuple(nt) => {
                NamedTupleValue::new(i_s.db, nt).get_item(i_s, slice_type, result_context)
            }
            DbType::Union(union) => Inferred::gather_simplified_union(i_s, |callable| {
                for t in union.iter() {
                    callable(Type::new(t).get_item(i_s, None, slice_type, result_context))
                }
            }),
            t @ DbType::TypeVar(tv) => match &tv.type_var.kind {
                TypeVarKind::Bound(bound) => {
                    Type::new(bound).get_item(i_s, None, slice_type, result_context)
                }
                TypeVarKind::Constraints(constraints) => todo!(),
                TypeVarKind::Unrestricted => todo!(),
            },
            DbType::Type(t) => match t.as_ref() {
                DbType::Class(c) => c.class(i_s.db).get_item(i_s, slice_type, result_context),
                DbType::Dataclass(d) => slice_type
                    .file
                    .inference(i_s)
                    .compute_type_application_on_dataclass(d, *slice_type, false),
                t @ DbType::Enum(_) => {
                    let enum_index = slice_type.infer(i_s);
                    if !enum_index
                        .as_type(i_s)
                        .is_simple_sub_type_of(i_s, &Type::owned(i_s.db.python_state.str_db_type()))
                        .bool()
                    {
                        slice_type.as_node_ref().add_issue(
                            i_s,
                            IssueType::EnumIndexShouldBeAString {
                                actual: enum_index.format_short(i_s),
                            },
                        );
                    }
                    Inferred::from_type(t.clone())
                }
                DbType::TypedDict(td) => slice_type
                    .file
                    .inference(i_s)
                    .compute_type_application_on_typed_dict(
                        td,
                        *slice_type,
                        matches!(result_context, ResultContext::AssignmentNewDefinition),
                    ),
                _ => {
                    slice_type
                        .as_node_ref()
                        .add_issue(i_s, IssueType::OnlyClassTypeApplication);
                    Inferred::new_any()
                }
            },
            DbType::NewType(new_type) => {
                Type::new(new_type.type_(i_s)).get_item(i_s, None, slice_type, result_context)
            }
            DbType::RecursiveAlias(r) => Type::new(r.calculated_db_type(i_s.db)).get_item(
                i_s,
                None,
                slice_type,
                result_context,
            ),
            DbType::TypedDict(d) => TypedDictHelper(d).get_item(i_s, slice_type, result_context),
            DbType::Callable(_) => {
                slice_type
                    .as_node_ref()
                    .add_issue(i_s, IssueType::OnlyClassTypeApplication);
                Inferred::new_unknown()
            }
            DbType::FunctionOverload(_) => {
                slice_type
                    .as_node_ref()
                    .add_issue(i_s, IssueType::OnlyClassTypeApplication);
                todo!("Please write a test that checks this");
            }
            DbType::None => {
                debug!("TODO None[...]");
                Inferred::new_any()
            }
            DbType::Literal(l) => i_s.db.python_state.literal_type(&l.kind).get_item(
                i_s,
                None,
                slice_type,
                result_context,
            ),
            _ => todo!("get_item not implemented for {self:?}"),
        };
        // Make sure the slices are inferred
        slice_type.infer(i_s);
        inf
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
                        (Some(FixedLength(ts1)), Some(FixedLength(ts2)))
                            if ts1.len() == ts2.len() =>
                        {
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
                        (Some(ArbitraryLength(t1)), Some(ArbitraryLength(t2))) => {
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

fn iter_on_type(
    i_s: &InferenceState,
    t: &DbType,
    from: NodeRef,
    on_error: &impl Fn(&DbType) -> IteratorContent,
) -> IteratorContent {
    match t {
        DbType::Class(c) => {
            if let Some(result) = c.class(i_s.db).iter(i_s, from) {
                return result;
            }
        }
        DbType::Union(union) => {
            let mut items = vec![];
            for t in union.iter() {
                items.push(iter_on_type(i_s, t, from, on_error));
            }
            return IteratorContent::Union(items);
        }
        DbType::TypeVar(t) => match &t.type_var.kind {
            TypeVarKind::Bound(bound) => return iter_on_type(i_s, bound, from, on_error),
            TypeVarKind::Constraints(constraints) => todo!(),
            TypeVarKind::Unrestricted => (),
        },
        t @ DbType::Enum(_) => return IteratorContent::Inferred(Inferred::from_type(t.clone())),
        _ => (),
    }
    on_error(&DbType::Type(Rc::new(t.clone())))
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
            result = Cow::Owned(Type(result).common_base_type(i_s, &Type::new(t)));
        }
        result.into_owned()
    } else {
        DbType::Never
    }
}

fn common_base_class(i_s: &InferenceState, c1: Class, c2: Class) -> Option<DbType> {
    if c1.node_ref != c2.node_ref {
        return None;
    }
    let mut generics = vec![];
    for ((type_var_like, generic1), generic2) in c1
        .type_vars(i_s)
        .iter()
        .zip(c1.generics().iter(i_s.db))
        .zip(c2.generics().iter(i_s.db))
    {
        match type_var_like {
            TypeVarLike::TypeVar(type_var) => {
                let inner_t1 = generic1.expect_type_argument();
                let inner_t2 = generic2.expect_type_argument();
                match type_var.variance {
                    Variance::Invariant => {
                        let matches = inner_t1.is_simple_same_type(i_s, &inner_t2);
                        // TODO this with_any check is not very precise and a structure
                        // like T[Any, int] & T[int, Any] should become T[Any, Any]
                        match matches {
                            Match::True { with_any: false } => {
                                generics.push(GenericItem::TypeArgument(inner_t1.into_db_type()));
                            }
                            Match::True { with_any: true } => {
                                generics.push(GenericItem::TypeArgument(inner_t2.into_db_type()));
                            }
                            _ => return None,
                        }
                    }
                    Variance::Covariant => {
                        generics.push(GenericItem::TypeArgument(
                            inner_t1.common_base_type(i_s, &inner_t2),
                        ));
                    }
                    Variance::Contravariant => {
                        if let Some(t) = inner_t1.common_sub_type(i_s, &inner_t2) {
                            generics.push(GenericItem::TypeArgument(t));
                        } else {
                            return None;
                        }
                    }
                }
            }
            _ => todo!(),
        }
    }
    Some(DbType::new_class(
        c1.node_ref.as_link(),
        ClassGenerics::List(GenericsList::generics_from_vec(generics)),
    ))
}

fn common_base_type_for_non_class(
    i_s: &InferenceState,
    t1: &DbType,
    t2: &DbType,
) -> Option<DbType> {
    match t1 {
        DbType::Callable(c1) => {
            // TODO this should also be done for function/callable and callable/function and
            // not only callable/callable
            if let DbType::Callable(c2) = t2 {
                return Some(common_base_for_callables(i_s, c1, c2));
            }
        }
        DbType::Tuple(tup1) => return common_base_for_tuple_against_db_type(i_s, tup1, t2),
        DbType::NamedTuple(nt1) => {
            if let DbType::NamedTuple(nt2) = t2 {
                if nt1.__new__.defined_at == nt2.__new__.defined_at {
                    return Some(DbType::NamedTuple(nt1.clone()));
                }
            }
            return common_base_for_tuple_against_db_type(i_s, &nt1.as_tuple(), t2);
        }
        DbType::TypedDict(td1) => {
            if let DbType::TypedDict(td2) = &t2 {
                return Some(DbType::TypedDict(td1.intersection(i_s, td2)));
            }
        }
        DbType::Type(t1) => {
            if let DbType::Type(t2) = t2 {
                return Some(DbType::Type(Rc::new(
                    Type::new(t1).common_base_type(i_s, &Type::new(t2)),
                )));
            }
        }
        _ => {
            if Type::new(t1)
                .is_simple_same_type(i_s, &Type::new(t2))
                .bool()
            {
                return Some(t1.clone());
            }
        }
    }
    None
}

fn common_base_for_callables(
    i_s: &InferenceState,
    c1: &CallableContent,
    c2: &CallableContent,
) -> DbType {
    if c1.kind != c2.kind {
        todo!()
    }
    match &c1.params {
        CallableParams::Simple(params1) => match &c2.params {
            CallableParams::Simple(params2) => {
                if let Some(params) = common_params(i_s, &params1, &params2) {
                    return DbType::Callable(Rc::new(CallableContent {
                        name: None,
                        class_name: None,
                        defined_at: c1.defined_at,
                        kind: c1.kind,
                        type_vars: i_s.db.python_state.empty_type_var_likes.clone(),
                        params,
                        result_type: Type::new(&c1.result_type)
                            .common_base_type(i_s, &Type::new(&c2.result_type)),
                    }));
                }
            }
            CallableParams::WithParamSpec(_, _) => (),
            CallableParams::Any => todo!(),
        },
        CallableParams::WithParamSpec(_, _) => (),
        CallableParams::Any => todo!(),
    }
    i_s.db.python_state.function_db_type()
}

fn common_params(
    i_s: &InferenceState,
    params1: &[CallableParam],
    params2: &[CallableParam],
) -> Option<CallableParams> {
    if params1.len() == params2.len() {
        let mut new_params = vec![];
        for (p1, p2) in params1.iter().zip(params2.iter()) {
            let mut kind = p1.param_specific.param_kind();
            let p2_kind = p2.param_specific.param_kind();
            let p1_name = p1.name.map(|n| n.as_str(i_s.db));
            let p2_name = p2.name.map(|n| n.as_str(i_s.db));
            if p1_name != p2_name {
                if matches!(
                    kind,
                    ParamKind::PositionalOnly | ParamKind::PositionalOrKeyword
                ) && matches!(
                    p2_kind,
                    ParamKind::PositionalOnly | ParamKind::PositionalOrKeyword
                ) {
                    kind = ParamKind::PositionalOnly;
                } else {
                    return None;
                }
            }
            let t1 = p1.param_specific.maybe_positional_db_type()?;
            let t2 = p2.param_specific.maybe_positional_db_type()?;
            let new_t = Type::new(t1).common_sub_type(i_s, &Type::new(t2))?;
            new_params.push(CallableParam {
                param_specific: match &kind {
                    ParamKind::PositionalOnly => ParamSpecific::PositionalOnly(new_t),
                    ParamKind::PositionalOrKeyword => ParamSpecific::PositionalOrKeyword(new_t),
                    ParamKind::KeywordOnly => ParamSpecific::KeywordOnly(new_t),
                    ParamKind::Starred => {
                        ParamSpecific::Starred(StarredParamSpecific::ArbitraryLength(new_t))
                    }
                    ParamKind::DoubleStarred => {
                        ParamSpecific::DoubleStarred(DoubleStarredParamSpecific::ValueType(new_t))
                    }
                },
                name: (p1_name == p2_name).then(|| p1.name).flatten(),
                has_default: p1.has_default & p2.has_default,
            });
        }
        Some(CallableParams::Simple(new_params.into()))
    } else {
        todo!()
    }
}

fn common_base_for_tuple_against_db_type(
    i_s: &InferenceState,
    tup1: &TupleContent,
    t2: &DbType,
) -> Option<DbType> {
    Some(match t2 {
        DbType::Tuple(tup2) => DbType::Tuple(Rc::new(common_base_for_tuples(i_s, tup1, tup2))),
        DbType::NamedTuple(nt2) => {
            DbType::Tuple(Rc::new(common_base_for_tuples(i_s, tup1, &nt2.as_tuple())))
        }
        _ => return None,
    })
}

fn common_base_for_tuples(
    i_s: &InferenceState,
    tup1: &TupleContent,
    tup2: &TupleContent,
) -> TupleContent {
    let Some(tup1_args) = &tup1.args else {
        todo!()
    };
    let Some(tup2_args) = &tup2.args else {
        todo!()
    };
    TupleContent::new(match tup2_args {
        TupleTypeArguments::FixedLength(ts2) => {
            let mut new_args = tup1_args.clone();
            common_base_type_of_type_var_tuple_with_items(
                &mut new_args,
                i_s,
                ts2.len(),
                ts2.iter(),
            );
            new_args
        }
        TupleTypeArguments::ArbitraryLength(t2) => match tup1_args {
            TupleTypeArguments::FixedLength(ts1) => {
                let mut new_args = tup2_args.clone();
                common_base_type_of_type_var_tuple_with_items(
                    &mut new_args,
                    i_s,
                    ts1.len(),
                    ts1.iter(),
                );
                new_args
            }
            TupleTypeArguments::ArbitraryLength(t1) => todo!(),
        },
    })
}

pub fn common_base_type_of_type_var_tuple_with_items<
    'x,
    I: Iterator<Item = &'x TypeOrTypeVarTuple>,
>(
    args: &mut TupleTypeArguments,
    i_s: &InferenceState,
    length: usize,
    items: I,
) {
    match args {
        TupleTypeArguments::FixedLength(calc_ts) => {
            if length == calc_ts.len() {
                let mut new = vec![];
                for (t1, t2) in calc_ts.iter().zip(items) {
                    match (t1, t2) {
                        (TypeOrTypeVarTuple::Type(t1), TypeOrTypeVarTuple::Type(t2)) => {
                            new.push(TypeOrTypeVarTuple::Type(
                                Type::new(t1).common_base_type(i_s, &Type::new(t2)),
                            ));
                        }
                        _ => todo!(),
                    }
                }
                *calc_ts = new.into();
            } else {
                // We use map to make an iterator with covariant lifetimes.
                #[allow(clippy::map_identity)]
                let t = common_base_type(i_s, calc_ts.iter().chain(items.map(|x| x)));
                *args = TupleTypeArguments::ArbitraryLength(Box::new(t));
            }
        }
        TupleTypeArguments::ArbitraryLength(calc_t) => {
            let base = common_base_type(i_s, items);
            debug!("TODO Type var tuple merging");
        }
    }
}

fn common_sub_type_for_callables(
    i_s: &InferenceState,
    c1: &CallableContent,
    c2: &CallableContent,
) -> Rc<CallableContent> {
    if c1.kind != c2.kind {
        todo!()
    }
    match &c1.params {
        CallableParams::Simple(params1) => match &c2.params {
            CallableParams::Simple(params2) => {
                if let Some(params) = common_sub_type_params(i_s, &params1, &params2) {
                    if let Some(result_type) =
                        Type::new(&c1.result_type).common_sub_type(i_s, &Type::new(&c2.result_type))
                    {
                        return Rc::new(CallableContent {
                            name: None,
                            class_name: None,
                            defined_at: c1.defined_at,
                            kind: c1.kind,
                            type_vars: i_s.db.python_state.empty_type_var_likes.clone(),
                            params,
                            result_type,
                        });
                    }
                }
            }
            CallableParams::WithParamSpec(_, _) => todo!(),
            CallableParams::Any => todo!(),
        },
        CallableParams::WithParamSpec(_, _) => todo!(),
        CallableParams::Any => todo!(),
    }
    Rc::new(CallableContent::new_any(
        i_s.db.python_state.empty_type_var_likes.clone(),
    ))
    //return i_s.db.python_state.function_db_type();
}

fn common_sub_type_params(
    i_s: &InferenceState,
    params1: &[CallableParam],
    params2: &[CallableParam],
) -> Option<CallableParams> {
    if params1.len() == params2.len() {
        let mut new_params = vec![];
        for (p1, p2) in params1.iter().zip(params2.iter()) {
            if p1.name != p2.name || p1.has_default != p2.has_default {
                return None;
            }
            if p1.param_specific.param_kind() != p2.param_specific.param_kind() {
                return None;
            }
            let t1 = p1.param_specific.maybe_positional_db_type()?;
            let t2 = p2.param_specific.maybe_positional_db_type()?;
            let new_t = Type::new(t1).common_base_type(i_s, &Type::new(t2));
            new_params.push(CallableParam {
                param_specific: match &p1.param_specific.param_kind() {
                    ParamKind::PositionalOnly => ParamSpecific::PositionalOnly(new_t),
                    ParamKind::PositionalOrKeyword => ParamSpecific::PositionalOrKeyword(new_t),
                    ParamKind::KeywordOnly => ParamSpecific::KeywordOnly(new_t),
                    ParamKind::Starred => {
                        ParamSpecific::Starred(StarredParamSpecific::ArbitraryLength(new_t))
                    }
                    ParamKind::DoubleStarred => {
                        ParamSpecific::DoubleStarred(DoubleStarredParamSpecific::ValueType(new_t))
                    }
                },
                name: p1.name,
                has_default: p1.has_default,
            });
        }
        Some(CallableParams::Simple(new_params.into()))
    } else {
        todo!()
    }
}

pub fn simplified_union_from_iterators(
    i_s: &InferenceState,
    types: impl Iterator<Item = (usize, DbType)>,
    // We need this to make sure that the unions within the iterator can be properly ordered.
    highest_union_format_index: usize,
    format_as_optional: bool,
) -> DbType {
    let multiply = highest_union_format_index + 1;
    let mut result = merge_simplified_union_type(
        i_s,
        types.into_iter().flat_map(|(format_index, t)| {
            t.into_iter_with_unpacked_unions()
                .map(move |entry| UnionEntry {
                    format_index: format_index * multiply + entry.format_index,
                    type_: entry.type_,
                })
        }),
        format_as_optional,
    );
    loop {
        match result {
            MergeSimplifiedUnionResult::Done(t) => return t,
            MergeSimplifiedUnionResult::NotDone(items) => {
                result = merge_simplified_union_type(i_s, items.into_iter(), format_as_optional)
            }
        }
    }
}

enum MergeSimplifiedUnionResult {
    NotDone(Vec<UnionEntry>),
    Done(DbType),
}

fn merge_simplified_union_type(
    i_s: &InferenceState,
    types: impl Iterator<Item = UnionEntry>,
    format_as_optional: bool,
) -> MergeSimplifiedUnionResult {
    let mut new_types: Vec<UnionEntry> = vec![];
    let mut finished = true;
    'outer: for additional in types {
        if additional.type_.has_any(i_s) {
            if !new_types
                .iter()
                .any(|entry| entry.type_ == additional.type_)
            {
                new_types.push(additional)
            }
            continue;
        }
        match &additional.type_ {
            DbType::RecursiveAlias(r1) if r1.generics.is_some() => {
                // Recursive aliases need special handling, because the normal subtype
                // checking will call this function again if generics are available to
                // cache the type. In that case we just avoid complex matching and use
                // a simple heuristic. This won't affect correctness, it might just
                // display a bigger union than necessary.
                for entry in new_types.iter() {
                    if let DbType::RecursiveAlias(r2) = &entry.type_ {
                        if r1 == r2 {
                            continue 'outer;
                        }
                    }
                }
            }
            _ => {
                for (i, current) in new_types.iter().enumerate() {
                    if current.type_.has_any(i_s) {
                        continue;
                    }
                    match &current.type_ {
                        DbType::RecursiveAlias(r) if r.generics.is_some() => (),
                        t => {
                            if Type::new(&additional.type_)
                                .is_super_type_of(
                                    i_s,
                                    &mut Matcher::with_ignored_promotions(),
                                    &Type::new(t),
                                )
                                .bool()
                            {
                                new_types[i].type_ = additional.type_;
                                finished = false;
                                continue 'outer;
                            }
                            if Type::new(t)
                                .is_super_type_of(
                                    i_s,
                                    &mut Matcher::with_ignored_promotions(),
                                    &Type::new(&additional.type_),
                                )
                                .bool()
                            {
                                finished = false;
                                continue 'outer;
                            }
                        }
                    }
                }
            }
        }
        new_types.push(additional);
    }
    if finished {
        MergeSimplifiedUnionResult::Done(match new_types.len() {
            0 => DbType::Never,
            1 => new_types.into_iter().next().unwrap().type_,
            _ => {
                let mut union = UnionType {
                    format_as_optional,
                    entries: new_types.into(),
                };
                union.sort_for_priority();
                DbType::Union(union)
            }
        })
    } else {
        MergeSimplifiedUnionResult::NotDone(new_types)
    }
}

pub fn attribute_access_of_type(
    i_s: &InferenceState,
    from: NodeRef,
    name: &str,
    kind: LookupKind,
    result_context: &mut ResultContext,
    callable: &mut impl FnMut(&Type, LookupResult),
    in_type: Rc<DbType>,
) {
    let lookup_result = match in_type.as_ref() {
        DbType::Union(union) => {
            debug_assert!(union.entries.len() > 1);
            for t in union.iter() {
                attribute_access_of_type(
                    i_s,
                    from,
                    name,
                    kind,
                    result_context,
                    callable,
                    Rc::new(t.clone()),
                )
            }
            return;
        }
        DbType::TypeVar(t) => {
            match &t.type_var.kind {
                TypeVarKind::Bound(bound) => attribute_access_of_type(
                    i_s,
                    from,
                    name,
                    kind,
                    result_context,
                    callable,
                    Rc::new(bound.clone()),
                ),
                TypeVarKind::Constraints(_) => todo!(),
                TypeVarKind::Unrestricted => todo!(),
            }
            return;
        }
        DbType::Class(g) => g.class(i_s.db).lookup(i_s, from, name, kind),
        DbType::Literal(l) => i_s
            .db
            .python_state
            .literal_instance(&l.kind)
            .class
            .lookup(i_s, from, name, kind),
        DbType::Callable(_) => LookupResult::None,
        DbType::Self_ => i_s.current_class().unwrap().lookup(i_s, from, name, kind),
        DbType::Any => i_s
            .db
            .python_state
            .bare_type_class()
            .instance()
            .lookup(i_s, from, name, kind)
            .or_else(|| LookupResult::any()),
        t @ DbType::Enum(e) => lookup_on_enum_class(i_s, from, e, name, result_context),
        DbType::Dataclass(d) => DataclassHelper(d).lookup_on_type(i_s, from, name, kind),
        DbType::TypedDict(d) => i_s
            .db
            .python_state
            .typed_dict_class()
            .lookup(i_s, from, name, kind),
        DbType::NamedTuple(nt) => match name {
            "__new__" => {
                LookupResult::UnknownName(Inferred::from_type(DbType::Callable(nt.__new__.clone())))
            }
            _ => todo!(),
        },
        DbType::Tuple(tup) => i_s
            .db
            .python_state
            .tuple_class(i_s.db, tup)
            .lookup(i_s, from, name, kind),
        DbType::Type(_) => i_s
            .db
            .python_state
            .bare_type_class()
            .lookup(i_s, from, name, kind),
        t => todo!("{name} on {t:?}"),
    };
    callable(&Type::owned(DbType::Type(in_type.clone())), lookup_result)
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
            return Inferred::from_type(tuple.clone());
            // TODO reenable this
            let mut args_iterator = args.iter();
            let (arg, inferred_tup) = if let Some(arg) = args_iterator.next() {
                let inf = arg.infer(i_s, &mut ResultContext::Known(tuple));
                (arg, inf)
            } else {
                debug!("TODO this does not check the arguments");
                return Inferred::from_type(tuple.clone());
            };
            if args_iterator.next().is_some() {
                todo!()
            }
            Type::new(tuple).error_if_not_matches(i_s, &inferred_tup, |t1, t2| {
                (on_type_error.callback)(i_s, &|_| todo!(), &arg, t1, t2);
                args.as_node_ref().to_db_lifetime(i_s.db)
            });
            Inferred::from_type(tuple.clone())
        }
        DbType::Class(c) => c
            .class(i_s.db)
            .execute(i_s, args, result_context, on_type_error),
        DbType::TypeVar(t) => match &t.type_var.kind {
            TypeVarKind::Bound(bound) => {
                execute_type_of_type(i_s, args, result_context, on_type_error, bound);
                Inferred::from_type(type_.clone())
            }
            TypeVarKind::Constraints(constraints) => todo!(),
            TypeVarKind::Unrestricted => todo!(),
        },
        DbType::NewType(n) => {
            let mut iterator = args.iter();
            if let Some(first) = iterator.next() {
                if iterator.next().is_some() {
                    todo!()
                }
                // TODO match
                Inferred::from_type(type_.clone())
            } else {
                todo!()
            }
        }
        DbType::Self_ => {
            i_s.current_class()
                .unwrap()
                .execute(i_s, args, result_context, on_type_error);
            Inferred::from_type(DbType::Self_)
        }
        DbType::Any => Inferred::new_any(),
        DbType::Dataclass(d) => {
            DataclassHelper(d).initialize(i_s, args, result_context, on_type_error)
        }
        DbType::TypedDict(td) => {
            TypedDictHelper(td).initialize(i_s, args, result_context, on_type_error)
        }
        DbType::NamedTuple(nt) => {
            let calculated_type_vars = calculate_callable_type_vars_and_return(
                i_s,
                Callable::new(&nt.__new__, None),
                args.iter(),
                &|| args.as_node_ref(),
                true,
                &mut ResultContext::Unknown,
                Some(on_type_error),
            );
            debug!("TODO use generics for namedtuple");
            Inferred::from_type(DbType::NamedTuple(nt.clone()))
        }
        DbType::Enum(_) => {
            debug!("TODO did not check arguments in execution of enum");
            Inferred::from_type(type_.clone())
        }
        DbType::Union(union) => Inferred::gather_base_types(i_s, |gather| {
            for t in union.iter() {
                gather(execute_type_of_type(
                    i_s,
                    args,
                    result_context,
                    on_type_error,
                    t,
                ))
            }
        }),
        _ => todo!("{:?}", type_),
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
