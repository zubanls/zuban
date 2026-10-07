mod callable;
mod common_base_type;
mod common_sub_type;
mod custom_behavior;
mod dataclass;
mod enum_;
mod generics;
mod intersection;
mod literal;
mod lookup_result;
mod matching;
mod named_tuple;
mod namespace;
mod new_type;
mod operations;
mod overlaps;
mod recursive_type;
mod replace;
mod sentinel;
mod tuple;
mod type_var_likes;
mod typed_dict;
mod union;
mod utils;

use std::{borrow::Cow, cell::Cell, hash::Hash, sync::Arc};

use typed_dict::rc_typed_dict_as_callable;
use vfs::FileIndex;

pub(crate) use self::{
    callable::*, custom_behavior::*, dataclass::*, enum_::*, generics::*, intersection::*,
    literal::*, lookup_result::*, matching::*, named_tuple::*, namespace::*, new_type::*,
    operations::*, recursive_type::*, replace::*, sentinel::*, tuple::*, type_var_likes::*,
    typed_dict::*, union::*,
};
use crate::{
    database::{Database, PointLink},
    debug,
    diagnostics::IssueKind,
    file::ClassNodeRef,
    format_data::{AvoidRecursionFor, FormatData, find_similar_types},
    inference_state::InferenceState,
    inferred::Inferred,
    match_::{Match, MismatchReason},
    matching::{ErrorStrs, ErrorTypes, Generic, Generics, GotType, Matcher},
    new_class, recoverable_error,
    type_helpers::{Class, Instance, MroIterator, TypeOrClass},
    utils::join_with_commas,
};

thread_local! {
    static EMPTY_TYPES: Arc<[Type]> = Arc::new([]);
}

pub(crate) fn empty_types() -> Arc<[Type]> {
    EMPTY_TYPES.with(|t| t.clone())
}

// PartialEq is only here for optimizations, it is not a reliable way to check if a type matches
// with another type.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[allow(clippy::enum_variant_names)]
pub(crate) enum Type {
    Class(GenericClass),
    Union(UnionType),
    Intersection(Intersection),
    FunctionOverload(FunctionOverload),
    TypeVar(TypeVarUsage),
    Type(Arc<Type>),
    Tuple(Arc<Tuple>),
    Callable(Arc<CallableContent>),
    RecursiveType(Arc<RecursiveType>),
    NewType(Arc<NewType>),
    ParamSpecArgs(ParamSpecUsage),
    ParamSpecKwargs(ParamSpecUsage),
    Literal(Literal),
    Dataclass(Arc<Dataclass>),
    TypedDict(Arc<TypedDict>),
    NamedTuple(Arc<NamedTuple>),
    Enum(Arc<Enum>),
    EnumMember(EnumMember),
    Module(FileIndex),
    Namespace(Arc<Namespace>),
    Super {
        class: Arc<GenericClass>,
        bound_to: Arc<Type>,
        mro_index: usize,
    },
    CustomBehavior(CustomBehavior),
    DataclassTransformObj(DataclassTransformObj),
    Self_,
    None,
    LiteralString {
        implicit: bool,
    },
    TypeForm(Arc<Type>),
    Sentinel(Sentinel),
    Any(AnyCause),
    Never(NeverCause),
}

impl Type {
    pub fn new_class(link: PointLink, generics: ClassGenerics) -> Self {
        Self::Class(GenericClass { link, generics })
    }

    pub const ERROR: Self = Self::Any(AnyCause::FromError);
    pub const NEVER: Self = Self::Never(NeverCause::Other);

    pub fn from_union_entries(entries: Vec<Type>, might_have_defined_type_vars: bool) -> Self {
        match entries.len() {
            0 => Type::NEVER,
            1 => entries.into_iter().next().unwrap(),
            _ => Type::Union(UnionType::new(entries, might_have_defined_type_vars)),
        }
    }

    pub fn filter(&self, db: &Database, filter: impl Fn(&Type) -> bool) -> Self {
        let might_have_defined_type_vars = match self {
            Type::Union(u) => u.might_have_type_vars,
            _ => true,
        };
        TypeGatherer::from_iter(
            self.iter_with_unpacked_unions(db)
                .filter(|t| filter(t))
                .cloned(),
        )
        .into_type_with_might_have_type_vars(might_have_defined_type_vars)
    }

    pub fn is_union_like(&self, db: &Database) -> bool {
        match self {
            Type::Union(_) => true,
            Type::Type(t) if t.as_ref().is_union_like(db) => true,
            Type::RecursiveType(r) => r.calculated_type(db).is_union_like(db),
            _ => false,
        }
    }

    pub fn maybe_union_like<'x>(&'x self, db: &'x Database) -> Option<Cow<'x, UnionType>> {
        match self {
            Type::Union(u) => Some(Cow::Borrowed(u)),
            Type::Type(t) => t.maybe_union_like(db).map(|u| {
                Cow::Owned(UnionType::from_types(
                    u.entries.iter().map(|e| Type::Type(Arc::new(e.clone()))),
                    u.might_have_type_vars,
                ))
            }),
            Type::RecursiveType(r) => r.calculated_type(db).maybe_union_like(db),
            _ => None,
        }
    }

    pub fn maybe_union_like_with_materializations<'x>(
        &'x self,
        db: &'x Database,
    ) -> Option<Cow<'x, UnionType>> {
        const MAX_MATERIALIZATIONS: usize = 20;
        self.maybe_union_like(db).or_else(|| {
            Some(Cow::Owned(UnionType::from_types(
                // For all of these we need to ensure that there are multiple union members. It
                // otherwise makes no sense.
                match self {
                    Type::Class(c) if c.link == db.python_state.bool_link() => {
                        vec![
                            Type::Literal(Literal::new_implicit(LiteralKind::Bool(true))),
                            Type::Literal(Literal::new_implicit(LiteralKind::Bool(false))),
                        ]
                    }
                    Type::Enum(e)
                        if e.members.len() < MAX_MATERIALIZATIONS && e.members.len() > 1 =>
                    {
                        Enum::implicit_members(e).map(Type::EnumMember).collect()
                    }
                    Type::Tuple(tup) => match &tup.args {
                        TupleArgs::FixedLen(items) => {
                            let union_for_each_entry: Vec<_> = items
                                .iter()
                                .map(|t| t.maybe_union_like_with_materializations(db))
                                .collect();
                            if union_for_each_entry.iter().all(|x| x.is_none()) {
                                return None;
                            }
                            let mut new_tuples = vec![vec![]];
                            for (tuple_index, maybe_union) in
                                union_for_each_entry.into_iter().enumerate()
                            {
                                if let Some(union_split_up) = maybe_union {
                                    let original_len = new_tuples.len();
                                    let union_len = union_split_up.entries.len();
                                    if union_len * original_len > MAX_MATERIALIZATIONS {
                                        return None;
                                    }
                                    for _ in 0..union_len - 1 {
                                        new_tuples.extend_from_within(0..original_len);
                                    }
                                    for j in 0..original_len {
                                        for (k, add_t) in union_split_up.iter().enumerate() {
                                            new_tuples[j * union_len + k].push(add_t.clone());
                                        }
                                    }
                                } else {
                                    let new = &items[tuple_index];
                                    for new_tuple in &mut new_tuples {
                                        new_tuple.push(new.clone());
                                    }
                                }
                            }
                            if new_tuples.len() <= 1 {
                                return None;
                            }
                            new_tuples
                                .into_iter()
                                .map(|ts| Type::Tuple(Tuple::new_fixed_length(Arc::from(ts))))
                                .collect()
                        }
                        _ => return None,
                    },
                    _ => return None,
                },
                false,
            )))
        })
    }

    pub fn is_calculating(&self, db: &Database) -> bool {
        match self {
            Type::Class(c) => c.class(db).is_calculating_class_infos(),
            Type::Tuple(tup) => tup.is_calculating(),
            Type::RecursiveType(r) => r
                .calculated_type_if_ready(db)
                .is_none_or(|t| t.is_calculating(db)),
            Type::Union(u) => u.iter().any(|t| t.is_calculating(db)),
            Type::Intersection(i) => i.iter_entries().any(|t| t.is_calculating(db)),
            _ => false,
        }
    }

    pub fn is_any(&self) -> bool {
        matches!(self, Type::Any(_))
    }

    pub fn is_never(&self) -> bool {
        matches!(self, Type::Never(_))
    }

    pub fn is_any_or_any_in_union(&self, db: &Database) -> bool {
        self.iter_with_unpacked_unions(db)
            .any(|t| matches!(t, Type::Any(_)))
    }

    pub fn maybe_remove_any(&self, db: &Database) -> Option<Self> {
        if !self.is_any_or_any_in_union(db) {
            return None;
        }
        Some(self.filter(db, |t| !t.is_any()))
    }

    pub fn is_type_of_any(&self) -> bool {
        match self {
            Type::Type(t) => t.is_any(),
            _ => false,
        }
    }

    pub fn is_none_or_none_in_union(&self, db: &Database) -> bool {
        self.iter_with_unpacked_unions(db)
            .any(|t| matches!(t, Type::None))
    }

    pub fn is_object(&self, db: &Database) -> bool {
        match self {
            Self::Class(c) => c.link == db.python_state.object_link(),
            _ => false,
        }
    }

    pub fn is_final(&self, db: &Database) -> bool {
        match self {
            Type::Class(c) => c.class(db).use_cached_class_infos(db).is_final,
            Type::Dataclass(d) => d.class(db).use_cached_class_infos(db).is_final,
            Type::Enum(_) | Type::EnumMember(_) => true, // Enums are always final
            _ => false,
        }
    }

    pub fn is_metaclass(&self, db: &Database) -> bool {
        match self {
            Type::Class(c) => c.class(db).is_metaclass(db),
            _ => false,
        }
    }

    pub fn maybe_remove_none(&self, db: &Database) -> Option<Type> {
        if self.is_none_or_none_in_union(db) {
            Some(self.filter(db, |t| !matches!(t, Type::None)))
        } else {
            None
        }
    }

    pub fn remove_none(&self, db: &Database) -> Cow<'_, Type> {
        self.maybe_remove_none(db)
            .map(Cow::Owned)
            .unwrap_or(Cow::Borrowed(self))
    }

    pub fn iter_with_unpacked_unions_without_unpacking_recursive_types(
        &self,
    ) -> impl Iterator<Item = &Type> {
        match self {
            Type::Union(items) => TypeRefIterator::Union(items.iter()),
            Type::Never(_) => TypeRefIterator::Finished,
            t => TypeRefIterator::Single(t),
        }
    }

    pub fn iter_with_unpacked_unions<'a>(
        &'a self,
        db: &'a Database,
    ) -> impl Iterator<Item = &'a Type> {
        self.iter_with_unpacked_unions_and_maybe_include_never(db, false)
    }

    pub fn iter_with_unpacked_unions_and_maybe_include_never<'a>(
        &'a self,
        db: &'a Database,
        include_never: bool,
    ) -> impl Iterator<Item = &'a Type> {
        RecursiveTypeIterator::new(
            db,
            include_never,
            match self {
                Type::Union(items) => TypeRefIterator::Union(items.iter()),
                Type::Never(_) if !include_never => TypeRefIterator::Finished,
                Type::RecursiveType(rec) => {
                    return rec
                        .calculated_type(db)
                        .iter_with_unpacked_unions_and_maybe_include_never(db, include_never);
                }
                t => TypeRefIterator::Single(t),
            },
        )
    }

    pub fn for_all_in_union(&self, db: &Database, callback: &impl Fn(&Type) -> bool) -> bool {
        self.iter_with_unpacked_unions(db).all(|t| match t {
            Type::Intersection(intersection) => intersection.iter_entries().any(callback),
            _ => callback(t),
        })
    }

    pub fn valid_in_type_form_assignment(&self, db: &Database) -> bool {
        self.iter_with_unpacked_unions(db)
            .all(|t| matches!(t, Type::TypeForm(_) | Type::Type(_) | Type::None))
    }

    #[inline]
    pub fn maybe_class<'a>(&'a self, db: &'a Database) -> Option<Class<'a>> {
        match self {
            Type::Class(c) => Some(c.class(db)),
            _ => None,
        }
    }

    pub fn inner_generic_class<'db: 'x, 'x>(
        &'x self,
        i_s: &InferenceState<'db, 'x>,
        allow_callable: bool,
    ) -> Option<Class<'x>> {
        match self {
            Type::Self_ => {
                let cls = i_s.current_class();
                if cls.is_none() {
                    recoverable_error!(
                        "Self was somehow not handled properly when finding inner_generic_class"
                    )
                }
                cls
            }
            Type::Type(t) => Some(
                t.inner_generic_class(i_s, allow_callable)?
                    .use_cached_class_infos(i_s.db)
                    .metaclass(i_s.db),
            ),
            _ => self.inner_generic_class_with_db(i_s.db, allow_callable),
        }
    }

    pub fn inner_generic_class_with_db<'x>(
        &'x self,
        db: &'x Database,
        allow_callable: bool,
    ) -> Option<Class<'x>> {
        Some(match self {
            Type::Class(c) => c.class(db),
            Type::Dataclass(dc) => dc.class(db),
            Type::Enum(enum_) => enum_.class(db),
            Type::EnumMember(member) => member.enum_.class(db),
            Type::Literal(l) => l.fallback_class(db),
            Type::LiteralString { .. } => db.python_state.str_class(),
            Type::Type(t) => t
                .inner_generic_class_with_db(db, allow_callable)?
                .use_cached_class_infos(db)
                .metaclass(db),
            Type::TypeVar(tv) => match tv.type_var.kind(db) {
                TypeVarKind::Bound(t) => return t.inner_generic_class_with_db(db, allow_callable),
                _ => return None,
            },
            Type::TypedDict(_) => db.python_state.typed_dict_class(),
            Type::Callable(_) | Type::FunctionOverload(_) if allow_callable => {
                db.python_state.function_class()
            }
            Type::RecursiveType(r) => {
                return r
                    .calculated_type(db)
                    .inner_generic_class_with_db(db, allow_callable);
            }
            Type::NewType(n) => return n.type_.inner_generic_class_with_db(db, allow_callable),
            _ => return None,
        })
    }

    #[inline]
    pub fn maybe_type_of_class<'a>(&'a self, db: &'a Database) -> Option<Class<'a>> {
        if let Type::Type(t) = self
            && let Type::Class(c) = t.as_ref()
        {
            return Some(c.class(db));
        }
        None
    }

    pub fn maybe_typed_dict(&self, _: &Database) -> Option<Arc<TypedDict>> {
        match self {
            Type::TypedDict(td) => Some(td.clone()),
            _ => None,
        }
    }

    pub fn maybe_callable(&self, i_s: &InferenceState) -> Option<CallableLike> {
        let check_class = |cls: Class| {
            let had_issue = Cell::new(false);
            cls.instance()
                .type_lookup(
                    i_s,
                    |issue| {
                        debug!("Caught issue: {issue:?}");
                        had_issue.set(true);
                        false
                    },
                    "__call__",
                )
                .into_maybe_inferred()
                .filter(|_| !had_issue.get())
                .and_then(|i| i.as_cow_type(i_s).maybe_callable(i_s))
        };
        match self {
            Type::Callable(c) => Some(CallableLike::Callable(c.clone())),
            Type::Type(t) => t.type_type_maybe_callable(i_s),
            Type::Any(cause) => Some(CallableLike::Callable(Arc::new(CallableContent::new_any(
                i_s.db.python_state.empty_type_var_likes.clone(),
                *cause,
            )))),
            Type::Class(c) => check_class(c.class(i_s.db)),
            Type::FunctionOverload(overload) => Some(CallableLike::Overload(overload.clone())),
            Type::TypeVar(t) => match t.type_var.kind(i_s.db) {
                TypeVarKind::Bound(bound) => bound.maybe_callable(i_s),
                _ => None,
            },
            Type::CustomBehavior(_) => Some(CallableLike::Callable(
                // TODO this should not be Any
                i_s.db.python_state.any_callable_from_error.clone(),
            )),
            Type::Dataclass(dc) => check_class(dc.class(i_s.db)),
            Type::Enum(e) => check_class(e.class(i_s.db)),
            Type::EnumMember(e) => check_class(e.enum_.class(i_s.db)),
            _ => None,
        }
    }

    fn type_type_maybe_callable(&self, i_s: &InferenceState) -> Option<CallableLike> {
        let cls_callable = |cls: Class| {
            let error = Cell::new(false);
            let result = cls
                .find_relevant_constructor(i_s, &|_| {
                    error.set(true);
                    false
                })
                .maybe_callable(i_s, cls);
            if error.get() {
                return None;
            }
            result
        };
        // Is type[Foo] a callable?
        match self {
            Type::Class(c) => cls_callable(c.class(i_s.db)),
            Type::Dataclass(d) => {
                let cls = d.class(i_s.db);
                // A dataclass cannot generate __init__ or overwrite it in its class body
                if d.options.init && cls.lookup_symbol(i_s, "__init__").is_none() {
                    let mut init = dataclass_init_func(d, i_s.db).clone();
                    if d.class.generics != ClassGenerics::NotDefinedYet
                        || cls.use_cached_type_vars(i_s.db).is_empty()
                    {
                        init.return_type = self.clone();
                    } else {
                        let mut type_var_dataclass = (**d).clone();
                        type_var_dataclass.class = Class::with_self_generics(i_s.db, cls.node_ref)
                            .as_generic_class(i_s.db);
                        init.return_type = Type::Dataclass(Arc::new(type_var_dataclass));
                    }
                    return Some(CallableLike::Callable(Arc::new(init)));
                }
                cls_callable(cls)
            }
            Type::TypedDict(td) => Some(CallableLike::Callable(Arc::new(
                rc_typed_dict_as_callable(i_s.db, td.clone()),
            ))),
            Type::NamedTuple(nt) => {
                let mut callable = nt.__new__.remove_first_positional_param().unwrap();
                callable.return_type = self.clone();
                Some(CallableLike::Callable(Arc::new(callable)))
            }
            Type::Tuple(tup) => {
                // Tuple exists either as tuple() or tuple(<some iterable>), we can not force the
                // correct length of a tuple when an iterable is provided, therefore only work with
                // that case.
                let iterable = new_class!(
                    i_s.db.python_state.iterable_link(),
                    tup.fallback_type(i_s.db).clone(),
                );
                let mut param = CallableParam::new_anonymous(ParamType::PositionalOnly(iterable));
                param.has_default = true;
                Some(CallableLike::Callable(Arc::new(
                    CallableContent::new_simple(
                        None,
                        None,
                        i_s.db.python_state.tuple_node_ref().as_link(),
                        i_s.db.python_state.empty_type_var_likes.clone(),
                        CallableParams::new_simple(Arc::new([param])),
                        Type::Tuple(tup.clone()),
                    ),
                )))
            }
            Type::NewType(nt) => Some({
                let mut result = nt.type_.type_type_maybe_callable(i_s)?;
                let map_callable = |c: &Arc<CallableContent>| {
                    let mut new = c.as_ref().clone();
                    new.return_type = Type::NewType(nt.clone());
                    Arc::new(new)
                };
                match &mut result {
                    CallableLike::Callable(c) => *c = map_callable(c),
                    CallableLike::Overload(o) => {
                        *o = FunctionOverload::new(o.iter_functions().map(map_callable).collect())
                    }
                }
                result
            }),
            Type::Enum(enum_) => Some({
                CallableLike::Callable(Arc::new(CallableContent::new_non_generic(
                    i_s.db,
                    None,
                    None,
                    enum_.defined_at,
                    [CallableParam::new(
                        DbString::Static("value"),
                        ParamType::PositionalOrKeyword(Type::Any(AnyCause::Internal)),
                    )],
                    self.clone(),
                )))
            }),
            _ => None,
        }
    }

    pub fn is_func_or_overload(&self) -> bool {
        match self {
            Type::Callable(_) | Type::FunctionOverload(_) => true,
            Type::Union(u) => u.iter().any(|t| t.is_func_or_overload()),
            _ => false,
        }
    }

    pub fn is_func_or_overload_not_any_callable(&self) -> bool {
        match self {
            Type::Callable(c) => !matches!(&c.params, CallableParams::Any(_)),
            Type::FunctionOverload(_) => true,
            Type::Union(u) => u.iter().any(|t| t.is_func_or_overload_not_any_callable()),
            _ => false,
        }
    }

    pub fn format_short(&self, db: &Database) -> Box<str> {
        let similar_types = find_similar_types(db, &[self]);
        self.format(&FormatData::with_types_that_need_qualified_names(
            db,
            &similar_types,
        ))
    }

    pub fn format(&self, format_data: &FormatData) -> Box<str> {
        match self {
            Self::Class(c) => c.class(format_data.db).format(format_data),
            Self::Union(union) => union.format(format_data),
            Self::FunctionOverload(callables) => match format_data.style {
                FormatStyle::MypyRevealType => format!(
                    "Overload({})",
                    join_with_commas(callables.iter_functions().map(|t| t.format(format_data)))
                )
                .into(),
                _ => Box::from("overloaded function"),
            },
            Self::TypeVar(t) => format_data.format_type_var(t),
            Self::Type(type_) => format!("type[{}]", type_.format(format_data)).into(),
            Self::Tuple(content) => content.format(format_data),
            Self::Callable(content) => content.format(format_data).into(),
            Self::Any(_) => Box::from("Any"),
            Self::None => Box::from("None"),
            Self::Never(_) => Box::from("Never"),
            Self::Literal(literal) => literal.format(format_data),
            Self::NewType(n) => n.format(format_data),
            Self::RecursiveType(rec) => {
                if let Some(generics) = &rec.generics
                    && format_data.style != FormatStyle::MypyRevealType
                {
                    return format!(
                        "{}[{}]",
                        rec.name(format_data.db),
                        generics.format(format_data)
                    )
                    .into();
                }

                let avoid = AvoidRecursionFor::RecursiveType(rec);
                match format_data.with_seen_recursive_type(avoid) {
                    Ok(format_data) => {
                        if let Some(t) = rec.calculated_type_if_ready(format_data.db) {
                            t.format(&format_data)
                        } else {
                            // Happens only in weird cases like MRO calculation and will probably mostly
                            // appear when debugging.
                            rec.name(format_data.db).into()
                        }
                    }
                    Err(()) => {
                        if format_data.style == FormatStyle::MypyRevealType {
                            "...".into()
                        } else {
                            rec.name(format_data.db).into()
                        }
                    }
                }
            }
            Self::Self_ => Box::from("Self"),
            Self::ParamSpecArgs(usage) => {
                format!("{}.args", usage.param_spec.name(format_data.db)).into()
            }
            Self::ParamSpecKwargs(usage) => {
                format!("{}.kwargs", usage.param_spec.name(format_data.db)).into()
            }
            Self::Dataclass(d) => d.class(format_data.db).format(format_data),
            Self::TypedDict(d) => d.format(format_data).into(),
            Self::NamedTuple(nt) => match format_data.style {
                FormatStyle::Short
                    if !format_data.should_format_qualified(nt.__new__.defined_at) =>
                {
                    nt.format_with_name(
                        format_data,
                        nt.name(format_data.db),
                        Generics::None, // Format without generics
                    )
                }
                _ => nt.format_with_name(
                    format_data,
                    &nt.qualified_name(format_data.db),
                    Generics::None, // Format without generics
                ),
            },
            Self::Enum(e) => e.format(format_data).into(),
            Self::EnumMember(e) => e.format(format_data).into(),
            Self::Module(_) => format_data
                .db
                .python_state
                .module_type()
                .format(format_data),
            Self::Intersection(intersection) => intersection.format(format_data),
            Self::Namespace(_) => match format_data.style {
                FormatStyle::Short => "ModuleType".into(),
                FormatStyle::MypyRevealType => "types.ModuleType".into(),
            },
            Self::Super { .. } => "super".into(),
            Self::CustomBehavior(_) => "TODO custombehavior".into(),
            Self::DataclassTransformObj(_) => "TODO dataclass_transform".into(),
            Self::LiteralString { .. } => "LiteralString".into(),
            Self::TypeForm(t) => format!("TypeForm[{}]", t.format(format_data)).into(),
            Self::Sentinel(s) => s.format(format_data),
        }
    }

    pub fn search_type_vars<C: FnMut(TypeVarLikeUsage) + ?Sized>(&self, found_type_var: &mut C) {
        match self {
            Self::Class(GenericClass {
                generics: ClassGenerics::List(generics),
                ..
            }) => generics.search_type_vars(found_type_var),
            Self::Union(u) => {
                for t in u.iter() {
                    t.search_type_vars(found_type_var);
                }
            }
            Self::FunctionOverload(intersection) => {
                for callable in intersection.iter_functions() {
                    callable.search_type_vars(found_type_var);
                }
            }
            Self::TypeVar(t) => found_type_var(TypeVarLikeUsage::TypeVar(t.clone())),
            Self::Type(type_) => type_.search_type_vars(found_type_var),
            Self::Tuple(tup) => tup.args.search_type_vars(found_type_var),
            Self::Callable(c) => c.search_type_vars(found_type_var),
            Self::Class(..)
            | Self::Any(_)
            | Self::None
            | Self::Never(_)
            | Self::Literal { .. }
            | Self::Module(_)
            | Self::Self_
            | Self::Namespace(_)
            | Self::Super { .. }
            | Self::CustomBehavior(_)
            | Self::DataclassTransformObj(_)
            | Self::Enum(_)
            | Self::EnumMember(_)
            | Self::NewType(_)
            | Self::Sentinel(_)
            | Self::LiteralString { .. } => (),
            Self::RecursiveType(rec) => {
                if let Some(generics) = rec.generics.as_ref() {
                    generics.search_type_vars(found_type_var)
                }
            }
            Self::ParamSpecArgs(usage) => {
                found_type_var(TypeVarLikeUsage::ParamSpec(usage.clone()))
            }
            Self::ParamSpecKwargs(usage) => {
                found_type_var(TypeVarLikeUsage::ParamSpec(usage.clone()))
            }
            Self::Dataclass(d) => {
                if let ClassGenerics::List(generics) = &d.class.generics {
                    generics.search_type_vars(found_type_var)
                }
            }
            Self::TypedDict(d) => d.search_type_vars(found_type_var),
            Self::NamedTuple(_) => {
                debug!("TODO do we need to support namedtuple searching for type vars?");
            }
            Self::Intersection(i) => {
                for t in i.iter_entries() {
                    t.search_type_vars(found_type_var)
                }
            }
            Self::TypeForm(tf) => tf.search_type_vars(found_type_var),
        }
    }

    pub fn has_type_vars(&self) -> bool {
        let mut result = false;
        self.search_type_vars(&mut |_| result = true);
        result
    }

    pub fn has_any(&self, db: &Database) -> bool {
        self.has_any_internal(db, &mut Vec::new(), &|_| true)
    }

    pub fn has_any_internal(
        &self,
        db: &Database,
        already_checked: &mut Vec<Arc<RecursiveType>>,
        recheck: &impl Fn(AnyCause) -> bool,
    ) -> bool {
        let has_any_callable_params = |list: &GenericsList| {
            list.iter().any(|generic| match generic {
                GenericItem::ParamSpecArg(ParamSpecArg {
                    params: CallableParams::Any(cause),
                    ..
                }) => recheck(*cause),
                _ => false,
            })
        };
        let has_any_callable_params_in_generics = |generics: &_| match generics {
            ClassGenerics::List(list) => has_any_callable_params(list),
            _ => false,
        };
        self.find_in_type(db, &mut |t| match t {
            Self::Any(cause) => recheck(*cause),
            Self::RecursiveType(recursive) => {
                if let Some(generics) = &recursive.generics
                    && has_any_callable_params(generics)
                {
                    return true;
                }
                if already_checked.contains(recursive) {
                    false
                } else {
                    already_checked.push(recursive.clone());
                    match recursive.origin(db) {
                        RecursiveTypeOrigin::TypeAlias(type_alias) => {
                            !type_alias.calculating()
                                && type_alias.type_if_valid().has_any_internal(
                                    db,
                                    already_checked,
                                    recheck,
                                )
                        }
                        RecursiveTypeOrigin::Class(_) => false,
                    }
                }
            }
            Self::NewType(n) => n.type_.has_any_internal(db, already_checked, recheck),
            Self::Callable(c) => matches!(c.params, CallableParams::Any(cause) if recheck(cause)),

            Self::Class(c) => has_any_callable_params_in_generics(&c.generics),
            Self::Dataclass(d) => has_any_callable_params_in_generics(&d.class.generics),
            Self::TypedDict(td) => match &td.generics {
                TypedDictGenerics::Generics(list) => has_any_callable_params(list),
                _ => false,
            },
            // This is a special case for the experimental advanced function return inference mode
            Self::TypeVar(tv) => tv.type_var.is_untyped() && recheck(AnyCause::Unannotated),

            // All the other types are are either not Any or inner types will be checked by the
            // recursive nature of find_types.
            Self::None
            | Self::Never(_)
            | Self::Literal { .. }
            | Self::ParamSpecArgs(_)
            | Self::ParamSpecKwargs(_)
            | Self::Module(_)
            | Self::Enum(_)
            | Self::CustomBehavior(_)
            | Self::DataclassTransformObj(_)
            | Self::EnumMember(_)
            | Self::Super { .. }
            | Self::Namespace(_)
            | Self::Sentinel(_)
            | Self::LiteralString { .. }
            | Self::Union(_)
            | Self::Intersection(_)
            | Self::FunctionOverload(_)
            | Self::Type(_)
            | Self::Tuple(_)
            | Self::NamedTuple(_)
            | Self::Self_
            | Self::TypeForm(_) => false,
        })
    }

    pub fn has_self_type(&self, db: &Database) -> bool {
        self.find_in_type(db, &mut |t| matches!(t, Type::Self_))
    }

    pub fn find_in_type(&self, db: &Database, check: &mut impl FnMut(&Type) -> bool) -> bool {
        if check(self) {
            return true;
        }
        let mut search_in_generic_class = |c: &GenericClass| {
            Generics::from_class_generics(db, ClassNodeRef::from_link(db, c.link), &c.generics)
                .iter(db)
                .any(|generic| generic.find_in_type(db, check))
        };

        match self {
            Self::Class(c) => search_in_generic_class(c),
            Self::Dataclass(d) => search_in_generic_class(&d.class),
            Self::Union(u) => u.iter().any(|t| t.find_in_type(db, check)),
            Self::FunctionOverload(o) => o.iter_functions().any(|c| c.find_in_type(db, check)),
            Self::Type(t) => t.find_in_type(db, check),
            Self::Tuple(tup) => tup.args.find_in_type(db, check),
            Self::Callable(content) => content.find_in_type(db, check),
            Self::RecursiveType(recursive) => match &recursive.generics {
                Some(gs) => gs.iter().any(|g| Generic::new(g).find_in_type(db, check)),
                None => false,
            },
            Self::TypedDict(d) => {
                (match &d.generics {
                    TypedDictGenerics::Generics(gs) => {
                        gs.iter().any(|g| Generic::new(g).find_in_type(db, check))
                    }
                    TypedDictGenerics::None | TypedDictGenerics::NotDefinedYet(_) => false,
                }) || {
                    let Ok(members) = d.members_if_ready(db) else {
                        // This is a bit unfortunate, but TypedDicts can be unfinished
                        return false;
                    };
                    if let Some(extra) = &members.extra_items
                        && extra.t.find_in_type(db, check)
                    {
                        return true;
                    }
                    members
                        .named
                        .iter()
                        .any(|t| t.type_.find_in_type(db, check))
                }
            }
            Self::Intersection(intersection) => intersection
                .iter_entries()
                .any(|t| t.find_in_type(db, check)),
            Self::TypeForm(tf) => tf.find_in_type(db, check),
            _ => false,
        }
    }

    pub fn has_any_with_unknown_type_params(&self, db: &Database) -> bool {
        self.has_any_internal(db, &mut Vec::new(), &|cause| {
            cause == AnyCause::UnknownTypeParam
        })
    }

    pub fn has_any_but_not_from_coroutine(&self, db: &Database) -> bool {
        self.has_any_internal(db, &mut Vec::new(), &|cause| {
            cause != AnyCause::AsyncCoroutine
        })
    }

    pub fn has_untyped_type_params(&self, db: &Database) -> bool {
        if !db.project.should_infer_untyped_params() {
            return false;
        }
        self.find_in_type(
            db,
            &mut |t| matches!(t, Type::TypeVar(tv) if tv.type_var.is_untyped()),
        )
    }

    pub fn is_subclassable(&self, db: &Database) -> bool {
        match self {
            Self::Class(_)
            | Self::Tuple(_)
            | Self::NewType(_)
            | Self::NamedTuple(_)
            | Self::Dataclass(_) => true,
            Self::RecursiveType(r) => matches!(r.origin(db), RecursiveTypeOrigin::Class(_)),
            _ => false,
        }
    }

    pub fn is_intersectable(&self, db: &Database) -> bool {
        self.is_subclassable(db) || matches!(self, Type::Intersection(_))
    }

    pub fn maybe_avoid_implicit_literal(&self, db: &Database) -> Option<Self> {
        match self {
            Type::Literal(l) if l.implicit => Some(l.fallback_type(db)),
            Type::LiteralString { implicit: true } => Some(db.python_state.str_type()),
            Type::EnumMember(m) if m.implicit => Some(Type::Enum(m.enum_.clone())),
            Type::Tuple(tup) => Some(Type::Tuple(tup.maybe_avoid_implicit_literal(db)?)),
            Type::Union(union) => {
                if union
                    .iter()
                    .any(|t| t.maybe_avoid_implicit_literal(db).is_some())
                {
                    let mut gathered: Vec<Type> = vec![];
                    for entry in union.entries.iter() {
                        if let Some(type_) = entry.maybe_avoid_implicit_literal(db) {
                            if !gathered.iter().any(|e| *e == type_) {
                                gathered.push(type_);
                            }
                        } else if !gathered.contains(entry) {
                            gathered.push(entry.clone())
                        }
                    }
                    if gathered.len() == 1 {
                        return Some(gathered.into_iter().next().unwrap());
                    } else {
                        return Some(Type::Union(UnionType::new(
                            gathered,
                            union.might_have_type_vars,
                        )));
                    }
                }
                None
            }
            _ => None,
        }
    }

    pub fn avoid_implicit_literal(self, db: &Database) -> Self {
        self.maybe_avoid_implicit_literal(db).unwrap_or(self)
    }

    pub fn avoid_implicit_literal_cow(&self, db: &Database) -> Cow<'_, Self> {
        if let Some(t) = self.maybe_avoid_implicit_literal(db) {
            Cow::Owned(t)
        } else {
            Cow::Borrowed(self)
        }
    }

    pub fn is_literal_or_literal_in_tuple(&self) -> bool {
        self.iter_with_unpacked_unions_without_unpacking_recursive_types()
            .any(|t| match t {
                Type::Literal(_) | Type::EnumMember(_) => true,
                Type::Tuple(tup) => match &tup.args {
                    TupleArgs::FixedLen(ts) => {
                        ts.iter().any(|t| t.is_literal_or_literal_in_tuple())
                    }
                    TupleArgs::ArbitraryLen(t) => t.is_literal_or_literal_in_tuple(),
                    TupleArgs::WithUnpack(unpack) => {
                        unpack
                            .before
                            .iter()
                            .any(|t| t.is_literal_or_literal_in_tuple())
                            || unpack
                                .after
                                .iter()
                                .any(|t| t.is_literal_or_literal_in_tuple())
                    }
                },
                _ => false,
            })
    }

    pub fn is_allowed_as_literal_string(&self, allow_non_string_literals: bool) -> bool {
        match self {
            Type::LiteralString { .. } => true,
            Type::Literal(_) if allow_non_string_literals => true,
            Type::Literal(l) => matches!(l.kind, LiteralKind::String(_)),
            Type::Union(u) => u
                .iter()
                .all(|t| t.is_allowed_as_literal_string(allow_non_string_literals)),
            Type::Intersection(i) => i
                .iter_entries()
                .any(|t| t.is_allowed_as_literal_string(allow_non_string_literals)),
            _ => false,
        }
    }

    pub fn mro<'db: 'x, 'x>(&'x self, db: &'db Database) -> MroIterator<'db, 'x> {
        match self {
            Type::Literal(literal) => MroIterator::new(
                db,
                match literal.kind {
                    LiteralKind::Int(_) => db.python_state.int_link(),
                    LiteralKind::Bool(_) => db.python_state.bool_link(),
                    LiteralKind::String(_) => db.python_state.str_link(),
                    LiteralKind::Bytes(_) => db.python_state.bytes_link(),
                },
                TypeOrClass::Type(Cow::Borrowed(self)),
                Generics::None,
                match literal.kind {
                    LiteralKind::Int(_) => db.python_state.builtins_int_mro.iter(),
                    LiteralKind::Bool(_) => db.python_state.builtins_bool_mro.iter(),
                    LiteralKind::String(_) => db.python_state.builtins_str_mro.iter(),
                    LiteralKind::Bytes(_) => db.python_state.builtins_bytes_mro.iter(),
                },
                false,
            ),
            Type::Class(c) => c.class(db).mro_without_remap(db, false),
            Type::Tuple(tup) => {
                let tuple_class = tup.class(db);
                MroIterator::new(
                    db,
                    tuple_class.as_link(),
                    TypeOrClass::Type(Cow::Borrowed(self)),
                    tuple_class.generics,
                    tuple_class.use_cached_class_infos(db).mro.iter(),
                    false,
                )
            }
            Type::Dataclass(d) => {
                let mut mro = d.class(db).mro_without_remap(db, false);
                mro.class = Some(TypeOrClass::Type(Cow::Borrowed(self)));
                mro
            }
            Type::TypedDict(_) => MroIterator::new(
                db,
                db.python_state.typed_dict_link(),
                TypeOrClass::Type(Cow::Borrowed(self)),
                Generics::None,
                db.python_state.typing_typed_dict_bases.iter(),
                false,
            ),
            Type::Enum(e) | Type::EnumMember(EnumMember { enum_: e, .. }) => {
                let class = e.class(db);
                MroIterator::new(
                    db,
                    class.as_link(),
                    TypeOrClass::Type(Cow::Borrowed(self)),
                    class.generics,
                    class.use_cached_class_infos(db).mro.iter(),
                    false,
                )
            }
            _ => {
                if let Type::RecursiveType(r) = self
                    && let Some(t) = r.calculated_type_if_ready(db)
                {
                    let mut mro = t.mro(db);
                    mro.class = Some(TypeOrClass::Type(Cow::Borrowed(self)));
                    mro
                } else {
                    MroIterator::new(
                        db,
                        // This is a fake entry that shouldn't really matter, because classes are
                        // not involved at this point.
                        PointLink::new(db.python_state.builtins().file_index, 0),
                        TypeOrClass::Type(Cow::Borrowed(self)),
                        Generics::None,
                        [].iter(),
                        false,
                    )
                }
            }
        }
    }

    pub fn find_class_in_mro<'x>(
        &'x self,
        db: &'x Database,
        target: ClassNodeRef,
    ) -> Option<Class<'x>> {
        self.mro(db)
            .find_map(|(_, type_or_class)| match type_or_class {
                TypeOrClass::Class(cls) if cls.node_ref == target => Some(cls),
                _ => None,
            })
    }

    pub(crate) fn error_if_not_assignable(
        &self,
        i_s: &InferenceState,
        value: &Inferred,
        add_issue: impl Fn(IssueKind) -> bool,
        mut on_error: impl FnMut(&ErrorTypes) -> Option<IssueKind>,
    ) {
        self.error_if_not_assignable_with_matcher(
            i_s,
            &mut Matcher::default(),
            value,
            add_issue,
            |error_types, _reason: &MismatchReason| on_error(error_types),
        );
    }

    pub(crate) fn error_if_not_assignable_with_matcher(
        &self,
        i_s: &InferenceState,
        matcher: &mut Matcher,
        value: &Inferred,
        add_issue: impl Fn(IssueKind) -> bool,
        on_error: impl FnMut(&ErrorTypes, &MismatchReason) -> Option<IssueKind>,
    ) {
        let value_type = value.as_cow_type(i_s);
        self.error_if_t_not_assignable_with_matcher(i_s, matcher, &value_type, add_issue, on_error);
    }

    pub(crate) fn error_if_t_not_assignable_with_matcher(
        &self,
        i_s: &InferenceState,
        matcher: &mut Matcher,
        value_type: &Type,
        add_issue: impl Fn(IssueKind) -> bool,
        mut on_error: impl FnMut(&ErrorTypes, &MismatchReason) -> Option<IssueKind>,
    ) -> Match {
        let matches = self.is_super_type_of(i_s, matcher, value_type);
        if let Match::False { ref reason, .. } = matches {
            let error_types = ErrorTypes {
                expected: self,
                got: GotType::Type(value_type),
                matcher: Some(matcher),
                reason,
            };
            if cfg!(feature = "zuban_debug") {
                let ErrorStrs { expected, got } = error_types.as_boxed_strs(i_s.db);
                debug!(
                    "Mismatch between {expected:?} and {got:?} -> {:?}",
                    &matches
                );
            }
            if let Some(error) = on_error(&error_types, reason) {
                if add_issue(error) {
                    error_types.add_mismatch_notes(|kind| {
                        add_issue(kind);
                    })
                }
            }
        }
        matches
    }

    pub fn on_any_typed_dict(
        &self,
        i_s: &InferenceState,
        matcher: &mut Matcher,
        callable: &mut impl FnMut(&mut Matcher, Arc<TypedDict>) -> bool,
    ) -> bool {
        self.on_any_resolved_context_type(i_s, matcher, &mut |matcher, t| match t {
            Type::TypedDict(td) => callable(matcher, td.clone()),
            _ => false,
        })
    }

    pub fn on_any_resolved_context_type(
        &self,
        i_s: &InferenceState,
        matcher: &mut Matcher,
        callable: &mut impl FnMut(&mut Matcher, &Type) -> bool,
    ) -> bool {
        match self {
            Type::Union(union_type) => union_type
                .iter()
                .any(|t| t.on_any_resolved_context_type(i_s, matcher, callable)),
            Type::RecursiveType(r) => r
                .calculated_type(i_s.db)
                .on_any_resolved_context_type(i_s, matcher, callable),
            type_ @ Type::TypeVar(_) => {
                if matcher.might_have_defined_type_vars() {
                    let new = matcher.replace_type_var_likes_for_nested_context(i_s.db, type_);
                    if new.as_ref() == type_ {
                        return false;
                    }
                    new.on_any_resolved_context_type(i_s, matcher, callable)
                } else {
                    false
                }
            }
            t => callable(matcher, t),
        }
    }

    pub fn on_unique_type_in_unpacked_union<TRANSFER, T>(
        &self,
        db: &Database,
        matcher: &mut Matcher,
        find: &impl Fn(&Type) -> Option<TRANSFER>,
        on_unique_found: impl FnOnce(&mut Matcher, TRANSFER) -> T,
    ) -> Result<T, UniqueInUnpackedUnionError> {
        let found = self.find_unique_type_in_unpacked_union(db, matcher, find)?;
        Ok(on_unique_found(matcher, found))
    }

    fn find_unique_type_in_unpacked_union<T>(
        &self,
        db: &Database,
        matcher: &mut Matcher,
        find: &impl Fn(&Type) -> Option<T>,
    ) -> Result<T, UniqueInUnpackedUnionError> {
        let mut found = Err(UniqueInUnpackedUnionError::None);
        for t in self.iter_with_unpacked_unions(db) {
            match t {
                Type::TypeVar(_) if matcher.might_have_defined_type_vars() => {
                    let new_t = matcher.replace_type_var_likes_for_nested_context(db, t);
                    if new_t.as_ref() == t {
                        if let Some(x) = find(t) {
                            if found.is_ok() {
                                return Err(UniqueInUnpackedUnionError::Multiple);
                            } else {
                                found = Ok(x)
                            }
                        }
                        continue;
                    }
                    let new = new_t.find_unique_type_in_unpacked_union(db, matcher, find);
                    match new {
                        Err(UniqueInUnpackedUnionError::Multiple) => return new,
                        // Avoid overwriting current results
                        Err(UniqueInUnpackedUnionError::None) => (),
                        Ok(_) if found.is_ok() => return Err(UniqueInUnpackedUnionError::Multiple),
                        _ => found = new,
                    }
                }
                _ => {
                    if let Some(x) = find(t) {
                        if found.is_ok() {
                            return Err(UniqueInUnpackedUnionError::Multiple);
                        } else {
                            found = Ok(x)
                        }
                    }
                }
            }
        }
        found
    }

    pub fn check_duplicate_base_class(&self, db: &Database, other: &Self) -> Option<Box<str>> {
        match (self, other) {
            (Type::Class(c1), Type::Class(c2)) => {
                (c1.link == c2.link).then(|| Box::from(c1.class(db).name()))
            }
            (Type::Type(_), Type::Type(_)) => Some(Box::from("type")),
            (Type::Tuple(_), Type::Tuple(_)) => Some(Box::from("tuple")),
            (Type::Callable(_), Type::Callable(_)) => Some(Box::from("callable")),
            (Type::TypedDict(td1), Type::TypedDict(td2)) if td1.defined_at == td2.defined_at => {
                Some(td1.name_or_fallback(&FormatData::new_short(db)).into())
            }
            _ => None,
        }
    }

    pub fn merge_matching_parts(&self, db: &Database, other: &Self) -> Self {
        // TODO performance there's a lot of into_type here, that should not really be
        /*
        if self.as_ref() == other.as_ref() {
            return self;
        }
        */
        // necessary.
        match self {
            Type::Class(c1) => match other {
                Type::Class(c2) if c1.link == c2.link => {
                    let new_generics = match &c1.generics {
                        ClassGenerics::None { .. } => ClassGenerics::new_none(),
                        _ => {
                            let class_ref = ClassNodeRef::from_link(db, c1.link);
                            ClassGenerics::List(GenericsList::new_generics(
                                Generics::from_class_generics(db, class_ref, &c1.generics)
                                    .iter(db)
                                    .zip(
                                        Generics::from_class_generics(db, class_ref, &c2.generics)
                                            .iter(db),
                                    )
                                    .map(|(gi1, gi2)| gi1.merge_matching_parts(db, gi2))
                                    .collect(),
                            ))
                        }
                    };
                    Type::new_class(c1.link, new_generics)
                }
                _ => Type::ERROR,
            },
            Type::Tuple(c1) => match other {
                Type::Tuple(c2) => {
                    Type::Tuple(Tuple::new(c1.args.merge_matching_parts(db, &c2.args)))
                }
                _ => Type::ERROR,
            },
            Type::Callable(_) => match other {
                Type::Callable(_) => {
                    Type::Callable(db.python_state.any_callable_from_error.clone())
                }
                _ => Type::ERROR,
            },
            _ => {
                if self.is_equal_type(db, other) {
                    self.clone()
                } else {
                    Type::ERROR
                }
            }
        }
    }

    pub fn maybe_fixed_len_tuple(&self) -> Option<&[Type]> {
        if let Type::Tuple(tup) = self
            && let TupleArgs::FixedLen(ts) = &tup.args
        {
            return Some(ts);
        }
        None
    }

    pub fn container_types(&self, i_s: &InferenceState) -> Option<Type> {
        let mut result = ComplexTypeGatherer::default();
        let db = i_s.db;
        for t in self.iter_with_unpacked_unions(db) {
            match t {
                Type::Tuple(tup) => result.add(tup.fallback_type(db).clone()),
                Type::NamedTuple(named_tup) => {
                    result.add(named_tup.as_tuple_ref().fallback_type(db).clone())
                }
                _ => {
                    for (_, base) in t.mro(db) {
                        if let Some(cls) = base.maybe_class()
                            && cls.node_ref == db.python_state.container_node_ref()
                        {
                            result.add(cls.nth_type_argument(db, 0));
                        }
                    }
                }
            }
        }
        if result.is_empty() {
            None
        } else {
            Some(result.into_simplified_type(i_s))
        }
    }

    pub fn type_of_protocol_to_type_of_protocol_assignment(
        &self,
        i_s: &InferenceState,
        value: &Inferred,
    ) -> bool {
        if let Type::Type(type_) = self
            && let Some(cls) = type_.maybe_class(i_s.db)
            && cls.is_protocol(i_s.db)
            && let Some(node_ref) = value.maybe_saved_node_ref(i_s.db)
            && node_ref.maybe_class().is_some()
        {
            let cls2 = Class::from_non_generic_node_ref(ClassNodeRef::from_node_ref(node_ref));
            node_ref.ensure_cached_class_infos(i_s);
            return cls2.is_protocol(i_s.db);
        }
        false
    }

    pub fn make_generator_type(
        self,
        db: &Database,
        is_async: bool,
        return_type: impl FnOnce() -> Type,
    ) -> Self {
        if is_async {
            new_class!(
                db.python_state.async_generator_type_link(),
                self,
                Type::None,
            )
        } else {
            new_class!(
                db.python_state.generator_type_link(),
                self,
                Type::None,
                return_type()
            )
        }
    }

    pub fn might_be_string(&self, db: &Database) -> bool {
        self.for_all_in_union(db, &|t| match t {
            Type::LiteralString { .. } => true,
            Type::Literal(literal) => matches!(literal.kind, LiteralKind::String(_)),
            Type::Class(c) => c.link == db.python_state.str_link(),
            _ => false,
        })
    }

    pub fn is_singleton(&self, db: &Database) -> bool {
        self.for_all_in_union(db, &|t| t.is_non_union_singleton())
    }

    pub fn is_non_union_singleton(&self) -> bool {
        matches!(self, Type::Literal(_) | Type::None | Type::EnumMember(_))
    }
}

impl FromIterator<Type> for Type {
    fn from_iter<I: IntoIterator<Item = Type>>(iter: I) -> Self {
        let mut iter = iter.into_iter().peekable();
        let Some(first) = iter.next() else {
            return Type::NEVER;
        };
        if iter.peek().is_some() {
            Type::Union(UnionType::from_types(
                std::iter::once(first).chain(iter),
                true,
            ))
        } else {
            first
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct GenericClass {
    pub link: PointLink,
    pub generics: ClassGenerics,
}

impl GenericClass {
    pub fn class<'a>(&'a self, db: &'a Database) -> Class<'a> {
        Class::from_generic_class_components(db, self.link, &self.generics)
    }

    pub fn node_ref<'db>(&self, db: &'db Database) -> ClassNodeRef<'db> {
        ClassNodeRef::from_link(db, self.link)
    }
}

enum TypeRefIterator<'a, Iter> {
    Single(&'a Type),
    Union(Iter),
    Finished,
}

impl<'a, Iter: Iterator<Item = &'a Type>> Iterator for TypeRefIterator<'a, Iter> {
    type Item = &'a Type;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Single(_) => {
                let Self::Single(type_) = std::mem::replace(self, Self::Finished) else {
                    unreachable!();
                };
                Some(type_)
            }
            Self::Union(items) => items.next(),
            Self::Finished => None,
        }
    }
}

struct RecursiveTypeIterator<'a, Iter> {
    db: &'a Database,
    include_never: bool,
    current_recursive_type: Option<Box<dyn Iterator<Item = &'a Type> + 'a>>,
    types: TypeRefIterator<'a, Iter>,
}

impl<'a, Iter> RecursiveTypeIterator<'a, Iter> {
    fn new(db: &'a Database, include_never: bool, types: TypeRefIterator<'a, Iter>) -> Self {
        Self {
            db,
            include_never,
            current_recursive_type: None,
            types,
        }
    }
}

impl<'a, Iter: Iterator<Item = &'a Type>> Iterator for RecursiveTypeIterator<'a, Iter> {
    type Item = &'a Type;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(rec) = self.current_recursive_type.as_mut()
            && let next @ Some(_) = rec.next()
        {
            return next;
        }
        let next = self.types.next()?;
        if matches!(next, Type::RecursiveType(_)) {
            self.current_recursive_type = Some(Box::new(
                next.iter_with_unpacked_unions_and_maybe_include_never(self.db, self.include_never),
            ));
            self.next()
        } else {
            Some(next)
        }
    }
}

#[derive(Debug)]
pub enum UniqueInUnpackedUnionError {
    None,
    Multiple,
}

#[derive(Debug, PartialEq, Eq, Copy, Clone, Hash)]
pub(crate) enum AnyCause {
    Unannotated,
    Explicit,
    FromError,
    ModuleNotFound,
    TypeVarReplacement,
    Internal,
    UnknownTypeParam,
    UntypedDecorator,
    AsyncCoroutine,
    Todo, // Used for cases where it's currently unclear what the cause should be.
}

#[derive(Debug, PartialEq, Eq, Copy, Clone, Hash)]
pub(crate) enum NeverCause {
    Explicit,
    Other,
}
