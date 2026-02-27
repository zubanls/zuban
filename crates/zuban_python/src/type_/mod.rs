mod callable;
mod common_base_type;
mod common_sub_type;
mod custom_behavior;
mod dataclass;
mod enum_;
mod intersection;
mod lookup_result;
mod matching;
mod named_tuple;
mod operations;
mod overlaps;
mod recursive_type;
mod replace;
mod tuple;
mod type_var_likes;
mod typed_dict;
mod union;
mod utils;

use std::{
    borrow::Cow,
    cell::Cell,
    hash::{Hash, Hasher},
    mem,
    sync::Arc,
};

use parsa_python_cst::{CodeIndex, Expression, Name, PythonString};
use typed_dict::rc_typed_dict_as_callable;
use vfs::{Directory, FileIndex};

pub(crate) use self::{
    callable::{
        CallableContent, CallableParam, CallableParams, ParamType, ParamTypeDetails, StarParamType,
        StarStarParamType, TypeGuardInfo, WrongPositionalCount, add_any_params_to_params,
        add_param_spec_to_params, format_callable_params, format_params_as_param_spec,
        merge_class_type_vars,
    },
    custom_behavior::CustomBehavior,
    dataclass::{
        Dataclass, DataclassOptions, DataclassTransformObj, dataclass_converter_fields_lookup,
        dataclass_init_func, dataclass_initialize, dataclass_post_init_func, dataclasses_replace,
        ensure_calculated_dataclass, lookup_dataclass_symbol, lookup_on_dataclass,
        lookup_on_dataclass_type,
    },
    enum_::{
        Enum, EnumKind, EnumMember, EnumMemberAlias, EnumMemberDefinition, lookup_on_enum_class,
        lookup_on_enum_instance, lookup_on_enum_member_instance,
    },
    intersection::Intersection,
    lookup_result::LookupResult,
    matching::{match_arbitrary_len_vs_unpack, match_tuple_type_arguments, match_unpack},
    named_tuple::NamedTuple,
    operations::{IterCause, IterInfos, execute_type_of_type},
    recursive_type::{RecursiveType, RecursiveTypeOrigin},
    replace::{ReplaceSelf, ReplaceTypeVarLikes, replace_param_spec},
    tuple::{MaybeUnpackGatherer, Tuple, TupleArgs, TupleUnpack, WithUnpack, execute_tuple_class},
    type_var_likes::{
        CallableWithParent, ParamSpec, ParamSpecArg, ParamSpecTypeVars, ParamSpecUsage,
        TypeLikeInTypeVar, TypeVar, TypeVarIndex, TypeVarKind, TypeVarKindInfos, TypeVarLike,
        TypeVarLikeName, TypeVarLikeUsage, TypeVarLikes, TypeVarManager, TypeVarName, TypeVarTuple,
        TypeVarTupleUsage, TypeVarUsage, TypeVarVariance, Variance,
    },
    typed_dict::{
        ExtraItemsType, TypedDict, TypedDictGenerics, TypedDictMember, TypedDictMembers,
        check_typed_dict_call, infer_typed_dict_arg, initialize_typed_dict, lookup_on_typed_dict,
        maybe_add_extra_keys_issue,
    },
    union::{UnionEntry, UnionType, simplified_union_from_iterators_with_format_index},
};
use crate::{
    database::{Database, PointLink},
    debug,
    diagnostics::IssueKind,
    file::{ClassNodeRef, dotted_path_from_dir},
    format_data::{AvoidRecursionFor, FormatData, find_similar_types},
    inference_state::InferenceState,
    inferred::Inferred,
    match_::{Match, MismatchReason},
    matching::{ErrorStrs, ErrorTypes, Generic, Generics, GotType, Matcher},
    new_class,
    node_ref::NodeRef,
    recoverable_error,
    type_helpers::{Class, Instance, MroIterator, TypeOrClass},
    utils::{arc_slice_into_vec, bytes_repr, join_with_commas, str_repr},
};

thread_local! {
    static EMPTY_TYPES: Arc<[Type]> = Arc::new([]);
}

pub(crate) fn empty_types() -> Arc<[Type]> {
    EMPTY_TYPES.with(|t| t.clone())
}

#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub(crate) enum FormatStyle {
    Short,
    MypyRevealType,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct StringSlice {
    pub file_index: FileIndex,
    pub start: CodeIndex,
    pub end: CodeIndex,
}

impl StringSlice {
    pub fn from_string_in_expression(file_index: FileIndex, expr: Expression) -> Option<Self> {
        if let Some(literal) = expr.maybe_single_string_literal() {
            let (start, end) = literal.content_start_and_end_in_literal();
            let s = literal.start();
            Some(Self::new(file_index, s + start, s + end))
        } else {
            None
        }
    }

    pub fn from_name(file_index: FileIndex, name: Name) -> Self {
        Self::new(file_index, name.start(), name.end())
    }

    pub fn new(file_index: FileIndex, start: CodeIndex, end: u32) -> Self {
        Self {
            file_index,
            start,
            end,
        }
    }

    pub fn as_str(self, db: &Database) -> &str {
        let file = db.loaded_python_file(self.file_index);
        &file.tree.code()[self.start as usize..self.end as usize]
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum DbString {
    StringSlice(StringSlice),
    ArcStr(Arc<str>),
    Static(&'static str),
}

impl DbString {
    pub fn as_str<'x>(&'x self, db: &'x Database) -> &'x str {
        match self {
            Self::StringSlice(s) => s.as_str(db),
            Self::ArcStr(s) => s,
            Self::Static(s) => s,
        }
    }

    pub fn from_python_string(file_index: FileIndex, python_string: PythonString) -> Option<Self> {
        match python_string {
            PythonString::Ref(code_index, s) => Some(Self::StringSlice(StringSlice::new(
                file_index,
                code_index,
                code_index + s.len() as CodeIndex,
            ))),
            PythonString::String(_, s) => Some(Self::ArcStr(s.into())),
            PythonString::FString => None,
        }
    }
}

impl From<StringSlice> for DbString {
    fn from(item: StringSlice) -> Self {
        Self::StringSlice(item)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct TypeArgs {
    pub args: TupleArgs,
}

impl TypeArgs {
    pub fn new(args: TupleArgs) -> Self {
        Self { args }
    }

    pub fn new_arbitrary_from_error() -> Self {
        TypeArgs {
            args: TupleArgs::new_arbitrary_from_error(),
        }
    }

    pub fn new_arbitrary_length(arg: Type) -> Self {
        Self::new(TupleArgs::ArbitraryLen(Arc::new(arg)))
    }

    pub fn format(&self, format_data: &FormatData) -> Option<Box<str>> {
        let result = self.args.format(format_data);
        if matches!(self.args, TupleArgs::ArbitraryLen(_)) {
            Some(format!("Unpack[Tuple[{result}]]").into())
        } else {
            (!self.args.is_empty()).then_some(result)
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum GenericItem {
    TypeArg(Type),
    // For TypeVarTuple
    TypeArgs(TypeArgs),
    // For ParamSpec
    ParamSpecArg(ParamSpecArg),
}

impl GenericItem {
    fn maybe_any(&self) -> Option<AnyCause> {
        match self {
            Self::TypeArg(Type::Any(cause)) => Some(*cause),
            Self::TypeArg(_) => None,
            Self::TypeArgs(ts) => ts.args.maybe_any(),
            Self::ParamSpecArg(p) => match p.params {
                CallableParams::Any(cause) => Some(cause),
                _ => None,
            },
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum ClassGenerics {
    List(GenericsList),
    // A class definition (no type vars or stuff like callables)
    ExpressionWithClassType(PointLink),
    // Multiple class definitions, e.g. [int, str], but not [T, str]
    SlicesWithClassTypes(PointLink),
    NotDefinedYet,
    None { might_be_promoted: bool },
}

impl ClassGenerics {
    pub const fn new_none() -> Self {
        Self::None {
            might_be_promoted: true,
        }
    }

    pub fn all_any(&self) -> bool {
        match self {
            Self::List(list) => list.iter().all(|g| g.maybe_any().is_some()),
            Self::NotDefinedYet => true,
            _ => false,
        }
    }

    pub fn all_any_with_unknown_type_params(&self) -> bool {
        match self {
            Self::List(list) => list
                .iter()
                .all(|g| g.maybe_any() == Some(AnyCause::UnknownTypeParam)),
            _ => false,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct GenericsList(Arc<[GenericItem]>);

impl GenericsList {
    pub fn new_generics(parts: Arc<[GenericItem]>) -> Self {
        debug_assert!(!parts.is_empty());
        Self(parts)
    }

    pub fn generics_from_vec(parts: Vec<GenericItem>) -> Self {
        Self::new_generics(Arc::from(parts))
    }

    pub fn nth(&self, index: TypeVarIndex) -> Option<&GenericItem> {
        self.0.get(index.0 as usize)
    }

    pub fn iter(&self) -> std::slice::Iter<'_, GenericItem> {
        self.0.iter()
    }

    pub fn format(&self, format_data: &FormatData) -> Box<str> {
        join_with_commas(
            self.0
                .iter()
                .filter_map(|g| Generic::new(g).format(format_data)),
        )
        .into()
    }

    pub fn has_param_spec(&self) -> bool {
        self.iter()
            .any(|g| matches!(g, GenericItem::ParamSpecArg(_)))
    }

    fn search_type_vars<C: FnMut(TypeVarLikeUsage) + ?Sized>(&self, found_type_var: &mut C) {
        for g in self.iter() {
            match g {
                GenericItem::TypeArg(t) => t.search_type_vars(found_type_var),
                GenericItem::TypeArgs(ts) => ts.args.search_type_vars(found_type_var),
                GenericItem::ParamSpecArg(p) => p.params.search_type_vars(found_type_var),
            }
        }
    }

    pub fn has_type_vars(&self) -> bool {
        let mut result = false;
        self.search_type_vars(&mut |_| result = true);
        result
    }

    pub fn into_vec(self) -> Vec<GenericItem> {
        arc_slice_into_vec(self.0)
    }

    fn has_any_internal(
        &self,
        i_s: &InferenceState,
        already_checked: &mut Vec<Arc<RecursiveType>>,
    ) -> bool {
        self.iter().any(|g| match g {
            GenericItem::TypeArg(t) => t.has_any_internal(i_s, already_checked),
            GenericItem::TypeArgs(ts) => ts.args.has_any_internal(i_s, already_checked),
            GenericItem::ParamSpecArg(a) => a.params.has_any_internal(i_s, already_checked),
        })
    }
}

impl std::ops::Index<TypeVarIndex> for GenericsList {
    type Output = GenericItem;

    fn index(&self, index: TypeVarIndex) -> &Self::Output {
        &self.0[index.0 as usize]
    }
}

#[derive(Debug, Clone)]
pub(crate) struct Namespace {
    pub directories: Arc<[Arc<Directory>]>,
}

impl Namespace {
    pub fn qualified_name(&self) -> String {
        dotted_path_from_dir(self.directories.first().unwrap())
    }

    pub fn debug_path(&self, db: &Database) -> String {
        join_with_commas(
            self.directories
                .iter()
                .map(|d| d.absolute_path(&*db.vfs.handler).path().to_string()),
        )
    }
}

impl std::cmp::PartialEq for Namespace {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.directories, &other.directories)
    }
}

impl Hash for Namespace {
    fn hash<H: Hasher>(&self, state: &mut H) {
        Arc::as_ptr(&self.directories).hash(state);
    }
}

impl std::cmp::Eq for Namespace {}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct FunctionOverload(Box<[Arc<CallableContent>]>);

impl FunctionOverload {
    pub fn new(functions: Box<[Arc<CallableContent>]>) -> Arc<Self> {
        debug_assert!(!functions.is_empty());
        Arc::new(Self(functions))
    }

    pub fn kind(&self) -> &FunctionKind {
        &self.0[0].kind
    }

    pub fn is_abstract(&self) -> bool {
        self.0[0].is_abstract
    }

    pub fn iter_functions(&self) -> impl Iterator<Item = &Arc<CallableContent>> + Clone {
        self.0.iter()
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

enum TypeIterator<Iter> {
    Single(Type),
    Union(Iter),
    Finished,
}

impl<Iter: Iterator<Item = UnionEntry>> Iterator for TypeIterator<Iter> {
    type Item = UnionEntry;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Single(_) => {
                let Self::Single(type_) = std::mem::replace(self, Self::Finished) else {
                    unreachable!();
                };
                Some(UnionEntry {
                    format_index: 0,
                    type_,
                })
            }
            Self::Union(items) => items.next(),
            Self::Finished => None,
        }
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

// PartialEq is only here for optimizations, it is not a reliable way to check if a type matches
// with another type.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[allow(clippy::enum_variant_names)]
pub(crate) enum Type {
    Class(GenericClass),
    Union(UnionType),
    Intersection(Intersection),
    FunctionOverload(Arc<FunctionOverload>),
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
    Any(AnyCause),
    Never(NeverCause),
}

impl Type {
    pub fn new_class(link: PointLink, generics: ClassGenerics) -> Self {
        Self::Class(GenericClass { link, generics })
    }

    pub const ERROR: Self = Self::Any(AnyCause::FromError);
    pub const NEVER: Self = Self::Never(NeverCause::Other);

    pub fn from_union_entries(
        entries: Vec<UnionEntry>,
        might_have_defined_type_vars: bool,
    ) -> Self {
        match entries.len() {
            0 => Type::Never(NeverCause::Other),
            1 => entries.into_iter().next().unwrap().type_,
            _ => {
                let mut union = UnionType::new(entries, might_have_defined_type_vars);
                union.sort_for_priority();
                Type::Union(union)
            }
        }
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
                Cow::Owned(UnionType::new(
                    u.entries
                        .iter()
                        .map(|e| UnionEntry {
                            type_: Type::Type(Arc::new(e.type_.clone())),
                            format_index: e.format_index,
                        })
                        .collect(),
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

    pub fn maybe_remove_none(&self, db: &Database) -> Option<Type> {
        if self.is_none_or_none_in_union(db) {
            let might_have_defined_type_vars = match self {
                Type::Union(u) => u.might_have_type_vars,
                Type::None => false,
                _ => true,
            };
            Some(Type::from_union_entries(
                self.clone()
                    .into_iter_with_unpacked_unions(db, true)
                    .filter(|union_entry| !matches!(&union_entry.type_, Type::None))
                    .collect(),
                might_have_defined_type_vars,
            ))
        } else {
            None
        }
    }

    pub fn remove_none(&self, db: &Database) -> Cow<'_, Type> {
        self.maybe_remove_none(db)
            .map(Cow::Owned)
            .unwrap_or(Cow::Borrowed(self))
    }

    pub fn into_iter_with_unpacked_unions(
        self,
        db: &Database,
        unpack_recursive_type: bool,
    ) -> impl Iterator<Item = UnionEntry> {
        match self {
            Type::Union(items) => TypeIterator::Union(items.entries.into_vec().into_iter()),
            Type::Never(_) => TypeIterator::Finished,
            Type::RecursiveType(rec) if unpack_recursive_type => rec
                .calculated_type(db)
                .clone()
                .into_iter_with_unpacked_unions(db, unpack_recursive_type),
            t => TypeIterator::Single(t),
        }
    }

    pub fn valid_in_type_form_assignment(&self, db: &Database) -> bool {
        self.iter_with_unpacked_unions(db)
            .all(|t| matches!(t, Type::TypeForm(_) | Type::Type(_) | Type::None))
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

    pub fn retain_in_union(&self, mut maybe_retain: impl FnMut(&Self) -> bool) -> Type {
        match self {
            Type::Union(union) => {
                let mut new_entries = vec![];
                for entry in union.entries.iter() {
                    if maybe_retain(&entry.type_) {
                        new_entries.push(entry.clone())
                    }
                }
                Self::from_union_entries(new_entries, union.might_have_type_vars)
            }
            Type::Never(cause) => Type::Never(*cause),
            t => {
                if maybe_retain(t) {
                    t.clone()
                } else {
                    Type::Never(NeverCause::Other)
                }
            }
        }
    }

    pub fn for_all_in_union(&self, db: &Database, callback: &impl Fn(&Type) -> bool) -> bool {
        self.iter_with_unpacked_unions(db).all(|t| match t {
            Type::Intersection(intersection) => intersection.iter_entries().any(callback),
            _ => callback(t),
        })
    }

    pub fn highest_union_format_index(&self) -> usize {
        match self {
            Type::Union(items) => items.entries.iter().map(|e| e.format_index).max().unwrap(),
            Type::Never(_) => 0,
            _ => 1,
        }
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
                t.inner_generic_class(i_s)?
                    .use_cached_class_infos(i_s.db)
                    .metaclass(i_s.db),
            ),
            _ => self.inner_generic_class_with_db(i_s.db),
        }
    }

    pub fn inner_generic_class_with_db<'x>(&'x self, db: &'x Database) -> Option<Class<'x>> {
        Some(match self {
            Type::Class(c) => c.class(db),
            Type::Dataclass(dc) => dc.class(db),
            Type::Enum(enum_) => enum_.class(db),
            Type::EnumMember(member) => member.enum_.class(db),
            Type::Literal(l) => l.fallback_class(db),
            Type::LiteralString { .. } => db.python_state.str_class(),
            Type::Type(t) => t
                .inner_generic_class_with_db(db)?
                .use_cached_class_infos(db)
                .metaclass(db),
            Type::TypeVar(tv) => match tv.type_var.kind(db) {
                TypeVarKind::Bound(t) => return t.inner_generic_class_with_db(db),
                _ => return None,
            },
            Type::TypedDict(_) => db.python_state.typed_dict_class(),
            Type::NewType(n) => return n.type_.inner_generic_class_with_db(db),
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
        match self {
            Type::Callable(c) => Some(CallableLike::Callable(c.clone())),
            Type::Type(t) => t.type_type_maybe_callable(i_s),
            Type::Any(cause) => Some(CallableLike::Callable(Arc::new(CallableContent::new_any(
                i_s.db.python_state.empty_type_var_likes.clone(),
                *cause,
            )))),
            Type::Class(c) => {
                let cls = c.class(i_s.db);
                let had_issue = Cell::new(false);
                Instance::new(cls, None)
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
            }
            Type::FunctionOverload(overload) => Some(CallableLike::Overload(overload.clone())),
            Type::TypeVar(t) => match t.type_var.kind(i_s.db) {
                TypeVarKind::Bound(bound) => bound.maybe_callable(i_s),
                _ => None,
            },
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
                if d.options.init {
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

    pub fn make_optional(&mut self) {
        *self = mem::replace(self, Self::Never(NeverCause::Other)).union(Type::None);
    }

    pub fn union(self, other: Self) -> Self {
        let entries = match self {
            Self::Union(u1) => {
                let mut vec = u1.entries.into_vec();
                match other {
                    Self::Union(u2) => {
                        for mut o in u2.entries.into_vec().into_iter() {
                            if !vec.iter().any(|e| e.type_ == o.type_) {
                                o.format_index = vec.len();
                                vec.push(o);
                            }
                        }
                    }
                    Type::Never(_) => (), // `X | Never is always X`
                    _ => {
                        if !vec.iter().any(|t| t.type_ == other) {
                            vec.push(UnionEntry {
                                type_: other,
                                format_index: vec.len(),
                            })
                        }
                    }
                };
                vec
            }
            Self::Never(_) => return other,
            _ => match other {
                Self::Union(u) => {
                    if u.iter().any(|t| t == &self) {
                        return Self::Union(u);
                    } else {
                        let mut vec = u.entries.into_vec();
                        vec.push(UnionEntry {
                            type_: self,
                            format_index: vec.len(),
                        });
                        vec
                    }
                }
                _ => {
                    if self == other || matches!(other, Type::Never(_)) {
                        return self;
                    } else {
                        vec![
                            UnionEntry {
                                type_: self,
                                format_index: 0,
                            },
                            UnionEntry {
                                type_: other,
                                format_index: 1,
                            },
                        ]
                    }
                }
            },
        };
        let mut t = UnionType {
            entries: entries.into_boxed_slice(),
            // TODO should we calculate this?
            might_have_type_vars: true,
        };
        t.sort_for_priority();
        Self::Union(t)
    }

    pub fn union_in_place(&mut self, other: Type) {
        *self = mem::replace(self, Self::Never(NeverCause::Other)).union(other);
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
            Self::TypeForm(t) => format!("typing.TypeForm({})", t.format(format_data)).into(),
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

    pub fn has_any(&self, i_s: &InferenceState) -> bool {
        self.has_any_internal(i_s, &mut Vec::new())
    }

    fn has_any_internal(
        &self,
        i_s: &InferenceState,
        already_checked: &mut Vec<Arc<RecursiveType>>,
    ) -> bool {
        let mut search_in_generic_class = |c: &GenericClass| match &c.generics {
            ClassGenerics::List(generics) => generics.has_any_internal(i_s, already_checked),
            _ => false,
        };
        match self {
            Self::Class(c) => search_in_generic_class(c),
            Self::Union(u) => u.iter().any(|t| t.has_any_internal(i_s, already_checked)),
            Self::FunctionOverload(intersection) => intersection
                .iter_functions()
                .any(|callable| callable.has_any_internal(i_s, already_checked)),
            Self::Type(type_) => type_.has_any_internal(i_s, already_checked),
            Self::Tuple(content) => content.args.has_any_internal(i_s, already_checked),
            Self::Callable(content) => content.has_any_internal(i_s, already_checked),
            Self::Any(_) => true,
            Self::NewType(n) => n.type_.has_any_internal(i_s, already_checked),
            Self::RecursiveType(recursive_alias) => {
                if let Some(generics) = &recursive_alias.generics
                    && generics.has_any_internal(i_s, already_checked)
                {
                    return true;
                }
                if already_checked.contains(recursive_alias) {
                    false
                } else {
                    already_checked.push(recursive_alias.clone());
                    match recursive_alias.origin(i_s.db) {
                        RecursiveTypeOrigin::TypeAlias(type_alias) => {
                            !type_alias.calculating()
                                && type_alias
                                    .type_if_valid()
                                    .has_any_internal(i_s, already_checked)
                        }
                        RecursiveTypeOrigin::Class(_) => false,
                    }
                }
            }
            Self::Self_ => {
                debug!("TODO Self could contain Any?");
                false
            }
            Self::TypeVar(tv) => match &tv.type_var.kind(i_s.db) {
                TypeVarKind::Bound(bound) => bound.has_any_internal(i_s, already_checked),
                TypeVarKind::Unrestricted | TypeVarKind::Constraints(_) => false,
            },
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
            | Self::LiteralString { .. } => false,
            Self::Dataclass(d) => search_in_generic_class(&d.class),
            Self::TypedDict(d) => d.has_any_internal(i_s, already_checked),
            Self::NamedTuple(nt) => nt.__new__.has_any_internal(i_s, already_checked),
            Self::Intersection(intersection) => intersection
                .iter_entries()
                .any(|t| t.has_any_internal(i_s, already_checked)),
            Self::TypeForm(tf) => tf.has_any_internal(i_s, already_checked),
        }
    }

    pub fn has_self_type(&self, db: &Database) -> bool {
        self.find_in_type(db, &mut |t| matches!(t, Type::Self_))
    }

    pub fn find_in_type(&self, db: &Database, check: &mut impl FnMut(&Type) -> bool) -> bool {
        if check(self) {
            return true;
        }
        match self {
            Self::Class(c) => {
                Generics::from_class_generics(db, ClassNodeRef::from_link(db, c.link), &c.generics)
                    .iter(db)
                    .any(|generic| generic.find_in_type(db, check))
            }
            Self::Union(u) => u.iter().any(|t| t.find_in_type(db, check)),
            Self::FunctionOverload(intersection) => intersection
                .iter_functions()
                .any(|c| c.find_in_type(db, check)),
            Self::Type(t) => t.find_in_type(db, check),
            Self::Tuple(tup) => tup.find_in_type(db, check),
            Self::Callable(content) => content.find_in_type(db, check),
            Self::TypedDict(d) => match &d.generics {
                TypedDictGenerics::Generics(gs) => {
                    gs.iter().any(|g| Generic::new(g).find_in_type(db, check))
                }
                TypedDictGenerics::None | TypedDictGenerics::NotDefinedYet(_) => false,
            },
            _ => false,
        }
    }

    pub fn has_any_with_unknown_type_params(&self, db: &Database) -> bool {
        self.find_in_type(db, &mut |t| match t {
            Type::Any(AnyCause::UnknownTypeParam) => true,
            Type::Callable(c) => {
                matches!(c.params, CallableParams::Any(AnyCause::UnknownTypeParam))
            }
            Type::Class(c) => match &c.generics {
                ClassGenerics::List(list) => list.iter().any(|g| {
                    matches!(
                        g,
                        GenericItem::ParamSpecArg(ParamSpecArg {
                            params: CallableParams::Any(AnyCause::UnknownTypeParam),
                            ..
                        })
                    )
                }),
                _ => false,
            },
            _ => false,
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
                    let mut gathered: Vec<UnionEntry> = vec![];
                    for entry in union.entries.iter() {
                        if let Some(type_) = entry.type_.maybe_avoid_implicit_literal(db) {
                            if !gathered.iter().any(|e| e.type_ == type_) {
                                gathered.push(UnionEntry {
                                    type_,
                                    format_index: entry.format_index,
                                });
                            }
                        } else if !gathered.iter().any(|e| e.type_ == entry.type_) {
                            gathered.push(entry.clone())
                        }
                    }
                    if gathered.len() == 1 {
                        return Some(gathered.into_iter().next().unwrap().type_);
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
            Type::Class(c) => c.class(db).mro(db),
            Type::Tuple(tup) => {
                let tuple_class = tup.class(db);
                MroIterator::new(
                    db,
                    TypeOrClass::Type(Cow::Borrowed(self)),
                    tuple_class.generics,
                    tuple_class.use_cached_class_infos(db).mro.iter(),
                    false,
                )
            }
            Type::Dataclass(d) => {
                let mut mro = d.class(db).mro(db);
                mro.class = Some(TypeOrClass::Type(Cow::Borrowed(self)));
                mro
            }
            Type::TypedDict(_) => MroIterator::new(
                db,
                TypeOrClass::Type(Cow::Borrowed(self)),
                Generics::None,
                db.python_state.typing_typed_dict_bases.iter(),
                false,
            ),
            Type::Enum(e) | Type::EnumMember(EnumMember { enum_: e, .. }) => {
                let class = e.class(db);
                MroIterator::new(
                    db,
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

    pub(crate) fn error_if_not_matches(
        &self,
        i_s: &InferenceState,
        value: &Inferred,
        add_issue: impl Fn(IssueKind) -> bool,
        mut on_error: impl FnMut(&ErrorTypes) -> Option<IssueKind>,
    ) {
        self.error_if_not_matches_with_matcher(
            i_s,
            &mut Matcher::default(),
            value,
            add_issue,
            |error_types, _reason: &MismatchReason| on_error(error_types),
        );
    }

    pub(crate) fn error_if_not_matches_with_matcher(
        &self,
        i_s: &InferenceState,
        matcher: &mut Matcher,
        value: &Inferred,
        add_issue: impl Fn(IssueKind) -> bool,
        on_error: impl FnMut(&ErrorTypes, &MismatchReason) -> Option<IssueKind>,
    ) {
        let value_type = value.as_cow_type(i_s);
        self.error_if_t_not_matches_with_matcher(i_s, matcher, &value_type, add_issue, on_error);
    }

    pub(crate) fn error_if_t_not_matches_with_matcher(
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
            Type::Union(u1) => match other {
                Type::Union(u2) if u1.iter().all(|x| u2.iter().any(|y| x == y)) => {
                    Type::Union(u1.clone())
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

    pub fn container_types(&self, db: &Database) -> Option<Type> {
        let mut result = Type::Never(NeverCause::Other);
        for t in self.iter_with_unpacked_unions(db) {
            match t {
                Type::Tuple(tup) => result.union_in_place(tup.fallback_type(db).clone()),
                Type::NamedTuple(named_tup) => {
                    result.union_in_place(named_tup.as_tuple_ref().fallback_type(db).clone())
                }
                _ => {
                    for (_, base) in t.mro(db) {
                        if let Some(cls) = base.maybe_class()
                            && cls.node_ref == db.python_state.container_node_ref()
                        {
                            result.union_in_place(cls.nth_type_argument(db, 0));
                        }
                    }
                }
            }
        }
        if matches!(result, Type::Never(NeverCause::Other)) {
            None
        } else {
            Some(result)
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
            new_class!(db.python_state.async_generator_link(), self, Type::None,)
        } else {
            new_class!(
                db.python_state.generator_link(),
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
        self.for_all_in_union(db, &|t| {
            matches!(t, Type::Literal(_) | Type::None | Type::EnumMember(_))
        })
    }
}

impl FromIterator<Type> for Type {
    fn from_iter<I: IntoIterator<Item = Type>>(iter: I) -> Self {
        let mut result = Type::Never(NeverCause::Other);
        for t in iter {
            result.union_in_place(t)
        }
        result
    }
}

impl Tuple {
    pub fn maybe_avoid_implicit_literal(&self, db: &Database) -> Option<Arc<Self>> {
        if let TupleArgs::FixedLen(ts) = &self.args
            && ts
                .iter()
                .any(|t| t.maybe_avoid_implicit_literal(db).is_some())
        {
            let mut gathered = vec![];
            for t in ts.iter() {
                gathered.push(
                    t.maybe_avoid_implicit_literal(db)
                        .unwrap_or_else(|| t.clone()),
                )
            }
            return Some(Tuple::new_fixed_length(gathered.into()));
        }
        None
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum PropertySetterType {
    SameTypeFromCachedProperty, // This happens when @functools.cached_property is used
    OtherType(Type),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct PropertySetter {
    pub type_: PropertySetterType,
    pub deprecated_reason: Option<Arc<Box<str>>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum FunctionKind {
    Function {
        had_first_self_or_class_annotation: bool,
    },
    Property {
        had_first_self_or_class_annotation: bool,
        setter_type: Option<Arc<PropertySetter>>,
    },
    Classmethod {
        had_first_self_or_class_annotation: bool,
    },
    Staticmethod,
}

impl FunctionKind {
    pub fn is_same_base_kind(&self, other: &Self) -> bool {
        matches!(
            (self, other),
            (Self::Function { .. }, Self::Function { .. })
                | (Self::Property { .. }, Self::Property { .. })
                | (Self::Classmethod { .. }, Self::Classmethod { .. })
                | (Self::Staticmethod, Self::Staticmethod)
        )
    }

    pub fn had_first_self_or_class_annotation(&self) -> bool {
        match self {
            Self::Function {
                had_first_self_or_class_annotation,
            }
            | Self::Property {
                had_first_self_or_class_annotation,
                ..
            }
            | Self::Classmethod {
                had_first_self_or_class_annotation,
            } => *had_first_self_or_class_annotation,
            Self::Staticmethod => true,
        }
    }

    pub fn update_had_first_self_or_class_annotation(&mut self, new_value: bool) {
        match self {
            Self::Function {
                had_first_self_or_class_annotation,
            }
            | Self::Property {
                had_first_self_or_class_annotation,
                ..
            }
            | Self::Classmethod {
                had_first_self_or_class_annotation,
            } => *had_first_self_or_class_annotation = new_value,
            Self::Staticmethod => (),
        }
    }
}

#[derive(Debug, Clone, Eq)]
pub(crate) struct NewType {
    pub name_node: PointLink,
    pub name_string: PointLink,
    pub type_: Type,
}

impl NewType {
    pub fn new(name_node: PointLink, name_string: PointLink, type_: Type) -> Self {
        Self {
            name_node,
            name_string,
            type_,
        }
    }

    pub fn format(&self, format_data: &FormatData) -> Box<str> {
        match format_data.style {
            FormatStyle::Short if !format_data.should_format_qualified(self.name_string) => {
                self.name(format_data.db).into()
            }
            _ => self.qualified_name(format_data.db),
        }
    }

    pub fn name<'db>(&self, db: &'db Database) -> &'db str {
        NodeRef::from_link(db, self.name_string)
            .maybe_str()
            .unwrap()
            .content()
    }

    pub fn qualified_name(&self, db: &Database) -> Box<str> {
        let node_ref = NodeRef::from_link(db, self.name_string);
        format!(
            "{}.{}",
            node_ref.file.qualified_name(db),
            node_ref.maybe_str().unwrap().content()
        )
        .into()
    }
}

impl PartialEq for NewType {
    fn eq(&self, other: &Self) -> bool {
        self.name_string == other.name_string
    }
}

impl Hash for NewType {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.name_string.hash(state);
    }
}

#[derive(Debug, Clone, Eq)]
pub(crate) struct Literal {
    pub kind: LiteralKind,
    pub implicit: bool,
}

impl std::cmp::PartialEq for Literal {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind
    }
}

impl Hash for Literal {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.kind.hash(state);
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum LiteralKind {
    String(DbString),
    Int(num_bigint::BigInt),
    Bytes(DbBytes),
    Bool(bool),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum DbBytes {
    Link(PointLink),
    Static(&'static [u8]),
    Arc(Arc<[u8]>),
}

#[derive(PartialEq, Eq, Debug)]
pub(crate) enum LiteralValue<'db> {
    String(&'db str),
    Int(&'db num_bigint::BigInt),
    Bytes(Cow<'db, [u8]>),
    Bool(bool),
}

impl Literal {
    pub fn new(kind: LiteralKind) -> Self {
        Self {
            kind,
            implicit: false,
        }
    }

    pub fn new_implicit(kind: LiteralKind) -> Self {
        Self {
            kind,
            implicit: true,
        }
    }

    pub fn value<'x>(&'x self, db: &'x Database) -> LiteralValue<'x> {
        match &self.kind {
            LiteralKind::Int(i) => LiteralValue::Int(i),
            LiteralKind::String(s) => LiteralValue::String(s.as_str(db)),
            LiteralKind::Bool(b) => LiteralValue::Bool(*b),
            LiteralKind::Bytes(b) => match b {
                DbBytes::Link(link) => {
                    let node_ref = NodeRef::from_link(db, *link);
                    LiteralValue::Bytes(node_ref.expect_bytes_literal().content_as_bytes())
                }
                DbBytes::Static(b) => LiteralValue::Bytes(Cow::Borrowed(b)),
                DbBytes::Arc(b) => LiteralValue::Bytes(Cow::Borrowed(b)),
            },
        }
    }

    fn format_inner(&self, db: &Database) -> Cow<'_, str> {
        match self.value(db) {
            LiteralValue::String(s) => Cow::Owned(str_repr(s)),
            LiteralValue::Int(i) => Cow::Owned(format!("{i}")),
            LiteralValue::Bool(true) => Cow::Borrowed("True"),
            LiteralValue::Bool(false) => Cow::Borrowed("False"),
            LiteralValue::Bytes(b) => Cow::Owned(bytes_repr(b)),
        }
    }

    pub fn fallback_node_ref<'db>(&self, db: &'db Database) -> ClassNodeRef<'db> {
        match &self.kind {
            LiteralKind::Int(_) => db.python_state.int_node_ref(),
            LiteralKind::String(_) => db.python_state.str_node_ref(),
            LiteralKind::Bool(_) => db.python_state.bool_node_ref(),
            LiteralKind::Bytes(_) => db.python_state.bytes_node_ref(),
        }
    }

    pub fn fallback_class<'db>(&self, db: &'db Database) -> Class<'db> {
        Class::from_non_generic_node_ref(self.fallback_node_ref(db))
    }

    pub fn as_instance<'db>(&self, db: &'db Database) -> Instance<'db> {
        Instance::new(
            Class::from_non_generic_node_ref(self.fallback_node_ref(db)),
            None,
        )
    }

    pub fn fallback_type(&self, db: &Database) -> Type {
        Type::new_class(
            self.fallback_node_ref(db).as_link(),
            ClassGenerics::new_none(),
        )
    }

    pub fn format(&self, format_data: &FormatData) -> Box<str> {
        let question_mark = match format_data.style {
            FormatStyle::MypyRevealType if self.implicit => "?",
            _ if self.implicit && format_data.hide_implicit_literals => {
                return self.fallback_type(format_data.db).format(format_data);
            }
            _ => "",
        };
        format!(
            "Literal[{}]{}",
            self.format_inner(format_data.db),
            question_mark
        )
        .into()
    }
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub(crate) enum CallableLike {
    Callable(Arc<CallableContent>),
    Overload(Arc<FunctionOverload>),
}

impl CallableLike {
    pub fn format(&self, format_data: &FormatData) -> String {
        match self {
            Self::Callable(c) => c.format(format_data),
            Self::Overload(overload) => format!(
                "Overload({})",
                join_with_commas(overload.iter_functions().map(|c| c.format(format_data)))
            ),
        }
    }

    pub fn is_typed(&self, skip_first_param: bool) -> bool {
        match self {
            Self::Callable(c) => c.is_typed(skip_first_param),
            Self::Overload(overload) => overload
                .iter_functions()
                .all(|c| c.is_typed(skip_first_param)),
        }
    }

    pub fn is_typed_and_annotated_result(&self, db: &Database) -> bool {
        match self {
            Self::Callable(c) => c.is_typed_and_annotated_result(db),
            Self::Overload(overload) => overload
                .iter_functions()
                .all(|c| c.is_typed_and_annotated_result(db)),
        }
    }

    pub fn had_first_self_or_class_annotation(&self) -> bool {
        match self {
            Self::Callable(c) => c.kind.had_first_self_or_class_annotation(),
            Self::Overload(o) => o.kind().had_first_self_or_class_annotation(),
        }
    }
}

impl From<CallableLike> for Type {
    fn from(callable: CallableLike) -> Self {
        match callable {
            CallableLike::Callable(c) => Type::Callable(c),
            CallableLike::Overload(o) => Type::FunctionOverload(o),
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
    Todo, // Used for cases where it's currently unclear what the cause should be.
}

#[derive(Debug, PartialEq, Eq, Copy, Clone, Hash)]
pub(crate) enum NeverCause {
    Explicit,
    Other,
}
