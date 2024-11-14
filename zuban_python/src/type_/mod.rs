mod callable;
mod common_base_type;
mod common_sub_type;
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
    cell::OnceCell,
    fmt,
    hash::{Hash, Hasher},
    mem,
    rc::Rc,
};

use parsa_python_cst::{CodeIndex, Expression, Name, PythonString};
use typed_dict::rc_typed_dict_as_callable;

pub(crate) use self::{
    callable::{
        format_callable_params, format_params_as_param_spec, merge_class_type_vars,
        CallableContent, CallableParam, CallableParams, ParamType, ParamTypeDetails, StarParamType,
        StarStarParamType, TypeGuardInfo, WrongPositionalCount,
    },
    dataclass::{
        check_dataclass_options, dataclass_init_func, dataclass_initialize, dataclasses_replace,
        lookup_dataclass_symbol, lookup_on_dataclass, lookup_on_dataclass_type, Dataclass,
        DataclassOptions,
    },
    enum_::{
        execute_functional_enum, infer_value_on_member, lookup_on_enum_class,
        lookup_on_enum_instance, lookup_on_enum_member_instance, Enum, EnumMember,
        EnumMemberDefinition,
    },
    intersection::Intersection,
    lookup_result::LookupResult,
    matching::{match_arbitrary_len_vs_unpack, match_tuple_type_arguments, match_unpack},
    named_tuple::{
        add_named_tuple_param, execute_collections_named_tuple, execute_typing_named_tuple,
        new_collections_named_tuple, new_typing_named_tuple, NamedTuple,
    },
    operations::{execute_type_of_type, IterInfos},
    recursive_type::{RecursiveType, RecursiveTypeOrigin},
    replace::{replace_param_spec, ReplaceSelf},
    tuple::{execute_tuple_class, Tuple, TupleArgs, TupleUnpack, WithUnpack},
    type_var_likes::{
        CallableWithParent, ParamSpec, ParamSpecArg, ParamSpecTypeVars, ParamSpecUsage, TypeVar,
        TypeVarIndex, TypeVarKind, TypeVarLike, TypeVarLikeUsage, TypeVarLikes, TypeVarManager,
        TypeVarName, TypeVarTuple, TypeVarTupleUsage, TypeVarUsage, Variance,
    },
    typed_dict::{
        check_typed_dict_call, infer_typed_dict_item, infer_typed_dict_total_argument,
        initialize_typed_dict, lookup_on_typed_dict, maybe_add_extra_keys_issue, new_typed_dict,
        TypedDict, TypedDictGenerics, TypedDictMember, TypedDictMemberGatherer,
    },
    union::{
        simplified_union_from_iterators, simplified_union_from_iterators_with_format_index,
        UnionEntry, UnionType,
    },
};
use crate::{
    arguments::Args,
    database::{Database, FileIndex, PointLink},
    debug,
    diagnostics::IssueKind,
    file::dotted_path_from_dir,
    format_data::{find_similar_types, AvoidRecursionFor, FormatData},
    inference_state::InferenceState,
    inferred::Inferred,
    matching::{
        ErrorStrs, ErrorTypes, Generic, Generics, GotType, Match, Matcher, MismatchReason,
        OnTypeError, ResultContext,
    },
    node_ref::NodeRef,
    type_helpers::{Class, Instance, MroIterator, TypeOrClass},
    utils::{bytes_repr, join_with_commas, rc_slice_into_vec, str_repr},
    workspaces::Directory,
};

thread_local! {
    static EMPTY_TYPES: Rc<[Type]> = Rc::new([]);
}

pub fn empty_types() -> Rc<[Type]> {
    EMPTY_TYPES.with(|t| t.clone())
}

#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub enum FormatStyle {
    Short,
    MypyRevealType,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct StringSlice {
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

impl fmt::Display for FileIndex {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum DbString {
    StringSlice(StringSlice),
    RcStr(Rc<str>),
    Static(&'static str),
}

impl DbString {
    pub fn as_str<'x>(&'x self, db: &'x Database) -> &'x str {
        match self {
            Self::StringSlice(s) => s.as_str(db),
            Self::RcStr(s) => s,
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
            PythonString::String(code_index, s) => Some(Self::RcStr(s.into())),
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
pub struct TypeArgs {
    pub args: TupleArgs,
}

impl TypeArgs {
    pub fn new(args: TupleArgs) -> Self {
        Self { args }
    }

    pub fn new_fixed_length(args: Rc<[Type]>) -> Self {
        Self::new(TupleArgs::FixedLen(args))
    }

    pub fn new_arbitrary_length(arg: Type) -> Self {
        Self::new(TupleArgs::ArbitraryLen(Box::new(arg)))
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
pub enum GenericItem {
    TypeArg(Type),
    // For TypeVarTuple
    TypeArgs(TypeArgs),
    // For ParamSpec
    ParamSpecArg(ParamSpecArg),
}

impl GenericItem {
    fn is_any(&self) -> bool {
        match self {
            Self::TypeArg(t) => matches!(t, Type::Any(_)),
            Self::TypeArgs(ts) => ts.args.is_any(),
            Self::ParamSpecArg(_) => false,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ClassGenerics {
    List(GenericsList),
    // A class definition (no type vars or stuff like callables)
    ExpressionWithClassType(PointLink),
    // Multiple class definitions, e.g. [int, str], but not [T, str]
    SlicesWithClassTypes(PointLink),
    NotDefinedYet,
    None,
}

impl ClassGenerics {
    pub fn map_list(&self, callable: impl FnOnce(&GenericsList) -> GenericsList) -> Self {
        match self {
            Self::List(list) => Self::List(callable(list)),
            _ => self.clone(),
        }
    }

    pub fn all_any(&self) -> bool {
        match self {
            Self::List(list) => list.iter().all(|g| g.is_any()),
            Self::NotDefinedYet => true,
            _ => false,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct GenericsList(Rc<[GenericItem]>);

impl GenericsList {
    pub fn new_generics(parts: Rc<[GenericItem]>) -> Self {
        Self(parts)
    }

    pub fn generics_from_vec(parts: Vec<GenericItem>) -> Self {
        Self::new_generics(Rc::from(parts))
    }

    pub fn nth(&self, index: TypeVarIndex) -> Option<&GenericItem> {
        self.0.get(index.0 as usize)
    }

    pub fn iter(&self) -> std::slice::Iter<GenericItem> {
        self.0.iter()
    }

    pub fn format(&self, format_data: &FormatData) -> Box<str> {
        join_with_commas(
            self.0
                .iter()
                .filter_map(|g| Generic::new(g).format(format_data).map(|s| s.into())),
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
        rc_slice_into_vec(self.0)
    }

    fn has_any_internal(
        &self,
        i_s: &InferenceState,
        already_checked: &mut Vec<Rc<RecursiveType>>,
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
pub struct Namespace {
    pub directories: Rc<[Rc<Directory>]>,
}

impl Namespace {
    pub fn qualified_name(&self) -> String {
        dotted_path_from_dir(self.directories.first().unwrap())
    }

    pub fn debug_path(&self, db: &Database) -> String {
        join_with_commas(self.directories.iter().map(|d| d.path(&*db.vfs, true)))
    }
}

impl std::cmp::PartialEq for Namespace {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.directories, &other.directories)
    }
}

impl Hash for Namespace {
    fn hash<H: Hasher>(&self, state: &mut H) {
        Rc::as_ptr(&self.directories).hash(state);
    }
}

impl std::cmp::Eq for Namespace {}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FunctionOverload(Box<[Rc<CallableContent>]>);

impl FunctionOverload {
    pub fn new(functions: Box<[Rc<CallableContent>]>) -> Rc<Self> {
        debug_assert!(!functions.is_empty());
        Rc::new(Self(functions))
    }

    pub fn kind(&self) -> FunctionKind {
        self.0[0].kind
    }

    pub fn is_abstract(&self) -> bool {
        self.0[0].is_abstract
    }

    pub fn iter_functions(&self) -> impl Iterator<Item = &Rc<CallableContent>> + Clone {
        self.0.iter()
    }

    pub fn map_functions(
        &self,
        callable: impl FnOnce(&[Rc<CallableContent>]) -> Box<[Rc<CallableContent>]>,
    ) -> Rc<Self> {
        Rc::new(Self(callable(&self.0)))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct GenericClass {
    pub link: PointLink,
    pub generics: ClassGenerics,
}

impl GenericClass {
    pub fn class<'a>(&'a self, db: &'a Database) -> Class<'a> {
        Class::from_generic_class_components(db, self.link, &self.generics)
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

// PartialEq is only here for optimizations, it is not a reliable way to check if a type matches
// with another type.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[allow(clippy::enum_variant_names)]
pub enum Type {
    Class(GenericClass),
    Union(UnionType),
    Intersection(Intersection),
    FunctionOverload(Rc<FunctionOverload>),
    TypeVar(TypeVarUsage),
    Type(Rc<Type>),
    Tuple(Rc<Tuple>),
    Callable(Rc<CallableContent>),
    RecursiveType(Rc<RecursiveType>),
    NewType(Rc<NewType>),
    ParamSpecArgs(ParamSpecUsage),
    ParamSpecKwargs(ParamSpecUsage),
    Literal(Literal),
    Dataclass(Rc<Dataclass>),
    TypedDict(Rc<TypedDict>),
    NamedTuple(Rc<NamedTuple>),
    Enum(Rc<Enum>),
    EnumMember(EnumMember),
    Module(FileIndex),
    Namespace(Rc<Namespace>),
    Super {
        class: Rc<GenericClass>,
        bound_to: Rc<Type>,
        mro_index: usize,
    },
    CustomBehavior(CustomBehavior),
    Self_,
    None,
    Any(AnyCause),
    Never(NeverCause),
}

impl Type {
    pub fn new_class(link: PointLink, generics: ClassGenerics) -> Self {
        Self::Class(GenericClass { link, generics })
    }

    pub fn from_union_entries(entries: Vec<UnionEntry>) -> Self {
        match entries.len() {
            0 => Type::Never(NeverCause::Other),
            1 => entries.into_iter().next().unwrap().type_,
            _ => Type::Union(UnionType::new(entries)),
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

    pub fn maybe_union_like<'x>(&'x self, db: &'x Database) -> Option<Cow<UnionType>> {
        match self {
            Type::Union(u) => Some(Cow::Borrowed(u)),
            Type::Type(t) => t.maybe_union_like(db).map(|u| {
                Cow::Owned(UnionType::new(
                    u.entries
                        .iter()
                        .map(|e| UnionEntry {
                            type_: Type::Type(Rc::new(e.type_.clone())),
                            format_index: e.format_index,
                        })
                        .collect(),
                ))
            }),
            Type::RecursiveType(r) => r.calculated_type(db).maybe_union_like(db),
            _ => None,
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

    fn is_none_or_none_in_union(&self, db: &Database) -> bool {
        self.iter_with_unpacked_unions(db)
            .any(|t| matches!(t, Type::None))
    }

    pub fn is_true_literal(&self) -> bool {
        match self {
            Self::Literal(literal) => matches!(literal.kind, LiteralKind::Bool(true)),
            _ => false,
        }
    }

    pub fn is_object(&self, db: &Database) -> bool {
        match self {
            Self::Class(c) => c.link == db.python_state.object_link(),
            _ => false,
        }
    }

    pub fn remove_none(&self, db: &Database) -> Cow<Type> {
        if self.is_none_or_none_in_union(db) {
            Cow::Owned(Type::from_union_entries(
                self.clone()
                    .into_iter_with_unpacked_unions(db, true)
                    .filter(|union_entry| !matches!(&union_entry.type_, Type::None))
                    .collect(),
            ))
        } else {
            Cow::Borrowed(self)
        }
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
    ) -> impl Iterator<Item = &Type> {
        self.iter_with_unpacked_unions_and_maybe_include_never(db, false)
    }

    pub fn iter_with_unpacked_unions_and_maybe_include_never<'a>(
        &'a self,
        db: &'a Database,
        include_never: bool,
    ) -> impl Iterator<Item = &Type> {
        match self {
            Type::Union(items) => TypeRefIterator::Union(items.iter()),
            Type::Never(_) if !include_never => TypeRefIterator::Finished,
            Type::RecursiveType(rec) => rec
                .calculated_type(db)
                .iter_with_unpacked_unions_and_maybe_include_never(db, include_never),
            t => TypeRefIterator::Single(t),
        }
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
                match new_entries.len() {
                    0 => Type::Never(NeverCause::Other),
                    1 => new_entries.into_iter().next().unwrap().type_,
                    _ => Type::Union(UnionType::new(new_entries)),
                }
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
        Some(match self {
            Type::Class(c) => c.class(i_s.db),
            Type::Dataclass(dc) => dc.class(i_s.db),
            Type::Enum(enum_) => enum_.class(i_s.db),
            Type::EnumMember(member) => member.enum_.class(i_s.db),
            Type::Type(t) => {
                pub fn inner_generic_class_of_type<'db: 'x, 'x>(
                    t: &'x Type,
                    i_s: &InferenceState<'db, 'x>,
                ) -> Option<Class<'x>> {
                    Some(match t {
                        Type::Class(c) => c
                            .class(i_s.db)
                            .use_cached_class_infos(i_s.db)
                            .metaclass(i_s.db),
                        Type::TypeVar(tv) => match &tv.type_var.kind {
                            TypeVarKind::Bound(bound) => {
                                // TODO should this case be handled?
                                bound
                                    .maybe_class(i_s.db)
                                    .unwrap()
                                    .use_cached_class_infos(i_s.db)
                                    .metaclass(i_s.db)
                            }
                            _ => unreachable!(),
                        },
                        Type::Self_ => i_s
                            .current_class()
                            .unwrap()
                            .use_cached_class_infos(i_s.db)
                            .metaclass(i_s.db),
                        _ => return None,
                    })
                }
                return inner_generic_class_of_type(&t, i_s);
            }
            Type::TypeVar(tv) => match &tv.type_var.kind {
                TypeVarKind::Bound(t) => return t.inner_generic_class(i_s),
                _ => return None,
            },
            Type::Self_ => i_s.current_class().unwrap(),
            Type::TypedDict(_) => i_s.db.python_state.typed_dict_class(),
            Type::NewType(n) => return n.type_(i_s).inner_generic_class(i_s),
            _ => return None,
        })
    }

    #[inline]
    pub fn maybe_type_of_class<'a>(&'a self, db: &'a Database) -> Option<Class<'a>> {
        if let Type::Type(t) = self {
            if let Type::Class(c) = t.as_ref() {
                return Some(c.class(db));
            }
        }
        None
    }

    pub fn maybe_typed_dict(&self, db: &Database) -> Option<Rc<TypedDict>> {
        match self {
            Type::TypedDict(td) => Some(td.clone()),
            _ => None,
        }
    }

    pub fn maybe_callable(&self, i_s: &InferenceState) -> Option<CallableLike> {
        match self {
            Type::Callable(c) => Some(CallableLike::Callable(c.clone())),
            Type::Type(t) => t.type_type_maybe_callable(i_s),
            Type::Any(cause) => Some(CallableLike::Callable(Rc::new(CallableContent::new_any(
                i_s.db.python_state.empty_type_var_likes.clone(),
                *cause,
            )))),
            Type::Class(c) => {
                let cls = c.class(i_s.db);
                Instance::new(cls, None)
                    .type_lookup(i_s, |issue| todo!(), "__call__")
                    .into_maybe_inferred()
                    .and_then(|i| i.as_cow_type(i_s).maybe_callable(i_s))
            }
            Type::FunctionOverload(overload) => Some(CallableLike::Overload(overload.clone())),
            Type::TypeVar(t) => match &t.type_var.kind {
                TypeVarKind::Bound(bound) => bound.maybe_callable(i_s),
                _ => None,
            },
            _ => None,
        }
    }

    fn type_type_maybe_callable(&self, i_s: &InferenceState) -> Option<CallableLike> {
        // Is Type[Foo] a callable?
        match self {
            Type::Class(c) => {
                let cls = c.class(i_s.db);
                return cls.find_relevant_constructor(i_s).maybe_callable(i_s, cls);
            }
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
                        init.return_type = Type::Dataclass(Rc::new(type_var_dataclass));
                    }
                    return Some(CallableLike::Callable(Rc::new(init)));
                }
                return cls.find_relevant_constructor(i_s).maybe_callable(i_s, cls);
            }
            Type::TypedDict(td) => Some(CallableLike::Callable(Rc::new(
                rc_typed_dict_as_callable(i_s.db, td.clone()),
            ))),
            Type::NamedTuple(nt) => {
                let mut callable = nt.__new__.remove_first_positional_param().unwrap();
                callable.return_type = self.clone();
                Some(CallableLike::Callable(Rc::new(callable)))
            }
            _ => {
                /*
                if matches!(&c1.params, CallableParams::Any) {
                    c1.return_type.is_super_type_of(
                        i_s,
                        matcher,
                        t2,
                    )
                } else {
                    None
                }
                */
                None
            }
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
        };
        t.sort_for_priority();
        Self::Union(t)
    }

    pub fn union_in_place(&mut self, other: Type) {
        *self = mem::replace(self, Self::Never(NeverCause::Other)).union(other);
    }

    pub fn gather_union(callable: impl FnOnce(&mut dyn FnMut(Self))) -> Self {
        let mut result: Option<Self> = None;
        let r = &mut result;
        callable(&mut |t| {
            *r = Some(match r.take() {
                Some(i) => i.union(t),
                None => t,
            });
        });
        result.unwrap_or_else(|| Type::Never(NeverCause::Other))
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
            Self::Type(type_) => format!("Type[{}]", type_.format(format_data)).into(),
            Self::Tuple(content) => content.format(format_data),
            Self::Callable(content) => content.format(format_data).into(),
            Self::Any(_) => Box::from("Any"),
            Self::None => Box::from("None"),
            Self::Never(_) => Box::from("Never"),
            Self::Literal(literal) => literal.format(format_data),
            Self::NewType(n) => n.format(format_data),
            Self::RecursiveType(rec) => {
                if let Some(generics) = &rec.generics {
                    if format_data.style != FormatStyle::MypyRevealType {
                        return format!(
                            "{}[{}]",
                            rec.name(format_data.db),
                            generics.format(format_data)
                        )
                        .into();
                    }
                }

                if rec.calculating(format_data.db) {
                    // Happens only in weird cases like MRO calculation and will probably mostly
                    // appear when debugging.
                    return rec.name(format_data.db).into();
                }

                let avoid = AvoidRecursionFor::RecursiveType(rec);
                match format_data.with_seen_recursive_type(avoid) {
                    Ok(format_data) => rec.calculated_type(format_data.db).format(&format_data),
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
                        Generics::NotDefinedYet,
                    )
                }
                _ => nt.format_with_name(
                    format_data,
                    &nt.qualified_name(format_data.db),
                    Generics::NotDefinedYet,
                ),
            },
            Self::Enum(e) => e.format(format_data).into(),
            Self::EnumMember(e) => e.format(format_data).into(),
            Self::Module(file_index) => format_data
                .db
                .python_state
                .module_type()
                .format(format_data),
            Self::Intersection(intersection) => intersection.format(format_data),
            Self::Namespace(_) => "ModuleType".into(),
            Self::Super { .. } => "super".into(),
            Self::CustomBehavior(_) => "TODO custombehavior".into(),
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
            | Self::Enum(_)
            | Self::EnumMember(_)
            | Self::NewType(_) => (),
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
            Self::Dataclass(d) => match &d.class.generics {
                ClassGenerics::List(generics) => generics.search_type_vars(found_type_var),
                _ => (),
            },
            Self::TypedDict(d) => d.search_type_vars(found_type_var),
            Self::NamedTuple(_) => {
                debug!("TODO do we need to support namedtuple searching for type vars?");
            }
            Self::Intersection(i) => {
                for t in i.iter_entries() {
                    t.search_type_vars(found_type_var)
                }
            }
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
        already_checked: &mut Vec<Rc<RecursiveType>>,
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
            Self::TypeVar(t) => false,
            Self::Type(type_) => type_.has_any_internal(i_s, already_checked),
            Self::Tuple(content) => content.args.has_any_internal(i_s, already_checked),
            Self::Callable(content) => content.has_any_internal(i_s, already_checked),
            Self::None | Self::Never(_) | Self::Literal { .. } => false,
            Self::Any(_) => true,
            Self::NewType(n) => n.type_(i_s).has_any(i_s),
            Self::RecursiveType(recursive_alias) => {
                if let Some(generics) = &recursive_alias.generics {
                    if generics.has_any_internal(i_s, already_checked) {
                        return true;
                    }
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
            Self::ParamSpecArgs(_)
            | Self::ParamSpecKwargs(_)
            | Self::Module(_)
            | Self::Enum(_)
            | Self::CustomBehavior(_)
            | Self::Namespace(_) => false,
            Self::Dataclass(d) => search_in_generic_class(&d.class),
            Self::TypedDict(d) => d.has_any_internal(i_s, already_checked),
            Self::NamedTuple(nt) => nt.__new__.has_any_internal(i_s, already_checked),
            Self::EnumMember(_) => false,
            Self::Super { .. } => false,
            Self::Intersection(intersection) => intersection
                .iter_entries()
                .any(|t| t.has_any_internal(i_s, already_checked)),
        }
    }

    pub fn has_self_type(&self, db: &Database) -> bool {
        self.find_in_type(db, &mut |t| matches!(t, Type::Self_))
    }

    pub fn find_in_type(&self, db: &Database, check: &mut impl FnMut(&Type) -> bool) -> bool {
        match self {
            Self::Class(c) => {
                check(self)
                    || Generics::from_class_generics(db, &c.generics)
                        .iter(db)
                        .any(|generic| generic.find_in_type(db, check))
            }
            Self::Union(u) => u.iter().any(|t| t.find_in_type(db, check)),
            Self::FunctionOverload(intersection) => intersection
                .iter_functions()
                .any(|c| c.find_in_type(db, check)),
            Self::Type(t) => check(self) || t.find_in_type(db, check),
            Self::Tuple(tup) => tup.find_in_type(db, check),
            Self::Callable(content) => check(self) || content.find_in_type(db, check),
            Self::TypedDict(d) => {
                check(self)
                    || match &d.generics {
                        TypedDictGenerics::Generics(gs) => {
                            gs.iter().any(|g| Generic::new(g).find_in_type(db, check))
                        }
                        TypedDictGenerics::None | TypedDictGenerics::NotDefinedYet(_) => false,
                    }
            }
            _ => check(self),
        }
    }

    pub fn has_never_from_inference(&self, db: &Database) -> bool {
        self.find_in_type(db, &mut |t| match t {
            Type::Never(NeverCause::Inference) => true,
            Type::Callable(c) => matches!(c.params, CallableParams::Never(NeverCause::Inference)),
            Type::Class(c) => match &c.generics {
                ClassGenerics::List(list) => list.iter().any(|g| {
                    matches!(
                        g,
                        GenericItem::ParamSpecArg(ParamSpecArg {
                            params: CallableParams::Never(NeverCause::Inference),
                            ..
                        })
                    )
                }),
                _ => false,
            },
            _ => false,
        })
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
            Type::EnumMember(m) if m.implicit => Some(Type::Enum(m.enum_.clone())),
            Type::Tuple(tup) => {
                if let TupleArgs::FixedLen(ts) = &tup.args {
                    if ts
                        .iter()
                        .any(|t| t.maybe_avoid_implicit_literal(db).is_some())
                    {
                        let mut gathered = vec![];
                        for t in ts.iter() {
                            if let Some(new_t) = t.maybe_avoid_implicit_literal(db) {
                                gathered.push(new_t);
                                continue;
                            }
                            gathered.push(t.clone())
                        }
                        return Some(Type::Tuple(Tuple::new_fixed_length(gathered.into())));
                    }
                }
                None
            }
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
                        return Some(Type::Union(UnionType::new(gathered)));
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
            Type::TypedDict(td) => MroIterator::new(
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
            Type::RecursiveType(r) if !r.calculating(db) => {
                let mut mro = r.calculated_type(db).mro(db);
                mro.class = Some(TypeOrClass::Type(Cow::Borrowed(self)));
                mro
            }
            _ => MroIterator::new(
                db,
                TypeOrClass::Type(Cow::Borrowed(self)),
                Generics::None,
                [].iter(),
                false,
            ),
        }
    }

    pub fn find_class_in_mro<'x>(&'x self, db: &'x Database, target: NodeRef) -> Option<Class> {
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
        add_issue: impl Fn(IssueKind),
        mut on_error: impl FnMut(&ErrorTypes) -> Option<IssueKind>,
    ) {
        self.error_if_not_matches_with_matcher(
            i_s,
            &mut Matcher::default(),
            value,
            add_issue,
            |error_types, reason: &MismatchReason| on_error(error_types),
        );
    }

    pub(crate) fn error_if_not_matches_with_matcher(
        &self,
        i_s: &InferenceState,
        matcher: &mut Matcher,
        value: &Inferred,
        add_issue: impl Fn(IssueKind),
        mut on_error: impl FnMut(&ErrorTypes, &MismatchReason) -> Option<IssueKind>,
    ) {
        let value_type = value.as_cow_type(i_s);
        let matches = self.is_super_type_of(i_s, matcher, &value_type);
        if let Match::False { ref reason, .. } = matches {
            let error_types = ErrorTypes {
                expected: self,
                got: GotType::Type(&value_type),
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
                add_issue(error);
                error_types.add_mismatch_notes(add_issue)
            }
        }
    }

    pub fn on_any_typed_dict(
        &self,
        i_s: &InferenceState,
        matcher: &mut Matcher,
        callable: &mut impl FnMut(&mut Matcher, Rc<TypedDict>) -> bool,
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
    ) -> Option<T> {
        let found = self
            .find_unique_type_in_unpacked_union(db, matcher, find)
            .ok()?;
        Some(on_unique_found(matcher, found))
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
        let merge_generics = |g1: &ClassGenerics, g2: &ClassGenerics| {
            if matches!(g1, ClassGenerics::None) {
                return ClassGenerics::None;
            }
            ClassGenerics::List(GenericsList::new_generics(
                // Performance issue: clone could probably be removed. Rc -> Vec check
                // https://github.com/rust-lang/rust/issues/93610#issuecomment-1528108612
                Generics::from_class_generics(db, g1)
                    .iter(db)
                    .zip(Generics::from_class_generics(db, g2).iter(db))
                    .map(|(gi1, gi2)| gi1.merge_matching_parts(db, gi2))
                    .collect(),
            ))
        };
        match self {
            Type::Class(c1) => match other {
                Type::Class(c2) if c1.link == c2.link => {
                    Type::new_class(c1.link, merge_generics(&c1.generics, &c2.generics))
                }
                _ => Type::Any(AnyCause::FromError),
            },
            Type::Union(u1) => match other {
                Type::Union(u2) if u1.iter().all(|x| u2.iter().any(|y| x == y)) => {
                    Type::Union(u1.clone())
                }
                _ => Type::Any(AnyCause::FromError),
            },
            Type::Tuple(c1) => match other {
                Type::Tuple(c2) => {
                    Type::Tuple(Tuple::new(c1.args.merge_matching_parts(db, &c2.args)))
                }
                _ => Type::Any(AnyCause::FromError),
            },
            Type::Callable(content1) => match other {
                Type::Callable(content2) => {
                    Type::Callable(db.python_state.any_callable_from_error.clone())
                }
                _ => Type::Any(AnyCause::FromError),
            },
            _ => Type::Any(AnyCause::FromError),
        }
    }

    pub fn maybe_fixed_len_tuple(&self) -> Option<&[Type]> {
        if let Type::Tuple(tup) = self {
            if let TupleArgs::FixedLen(ts) = &tup.args {
                return Some(ts);
            }
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
                        if let Some(cls) = base.as_maybe_class() {
                            if cls.node_ref == db.python_state.container_node_ref() {
                                result.union_in_place(cls.nth_type_argument(db, 0));
                            }
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FunctionKind {
    Function {
        had_first_self_or_class_annotation: bool,
    },
    Property {
        had_first_self_or_class_annotation: bool,
        writable: bool,
    },
    Classmethod {
        had_first_self_or_class_annotation: bool,
    },
    Staticmethod,
}

impl FunctionKind {
    pub fn is_same_base_kind(self, other: Self) -> bool {
        matches!(
            (self, other),
            (Self::Function { .. }, Self::Function { .. })
                | (Self::Property { .. }, Self::Property { .. })
                | (Self::Classmethod { .. }, Self::Classmethod { .. })
                | (Self::Staticmethod, Self::Staticmethod)
        )
    }

    pub fn had_first_self_or_class_annotation(self) -> bool {
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
            } => had_first_self_or_class_annotation,
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
pub struct NewType {
    pub name_string: PointLink,
    type_expression: PointLink,
    // TODO locality needs to be checked, because this is lazily calculated.
    type_: OnceCell<Type>,
}

impl NewType {
    pub fn new(name_string: PointLink, type_expression: PointLink) -> Self {
        Self {
            name_string,
            type_expression,
            type_: OnceCell::new(),
        }
    }

    pub fn type_(&self, i_s: &InferenceState) -> &Type {
        self.type_.get_or_init(|| {
            let t =
                NodeRef::from_link(i_s.db, self.type_expression).compute_new_type_constraint(i_s);
            t
        })
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
        self.type_expression == other.type_expression
    }
}

impl Hash for NewType {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.type_expression.hash(state);
    }
}

#[derive(Debug, Clone, Eq)]
pub struct Literal {
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
pub enum LiteralKind {
    String(DbString),
    Int(i64), // TODO this does not work for Python ints > usize
    Bytes(PointLink),
    Bool(bool),
}

#[derive(PartialEq, Eq, Debug)]
pub enum LiteralValue<'db> {
    String(&'db str),
    Int(i64),
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

    pub fn value<'x>(&'x self, db: &'x Database) -> LiteralValue<'x> {
        match &self.kind {
            LiteralKind::Int(i) => LiteralValue::Int(*i),
            LiteralKind::String(s) => LiteralValue::String(s.as_str(db)),
            LiteralKind::Bool(b) => LiteralValue::Bool(*b),
            LiteralKind::Bytes(link) => {
                let node_ref = NodeRef::from_link(db, *link);
                LiteralValue::Bytes(node_ref.as_bytes_literal().content_as_bytes())
            }
        }
    }

    fn format_inner(&self, db: &Database) -> Cow<str> {
        match self.value(db) {
            LiteralValue::String(s) => Cow::Owned(str_repr(s)),
            LiteralValue::Int(i) => Cow::Owned(format!("{i}")),
            LiteralValue::Bool(true) => Cow::Borrowed("True"),
            LiteralValue::Bool(false) => Cow::Borrowed("False"),
            LiteralValue::Bytes(b) => Cow::Owned(bytes_repr(b)),
        }
    }

    pub fn fallback_node_ref<'db>(&self, db: &'db Database) -> NodeRef<'db> {
        match &self.kind {
            LiteralKind::Int(_) => db.python_state.int_node_ref(),
            LiteralKind::String(_) => db.python_state.str_node_ref(),
            LiteralKind::Bool(_) => db.python_state.bool_node_ref(),
            LiteralKind::Bytes(_) => db.python_state.bytes_node_ref(),
        }
    }

    pub fn as_instance<'db>(&self, db: &'db Database) -> Instance<'db> {
        Instance::new(
            Class::from_non_generic_node_ref(self.fallback_node_ref(db)),
            None,
        )
    }

    pub fn fallback_type(&self, db: &Database) -> Type {
        Type::new_class(self.fallback_node_ref(db).as_link(), ClassGenerics::None)
    }

    pub fn format(&self, format_data: &FormatData) -> Box<str> {
        let question_mark = match format_data.style {
            FormatStyle::MypyRevealType if self.implicit => "?",
            _ if self.implicit && format_data.hide_implicit_literals => {
                return self.fallback_type(format_data.db).format(format_data)
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

type CustomBehaviorCallback = for<'db> fn(
    i_s: &InferenceState<'db, '_>,
    args: &dyn Args<'db>,
    result_context: &mut ResultContext,
    on_type_error: OnTypeError,
    bound: Option<&Type>,
) -> Inferred;

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum CustomBehaviorKind {
    Function,
    Method { bound: Option<Rc<Type>> },
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct CustomBehavior {
    callback: CustomBehaviorCallback,
    kind: CustomBehaviorKind,
}

impl CustomBehavior {
    pub(crate) fn new_function(callback: CustomBehaviorCallback) -> Self {
        Self {
            callback,
            kind: CustomBehaviorKind::Function,
        }
    }

    pub(crate) fn new_method(callback: CustomBehaviorCallback, bound: Option<Rc<Type>>) -> Self {
        Self {
            callback,
            kind: CustomBehaviorKind::Method { bound },
        }
    }

    pub fn bind(&self, bound: Rc<Type>) -> Self {
        Self {
            callback: self.callback,
            kind: match self.kind {
                CustomBehaviorKind::Method { bound: None } => {
                    CustomBehaviorKind::Method { bound: Some(bound) }
                }
                _ => self.kind.clone(),
            },
        }
    }

    pub(crate) fn execute<'db>(
        &self,
        i_s: &InferenceState<'db, '_>,
        args: &dyn Args<'db>,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError,
    ) -> Inferred {
        let bound = match &self.kind {
            CustomBehaviorKind::Function => None,
            CustomBehaviorKind::Method { bound } => bound.as_deref(),
        };
        (self.callback)(i_s, args, result_context, on_type_error, bound)
    }
}

#[derive(Debug)]
pub enum CallableLike {
    Callable(Rc<CallableContent>),
    Overload(Rc<FunctionOverload>),
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
enum UniqueInUnpackedUnionError {
    None,
    Multiple,
}

impl PartialEq for AnyCause {
    fn eq(&self, other: &Self) -> bool {
        true
    }
}

#[derive(Debug, Eq, Copy, Clone, Hash)]
pub enum AnyCause {
    Unannotated,
    Explicit,
    FromError,
    ModuleNotFound,
    Internal,
    Todo, // Used for cases where it's currently unclear what the cause should be.
}

#[derive(Debug, Eq, Copy, Clone, Hash)]
pub enum NeverCause {
    Explicit,
    Inference,
    Other,
}

impl PartialEq for NeverCause {
    fn eq(&self, other: &Self) -> bool {
        true
    }
}
