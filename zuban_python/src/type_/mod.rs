mod callable;
mod common_base_type;
mod common_sub_type;
mod dataclass;
mod enum_;
mod matching;
mod named_tuple;
mod operations;
mod recursive_type;
mod replace;
mod tuple;
mod type_var_likes;
mod typed_dict;
mod union;
mod utils;

use std::{borrow::Cow, cell::OnceCell, fmt, mem, rc::Rc};

pub use common_base_type::{common_base_type, common_base_type_of_type_var_tuple_with_items};
pub use matching::match_tuple_type_arguments;
pub(crate) use named_tuple::{
    execute_collections_named_tuple, execute_typing_named_tuple, new_collections_named_tuple,
    new_typing_named_tuple, NamedTuple,
};
use parsa_python_ast::{CodeIndex, Expression, Name, PythonString};
pub use replace::ReplaceSelf;
pub use tuple::{Tuple, TupleTypeArguments};
pub use type_var_likes::{
    CallableWithParent, ParamSpec, ParamSpecArgument, ParamSpecTypeVars, ParamSpecUsage, TypeVar,
    TypeVarIndex, TypeVarKind, TypeVarLike, TypeVarLikeUsage, TypeVarLikes, TypeVarManager,
    TypeVarName, TypeVarTuple, TypeVarTupleUsage, TypeVarUsage, Variance,
};

pub(crate) use self::{
    callable::{
        format_callable_params, CallableContent, CallableParam, CallableParams, ParamType,
        StarParamType, StarStarParamType, WrongPositionalCount,
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
    operations::execute_type_of_type,
    recursive_type::{RecursiveType, RecursiveTypeOrigin},
    typed_dict::{
        check_typed_dict_call, infer_typed_dict_item, infer_typed_dict_total_argument,
        initialize_typed_dict, lookup_on_typed_dict, maybe_add_extra_keys_issue, new_typed_dict,
        TypedDict, TypedDictGenerics, TypedDictMember, TypedDictMemberGatherer,
    },
    union::{simplified_union_from_iterators, UnionEntry, UnionType},
};
use crate::{
    arguments::Arguments,
    database::{Database, FileIndex, PointLink},
    debug,
    diagnostics::IssueType,
    inference_state::InferenceState,
    inferred::Inferred,
    matching::{
        maybe_class_usage, AvoidRecursionFor, CalculatedTypeArguments, ErrorStrs, ErrorTypes,
        FormatData, Generic, Generics, GotType, Match, Matcher, MismatchReason, OnTypeError,
        ParamsStyle, ResultContext,
    },
    node_ref::NodeRef,
    type_helpers::{dotted_path_from_dir, Class, Instance, MroIterator, TypeOrClass},
    utils::{bytes_repr, join_with_commas, str_repr},
    workspaces::Directory,
};

#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub enum FormatStyle {
    Short,
    Qualified,
    MypyRevealType,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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

#[derive(Debug, Clone, PartialEq, Eq)]
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

#[derive(Debug, Clone, PartialEq)]
pub struct TypeArguments {
    pub args: TupleTypeArguments,
}

impl TypeArguments {
    pub fn new_fixed_length(args: Rc<[TypeOrTypeVarTuple]>) -> Self {
        Self {
            args: TupleTypeArguments::FixedLength(args),
        }
    }

    pub fn new_arbitrary_length(arg: Type) -> Self {
        Self {
            args: TupleTypeArguments::ArbitraryLength(Box::new(arg)),
        }
    }

    pub fn format(&self, format_data: &FormatData) -> Box<str> {
        self.args.format(format_data)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum GenericItem {
    TypeArgument(Type),
    // For TypeVarTuple
    TypeArguments(TypeArguments),
    // For ParamSpec
    ParamSpecArgument(ParamSpecArgument),
}

impl GenericItem {
    fn is_any(&self) -> bool {
        match self {
            Self::TypeArgument(t) => matches!(t, Type::Any(_)),
            Self::TypeArguments(ts) => ts.args.is_any(),
            Self::ParamSpecArgument(_) => false,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
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

#[derive(Debug, Clone, PartialEq)]
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
                .map(|g| Generic::new(g).format(format_data).into()),
        )
        .into()
    }

    fn search_type_vars<C: FnMut(TypeVarLikeUsage)>(&self, found_type_var: &mut C) {
        for g in self.iter() {
            match g {
                GenericItem::TypeArgument(t) => t.search_type_vars(found_type_var),
                GenericItem::TypeArguments(_) => todo!(),
                GenericItem::ParamSpecArgument(p) => p.params.search_type_vars(found_type_var),
            }
        }
    }

    pub fn has_type_vars(&self) -> bool {
        let mut result = false;
        self.search_type_vars(&mut |_| result = true);
        result
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
    pub path: String,
    pub content: Rc<Directory>,
}

impl Namespace {
    pub fn qualified_name(&self) -> String {
        dotted_path_from_dir(&self.content)
    }
}

impl std::cmp::PartialEq for Namespace {
    fn eq(&self, other: &Self) -> bool {
        self.path == other.path && Rc::ptr_eq(&self.content, &other.content)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct FunctionOverload(Box<[CallableContent]>);

impl FunctionOverload {
    pub fn new(functions: Box<[CallableContent]>) -> Rc<Self> {
        debug_assert!(!functions.is_empty());
        Rc::new(Self(functions))
    }

    pub fn kind(&self) -> FunctionKind {
        self.0[0].kind
    }

    pub fn iter_functions(&self) -> impl Iterator<Item = &CallableContent> {
        self.0.iter()
    }

    pub fn map_functions(
        &self,
        callable: impl FnOnce(&[CallableContent]) -> Box<[CallableContent]>,
    ) -> Rc<Self> {
        Rc::new(Self(callable(&self.0)))
    }
}

#[derive(Debug, Clone, PartialEq)]
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
#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Class(GenericClass),
    Union(UnionType),
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
        mro_index: usize,
    },
    CustomBehavior(CustomBehavior),
    Self_,
    None,
    Any(AnyCause),
    Never,
}

impl Type {
    pub fn new_class(link: PointLink, generics: ClassGenerics) -> Self {
        Self::Class(GenericClass { link, generics })
    }

    pub fn is_union_like(&self) -> bool {
        match self {
            Type::Union(_) => true,
            Type::Type(t) if t.as_ref().is_union_like() => true,
            _ => false,
        }
    }

    pub fn is_any(&self) -> bool {
        matches!(self, Type::Any(_))
    }

    pub fn into_iter_with_unpacked_unions(self) -> impl Iterator<Item = UnionEntry> {
        match self {
            Type::Union(items) => TypeIterator::Union(items.entries.into_vec().into_iter()),
            Type::Never => TypeIterator::Finished,
            t => TypeIterator::Single(t),
        }
    }

    pub fn iter_with_unpacked_unions(&self) -> impl Iterator<Item = &Type> {
        match self {
            Type::Union(items) => TypeRefIterator::Union(items.iter()),
            Type::Never => TypeRefIterator::Finished,
            t => TypeRefIterator::Single(t),
        }
    }

    pub fn highest_union_format_index(&self) -> usize {
        match self {
            Type::Union(items) => items.entries.iter().map(|e| e.format_index).max().unwrap(),
            Type::Never => 0,
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
            Type::Type(t) => match t.as_ref() {
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
                            init.return_type = t.as_ref().clone();
                        } else {
                            let mut type_var_dataclass = (**d).clone();
                            type_var_dataclass.class =
                                Class::with_self_generics(i_s.db, cls.node_ref)
                                    .as_generic_class(i_s.db);
                            init.return_type = Type::Dataclass(Rc::new(type_var_dataclass));
                        }
                        return Some(CallableLike::Callable(Rc::new(init)));
                    }
                    return cls.find_relevant_constructor(i_s).maybe_callable(i_s, cls);
                }
                Type::TypedDict(_) => {
                    todo!("Once this is implemented remove the reveal_type formatting")
                }
                Type::NamedTuple(nt) => {
                    let mut callable = nt.__new__.remove_first_param().unwrap();
                    callable.return_type = (**t).clone();
                    return Some(CallableLike::Callable(Rc::new(callable)));
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
            },
            Type::Any(cause) => Some(CallableLike::Callable(Rc::new(CallableContent::new_any(
                i_s.db.python_state.empty_type_var_likes.clone(),
                *cause,
            )))),
            Type::Class(c) => {
                let cls = c.class(i_s.db);
                debug!("TODO this from is completely wrong and should never be used.");
                let hack = cls.node_ref;
                Instance::new(cls, None)
                    .type_lookup(i_s, hack, "__call__")
                    .into_maybe_inferred()
                    .and_then(|i| i.as_cow_type(i_s).maybe_callable(i_s))
            }
            Type::FunctionOverload(overload) => Some(CallableLike::Overload(overload.clone())),
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

    pub fn union(self, db: &Database, other: Type) -> Self {
        self.union_with_details(db, other, false)
    }

    pub fn make_optional(&mut self, db: &Database) {
        *self = mem::replace(self, Self::Never).union_with_details(db, Type::None, true);
    }

    pub fn union_with_details(
        self,
        db: &Database,
        other: Type,
        mut format_as_optional: bool,
    ) -> Self {
        let entries = match self {
            Self::Union(u1) => {
                let mut vec = u1.entries.into_vec();
                match other {
                    Self::Union(u2) => {
                        format_as_optional |= u2.format_as_optional;
                        for mut o in u2.entries.into_vec().into_iter() {
                            if !vec.iter().any(|e| e.type_ == o.type_) {
                                o.format_index = vec.len();
                                vec.push(o);
                            }
                        }
                    }
                    Type::Never => (), // `X | Never is always X`
                    _ => {
                        if !vec.iter().any(|t| t.type_ == other) {
                            vec.push(UnionEntry {
                                type_: other,
                                format_index: vec.len(),
                            })
                        }
                    }
                };
                format_as_optional |= u1.format_as_optional;
                vec
            }
            Self::Never => return other,
            _ => match other {
                Self::Union(u) => {
                    format_as_optional |= u.format_as_optional;
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
                    if self == other || matches!(other, Type::Never) {
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
            format_as_optional,
        };
        t.sort_for_priority();
        Self::Union(t)
    }

    pub fn union_in_place(&mut self, db: &Database, other: Type) {
        *self = mem::replace(self, Self::Never).union(db, other);
    }

    pub fn format_short(&self, db: &Database) -> Box<str> {
        self.format(&FormatData::new_short(db))
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
            Self::TypeVar(t) => format_data.format_type_var_like(
                &TypeVarLikeUsage::TypeVar(Cow::Borrowed(t)),
                ParamsStyle::Unreachable,
            ),
            Self::Type(type_) => format!("Type[{}]", type_.format(format_data)).into(),
            Self::Tuple(content) => content.format(format_data),
            Self::Callable(content) => content.format(format_data).into(),
            Self::Any(_) => Box::from("Any"),
            Self::None => Box::from("None"),
            Self::Never => Box::from("Never"),
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

                let avoid = AvoidRecursionFor::RecursiveType(rec);
                if format_data.has_already_seen_recursive_type(avoid) {
                    if format_data.style == FormatStyle::MypyRevealType {
                        "...".into()
                    } else {
                        rec.name(format_data.db).into()
                    }
                } else {
                    let format_data = format_data.with_seen_recursive_type(avoid);
                    rec.calculated_type(format_data.db).format(&format_data)
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
                FormatStyle::Short => nt.format_with_name(
                    format_data,
                    nt.name(format_data.db),
                    Generics::NotDefinedYet,
                ),
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
            Self::Namespace(_) => "object".into(),
            Self::Super { .. } => "TODO super".into(),
            Self::CustomBehavior(_) => "TODO custombehavior".into(),
        }
    }

    pub fn expect_class_generics(&self) -> &GenericsList {
        match self {
            Self::Class(GenericClass {
                generics: ClassGenerics::List(generics),
                ..
            }) => generics,
            Self::Dataclass(d) => match &d.class.generics {
                ClassGenerics::List(generics) => generics,
                _ => unreachable!(),
            },
            Self::TypedDict(d) => todo!("Maybe this should be implemented?"),
            // If we expect class generics and tuples are involved, the tuple was already
            // calculated.
            Self::Tuple(t) => t.tuple_class_generics.get().unwrap(),
            Self::NamedTuple(nt) => nt.as_tuple_ref().tuple_class_generics.get().unwrap(),
            _ => unreachable!(),
        }
    }

    pub fn search_type_vars<C: FnMut(TypeVarLikeUsage)>(&self, found_type_var: &mut C) {
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
                    callable.params.search_type_vars(found_type_var);
                    callable.return_type.search_type_vars(found_type_var)
                }
            }
            Self::TypeVar(t) => found_type_var(TypeVarLikeUsage::TypeVar(Cow::Borrowed(t))),
            Self::Type(type_) => type_.search_type_vars(found_type_var),
            Self::Tuple(content) => match &content.args {
                TupleTypeArguments::FixedLength(ts) => {
                    for t in ts.iter() {
                        match t {
                            TypeOrTypeVarTuple::Type(t) => t.search_type_vars(found_type_var),
                            TypeOrTypeVarTuple::TypeVarTuple(t) => {
                                found_type_var(TypeVarLikeUsage::TypeVarTuple(Cow::Borrowed(t)))
                            }
                        }
                    }
                }
                TupleTypeArguments::ArbitraryLength(t) => t.search_type_vars(found_type_var),
            },
            Self::Callable(content) => {
                content.params.search_type_vars(found_type_var);
                content.return_type.search_type_vars(found_type_var)
            }
            Self::Class(..)
            | Self::Any(_)
            | Self::None
            | Self::Never
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
            Self::ParamSpecArgs(usage) => todo!(),
            Self::ParamSpecKwargs(usage) => todo!(),
            Self::Dataclass(d) => match &d.class.generics {
                ClassGenerics::List(generics) => generics.search_type_vars(found_type_var),
                _ => (),
            },
            Self::TypedDict(d) => {
                if let TypedDictGenerics::Generics(list) = &d.generics {
                    list.search_type_vars(found_type_var)
                }

                /*
                 * TODO is this necessary?
                for member in d.members().iter() {
                    member.type_.search_type_vars(found_type_var);
                }
                */
            }
            Self::NamedTuple(_) => {
                debug!("TODO do we need to support namedtuple searching for type vars?");
            }
        }
    }

    fn has_type_vars(&self) -> bool {
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
        let search_in_generics = |generics: &GenericsList, already_checked: &mut _| {
            generics.iter().any(|g| match g {
                GenericItem::TypeArgument(t) => t.has_any_internal(i_s, already_checked),
                GenericItem::TypeArguments(_) => todo!(),
                GenericItem::ParamSpecArgument(a) => {
                    a.params.has_any_internal(i_s, already_checked)
                }
            })
        };
        match self {
            Self::Class(GenericClass {
                generics: ClassGenerics::List(generics),
                ..
            }) => search_in_generics(generics, already_checked),
            Self::Class(GenericClass {
                generics: ClassGenerics::NotDefinedYet,
                ..
            }) => false,
            Self::Union(u) => u.iter().any(|t| t.has_any_internal(i_s, already_checked)),
            Self::FunctionOverload(intersection) => intersection
                .iter_functions()
                .any(|callable| callable.has_any_internal(i_s, already_checked)),
            Self::TypeVar(t) => false,
            Self::Type(type_) => type_.has_any_internal(i_s, already_checked),
            Self::Tuple(content) => content.args.has_any_internal(i_s, already_checked),
            Self::Callable(content) => content.has_any_internal(i_s, already_checked),
            Self::Class(GenericClass {
                generics:
                    ClassGenerics::None
                    | ClassGenerics::ExpressionWithClassType(_)
                    | ClassGenerics::SlicesWithClassTypes(_),
                ..
            })
            | Self::None
            | Self::Never
            | Self::Literal { .. } => false,
            Self::Any(_) => true,
            Self::NewType(n) => n.type_(i_s).has_any(i_s),
            Self::RecursiveType(recursive_alias) => {
                if let Some(generics) = &recursive_alias.generics {
                    if search_in_generics(generics, already_checked) {
                        return true;
                    }
                }
                if already_checked.contains(recursive_alias) {
                    false
                } else {
                    already_checked.push(recursive_alias.clone());
                    match recursive_alias.origin(i_s.db) {
                        RecursiveTypeOrigin::TypeAlias(type_alias) => type_alias
                            .type_if_valid()
                            .has_any_internal(i_s, already_checked),
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
            Self::Dataclass(d) => match &d.class.generics {
                ClassGenerics::List(generics) => search_in_generics(generics, already_checked),
                ClassGenerics::NotDefinedYet => todo!(),
                _ => false,
            },
            Self::TypedDict(d) => {
                debug!("TODO this should not be ");
                d.members(i_s.db)
                    .iter()
                    .any(|m| m.type_.has_any_internal(i_s, already_checked))
            }
            Self::NamedTuple(nt) => nt.__new__.has_any_internal(i_s, already_checked),
            Self::EnumMember(_) => todo!(),
            Self::Super { .. } => todo!(),
        }
    }

    fn is_self_type(&self) -> bool {
        match self {
            Self::Self_ => true,
            Self::Dataclass(_) => todo!(),
            Self::NamedTuple(_) => {
                debug!("TODO namedtuple has_self_type");
                false
            }
            _ => false,
        }
    }

    pub fn has_self_type(&self) -> bool {
        self.find_in_type(&Self::is_self_type)
    }

    pub fn find_in_type(&self, check: &impl Fn(&Type) -> bool) -> bool {
        let check_generics_list = |generics: &GenericsList| {
            generics.iter().any(|g| match g {
                GenericItem::TypeArgument(t) => check(t),
                GenericItem::TypeArguments(ts) => match &ts.args {
                    TupleTypeArguments::FixedLength(ts) => ts.iter().any(|x| match x {
                        TypeOrTypeVarTuple::Type(t) => check(t),
                        TypeOrTypeVarTuple::TypeVarTuple(tvt) => false,
                    }),
                    TupleTypeArguments::ArbitraryLength(t) => check(t),
                },
                GenericItem::ParamSpecArgument(a) => todo!(),
            })
        };
        match self {
            Self::Class(GenericClass {
                generics: ClassGenerics::List(generics),
                ..
            }) => check(self) || check_generics_list(generics),
            Self::Union(u) => u.iter().any(|t| check(t)),
            Self::FunctionOverload(intersection) => {
                intersection.iter_functions().any(|c| c.find_in_type(check))
            }
            Self::Type(t) => check(self) || check(t),
            Self::Tuple(content) => match &content.args {
                TupleTypeArguments::FixedLength(ts) => ts.iter().any(|t| match t {
                    TypeOrTypeVarTuple::Type(t) => check(t),
                    TypeOrTypeVarTuple::TypeVarTuple(_) => false,
                }),
                TupleTypeArguments::ArbitraryLength(t) => check(t),
            },
            Self::Callable(content) => content.find_in_type(check),
            Self::TypedDict(d) => match &d.generics {
                TypedDictGenerics::Generics(g) => check_generics_list(g),
                TypedDictGenerics::None | TypedDictGenerics::NotDefinedYet(_) => false,
            },
            _ => check(self),
        }
    }

    pub fn is_subclassable(&self, db: &Database) -> bool {
        match self {
            Self::Class(_)
            | Self::Tuple(_)
            | Self::NewType(_)
            | Self::NamedTuple(_)
            | Self::Dataclass(_) => true,
            _ => false,
        }
    }

    pub fn maybe_avoid_implicit_literal(&self, db: &Database) -> Option<Self> {
        match self {
            Type::Literal(l) if l.implicit => Some(db.python_state.literal_type(&l.kind)),
            Type::EnumMember(m) if m.implicit => Some(Type::Enum(m.enum_.clone())),
            Type::Tuple(tup) => {
                if let TupleTypeArguments::FixedLength(ts) = &tup.args {
                    let mut gathered = vec![];
                    if ts.iter().any(|type_or| match type_or {
                        TypeOrTypeVarTuple::Type(t) => t.maybe_avoid_implicit_literal(db).is_some(),
                        TypeOrTypeVarTuple::TypeVarTuple(_) => false,
                    }) {
                        for type_or in ts.iter() {
                            if let TypeOrTypeVarTuple::Type(t) = type_or {
                                if let Some(new_t) = t.maybe_avoid_implicit_literal(db) {
                                    gathered.push(TypeOrTypeVarTuple::Type(new_t));
                                    continue;
                                }
                            }
                            gathered.push(type_or.clone())
                        }
                        return Some(Type::Tuple(Rc::new(Tuple::new_fixed_length(
                            gathered.into(),
                        ))));
                    }
                }
                None
            }
            _ => None,
        }
    }

    pub fn avoid_implicit_literal(self, db: &Database) -> Self {
        self.maybe_avoid_implicit_literal(db)
            .unwrap_or_else(|| self)
    }

    pub fn is_literal_or_literal_in_tuple(&self) -> bool {
        self.iter_with_unpacked_unions().any(|t| match t {
            Type::Literal(_) | Type::EnumMember(_) => true,
            Type::Tuple(tup) => match &tup.args {
                TupleTypeArguments::FixedLength(ts) => ts.iter().any(|type_or| matches!(type_or, TypeOrTypeVarTuple::Type(t) if t.is_literal_or_literal_in_tuple())),
                TupleTypeArguments::ArbitraryLength(t) => t.is_literal_or_literal_in_tuple(),
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
                let tuple_class = db.python_state.tuple_class(db, tup);
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

    pub(crate) fn error_if_not_matches<'x>(
        &self,
        i_s: &InferenceState,
        value: &Inferred,
        add_issue: impl Fn(IssueType),
        on_error: impl Fn(Box<str>, Box<str>) -> Option<IssueType>,
    ) {
        self.error_if_not_matches_with_matcher(
            i_s,
            &mut Matcher::default(),
            value,
            add_issue,
            |t1, t2, reason: &MismatchReason| on_error(t1, t2),
        );
    }

    pub(crate) fn error_if_not_matches_with_matcher<'x>(
        &self,
        i_s: &InferenceState,
        matcher: &mut Matcher,
        value: &Inferred,
        //callback: Option<impl FnOnce(Box<str>, Box<str>, &MismatchReason) -> NodeRef<'x>>,
        add_issue: impl Fn(IssueType),
        on_error: impl FnOnce(Box<str>, Box<str>, &MismatchReason) -> Option<IssueType>,
    ) {
        let value_type = value.as_cow_type(i_s);
        let matches = self.is_super_type_of(i_s, matcher, &value_type);
        if let Match::False { ref reason, .. } = matches {
            let error_types = ErrorTypes {
                expected: self,
                got: GotType::Type(&value_type),
                matcher,
                reason,
            };
            let ErrorStrs { expected, got } = error_types.as_boxed_strs(i_s);
            debug!(
                "Mismatch between {expected:?} and {got:?} -> {:?}",
                &matches
            );
            if let Some(error) = on_error(got, expected, reason) {
                add_issue(error);
                error_types.add_mismatch_notes(|issue| add_issue(issue))
            }
        }
    }

    pub fn execute_and_resolve_type_vars(
        &self,
        i_s: &InferenceState,
        calculated_type_args: &CalculatedTypeArguments,
        class: Option<&Class>,
        replace_self_type: ReplaceSelf,
    ) -> Inferred {
        let type_ =
            self.internal_resolve_type_vars(i_s, calculated_type_args, class, replace_self_type);
        debug!("Resolved type vars: {}", type_.format_short(i_s.db));
        Inferred::from_type(type_)
    }

    fn internal_resolve_type_vars(
        &self,
        i_s: &InferenceState,
        calculated_type_args: &CalculatedTypeArguments,
        class: Option<&Class>,
        replace_self_type: ReplaceSelf,
    ) -> Type {
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
                    matcher
                        .replace_type_var_likes_for_nested_context(i_s.db, type_)
                        .on_any_resolved_context_type(i_s, matcher, callable)
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
        for t in self.iter_with_unpacked_unions() {
            let new = match t {
                Type::RecursiveType(r) => r
                    .calculated_type(db)
                    .find_unique_type_in_unpacked_union(db, matcher, find),
                Type::TypeVar(_) if matcher.might_have_defined_type_vars() => matcher
                    .replace_type_var_likes_for_nested_context(db, t)
                    .find_unique_type_in_unpacked_union(db, matcher, find),
                _ => {
                    if let Some(x) = find(t) {
                        if found.is_ok() {
                            return Err(UniqueInUnpackedUnionError::Multiple);
                        } else {
                            found = Ok(x)
                        }
                    }
                    continue;
                }
            };
            match new {
                err @ Err(UniqueInUnpackedUnionError::Multiple) => return err,
                Ok(_) if found.is_ok() => return Err(UniqueInUnpackedUnionError::Multiple),
                _ => found = new,
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
                Generics::from_class_generics(db, &g1)
                    .iter(db)
                    .zip(Generics::from_class_generics(db, &g2).iter(db))
                    .map(|(gi1, gi2)| gi1.merge_matching_parts(db, gi2))
                    .collect(),
            ))
        };
        use TupleTypeArguments::*;
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
                    Type::Tuple(match (&c1.args, &c2.args) {
                        (FixedLength(ts1), FixedLength(ts2)) if ts1.len() == ts2.len() => {
                            Rc::new(Tuple::new_fixed_length(
                                // Performance issue: Same as above
                                ts1.iter()
                                    .zip(ts2.iter())
                                    .map(|(t1, t2)| match (t1, t2) {
                                        (
                                            TypeOrTypeVarTuple::Type(t1),
                                            TypeOrTypeVarTuple::Type(t2),
                                        ) => TypeOrTypeVarTuple::Type(
                                            t1.merge_matching_parts(db, t2),
                                        ),
                                        (t1, t2) => match t1 == t2 {
                                            true => t1.clone(),
                                            false => todo!(),
                                        },
                                    })
                                    .collect(),
                            ))
                        }
                        (ArbitraryLength(t1), ArbitraryLength(t2)) => Rc::new(
                            Tuple::new_arbitrary_length(t1.merge_matching_parts(db, &t2)),
                        ),
                        _ => Tuple::new_empty(),
                    })
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
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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
        match (self, other) {
            (Self::Function { .. }, Self::Function { .. })
            | (Self::Property { .. }, Self::Property { .. })
            | (Self::Classmethod { .. }, Self::Classmethod { .. })
            | (Self::Staticmethod, Self::Staticmethod) => true,
            _ => false,
        }
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

#[derive(Debug, Clone, PartialEq)]
pub enum TypeOrTypeVarTuple {
    Type(Type),
    TypeVarTuple(TypeVarTupleUsage),
}

impl TypeOrTypeVarTuple {
    fn format(&self, format_data: &FormatData) -> Box<str> {
        match self {
            Self::Type(t) => t.format(format_data),
            Self::TypeVarTuple(t) => format_data.format_type_var_like(
                &TypeVarLikeUsage::TypeVarTuple(Cow::Borrowed(t)),
                ParamsStyle::Unreachable,
            ),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
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
            FormatStyle::Short => self.name(format_data.db).into(),
            FormatStyle::Qualified | FormatStyle::MypyRevealType => {
                self.qualified_name(format_data.db)
            }
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
            node_ref.in_module().qualified_name(db),
            node_ref.maybe_str().unwrap().content()
        )
        .into()
    }
}

#[derive(Debug, Clone)]
pub struct Literal {
    pub kind: LiteralKind,
    pub implicit: bool,
}

impl std::cmp::PartialEq for Literal {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
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

    pub fn format(&self, format_data: &FormatData) -> Box<str> {
        let question_mark = match format_data.style {
            FormatStyle::MypyRevealType if self.implicit => "?",
            _ if self.implicit && format_data.hide_implicit_literals => {
                return format_data
                    .db
                    .python_state
                    .literal_type(&self.kind)
                    .format(format_data)
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
    args: &dyn Arguments<'db>,
    result_context: &mut ResultContext,
    on_type_error: OnTypeError<'db, '_>,
    bound: Option<&Type>,
) -> Inferred;

#[derive(Debug, PartialEq, Clone)]
pub enum CustomBehaviorKind {
    Function,
    Method { bound: Option<Rc<Type>> },
}

#[derive(Debug, PartialEq, Clone)]
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
        args: &dyn Arguments<'db>,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError<'db, '_>,
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
            Self::Callable(c) => !c.kind.had_first_self_or_class_annotation(),
            Self::Overload(o) => !o.kind().had_first_self_or_class_annotation(),
        }
    }
}

enum UniqueInUnpackedUnionError {
    None,
    Multiple,
}

impl PartialEq for AnyCause {
    fn eq(&self, other: &Self) -> bool {
        true
    }
}

#[derive(Debug, Eq, Copy, Clone)]
pub enum AnyCause {
    Unannotated,
    Explicit,
    FromError,
    ModuleNotFound,
    Internal,
    Todo, // Used for cases where it's currently unclear what the cause should be.
}
