mod common_base_type;
mod common_sub_type;
mod matching;
mod named_tuple;
mod operations;
mod replace;
mod simplified_union;
mod type_var_likes;

use std::borrow::Cow;
use std::fmt;
use std::mem;
use std::rc::Rc;

use parsa_python_ast::Expression;
use parsa_python_ast::Name;
use parsa_python_ast::PythonString;
use parsa_python_ast::{CodeIndex, ParamKind};
use std::cell::OnceCell;

use crate::arguments::Arguments;
use crate::database::ComplexPoint;
use crate::database::Database;
use crate::database::FileIndex;
use crate::database::ParentScope;
use crate::database::PointLink;
use crate::database::TypeAlias;
use crate::debug;
use crate::diagnostics::IssueType;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::matching::maybe_class_usage;
use crate::matching::CalculatedTypeArguments;
use crate::matching::Generics;
use crate::matching::Match;
use crate::matching::Matcher;
use crate::matching::MismatchReason;
use crate::matching::OnTypeError;
use crate::matching::ResultContext;

use crate::matching::{FormatData, Generic, ParamsStyle};
use crate::node_ref::NodeRef;
use crate::type_helpers::calculate_init_of_dataclass;
use crate::type_helpers::dotted_path_from_dir;
use crate::type_helpers::Instance;
use crate::type_helpers::MroIterator;
use crate::type_helpers::TypeOrClass;
use crate::type_helpers::{format_pretty_callable, Class, Module};
use crate::utils::join_with_commas;
use crate::utils::{bytes_repr, str_repr};
use crate::workspaces::Directory;

pub use common_base_type::{common_base_type, common_base_type_of_type_var_tuple_with_items};
pub use matching::match_tuple_type_arguments;
pub use named_tuple::{
    execute_collections_named_tuple, execute_typing_named_tuple, new_collections_named_tuple,
    new_typing_named_tuple, NamedTuple,
};
pub use replace::ReplaceSelf;
pub use simplified_union::simplified_union_from_iterators;
pub use type_var_likes::{
    CallableWithParent, ParamSpec, ParamSpecArgument, ParamSpecTypeVars, ParamSpecUsage, TypeVar,
    TypeVarIndex, TypeVarKind, TypeVarLike, TypeVarLikeUsage, TypeVarLikes, TypeVarManager,
    TypeVarName, TypeVarTuple, TypeVarTupleUsage, TypeVarUsage, Variance,
};

thread_local! {
    static ARBITRARY_TUPLE: Rc<TupleContent> = Rc::new(TupleContent::new_arbitrary_length(Type::Any));
}

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
            Self::TypeArgument(t) => matches!(t, Type::Any),
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
}

impl std::ops::Index<TypeVarIndex> for GenericsList {
    type Output = GenericItem;

    fn index(&self, index: TypeVarIndex) -> &Self::Output {
        &self.0[index.0 as usize]
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct UnionEntry {
    pub type_: Type,
    pub format_index: usize,
}

#[derive(Debug, Clone, PartialEq)]
pub struct UnionType {
    pub entries: Box<[UnionEntry]>,
    pub format_as_optional: bool,
}

impl UnionType {
    pub fn new(entries: Vec<UnionEntry>) -> Self {
        debug_assert!(entries.len() > 1);
        Self {
            entries: entries.into_boxed_slice(),
            format_as_optional: false,
        }
    }

    pub fn from_types(types: Vec<Type>) -> Self {
        Self::new(
            types
                .into_iter()
                .enumerate()
                .map(|(format_index, type_)| UnionEntry {
                    format_index,
                    type_,
                })
                .collect(),
        )
    }

    pub fn iter(&self) -> impl Iterator<Item = &Type> {
        self.entries.iter().map(|u| &u.type_)
    }

    pub fn sort_for_priority(&mut self) {
        self.entries.sort_by_key(|t| match t.type_ {
            Type::Literal(_) | Type::EnumMember(_) => -1,
            Type::None => 2,
            Type::TypeVar(_) => 3,
            Type::Any => 4,
            _ => t.type_.has_type_vars().into(),
        });
    }

    pub fn format(&self, format_data: &FormatData) -> Box<str> {
        let mut iterator = self.entries.iter();
        let mut sorted = match format_data.style {
            FormatStyle::MypyRevealType => String::new(),
            _ => {
                // Fetch the literals in the front of the union and format them like Literal[1, 2]
                // instead of Literal[1] | Literal[2].
                let count = self
                    .iter()
                    .take_while(|t| matches!(t, Type::Literal(_) | Type::EnumMember(_)))
                    .count();
                if count > 1 {
                    let lit = format!(
                        "Literal[{}]",
                        iterator
                            .by_ref()
                            .take(count)
                            .map(|t| match &t.type_ {
                                Type::Literal(l) => l.format_inner(format_data.db),
                                Type::EnumMember(m) => Cow::Owned(m.format_inner(format_data)),
                                _ => unreachable!(),
                            })
                            .collect::<Vec<_>>()
                            .join(", ")
                    );
                    if count == self.entries.len() {
                        return lit.into();
                    } else {
                        lit + " | "
                    }
                } else {
                    String::new()
                }
            }
        };
        let format_as_optional =
            self.format_as_optional && format_data.style != FormatStyle::MypyRevealType;
        let mut unsorted = iterator
            .filter_map(|e| {
                (!format_as_optional || !matches!(e.type_, Type::None))
                    .then(|| (e.format_index, e.type_.format(format_data)))
            })
            .collect::<Vec<_>>();
        unsorted.sort_by_key(|(format_index, _)| *format_index);
        sorted += &unsorted
            .into_iter()
            .map(|(_, t)| t)
            .collect::<Vec<_>>()
            .join(" | ");
        if format_as_optional {
            format!("Optional[{sorted}]").into()
        } else {
            sorted.into()
        }
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
    Tuple(Rc<TupleContent>),
    Callable(Rc<CallableContent>),
    RecursiveAlias(Rc<RecursiveAlias>),
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
    Any,
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
        matches!(self, Type::Any)
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
                            init.result_type = Type::Dataclass(Rc::new(type_var_dataclass));
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
                    callable.result_type = (**t).clone();
                    return Some(CallableLike::Callable(Rc::new(callable)));
                }
                _ => {
                    /*
                    if matches!(&c1.params, CallableParams::Any) {
                        c1.result_type.is_super_type_of(
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
            Type::Any => Some(CallableLike::Callable(
                i_s.db.python_state.any_callable.clone(),
            )),
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
        matches!(self, Type::Callable(_) | Type::FunctionOverload(_))
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
            Self::Any => Box::from("Any"),
            Self::None => Box::from("None"),
            Self::Never => Box::from("Never"),
            Self::Literal(literal) => literal.format(format_data),
            Self::NewType(n) => n.format(format_data),
            Self::RecursiveAlias(rec) => {
                if let Some(generics) = &rec.generics {
                    if format_data.style != FormatStyle::MypyRevealType {
                        let alias = rec.type_alias(format_data.db);
                        return format!(
                            "{}[{}]",
                            alias.name(format_data.db).unwrap(),
                            generics.format(format_data)
                        )
                        .into();
                    }
                }

                if format_data.has_already_seen_recursive_alias(rec) {
                    if format_data.style == FormatStyle::MypyRevealType {
                        "...".into()
                    } else {
                        let alias = rec.type_alias(format_data.db);
                        Box::from(alias.name(format_data.db).unwrap())
                    }
                } else {
                    let format_data = format_data.with_seen_recursive_alias(rec);
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
        let search_params = |found_type_var: &mut C, params: &_| match params {
            CallableParams::Simple(params) => {
                for param in params.iter() {
                    match &param.param_specific {
                        ParamSpecific::PositionalOnly(t)
                        | ParamSpecific::PositionalOrKeyword(t)
                        | ParamSpecific::KeywordOnly(t)
                        | ParamSpecific::Starred(StarredParamSpecific::ArbitraryLength(t))
                        | ParamSpecific::DoubleStarred(DoubleStarredParamSpecific::ValueType(t)) => {
                            t.search_type_vars(found_type_var)
                        }
                        ParamSpecific::Starred(StarredParamSpecific::ParamSpecArgs(_)) => {
                            unreachable!()
                        }
                        ParamSpecific::DoubleStarred(
                            DoubleStarredParamSpecific::ParamSpecKwargs(_),
                        ) => {
                            unreachable!()
                        }
                    }
                }
            }
            CallableParams::Any => (),
            CallableParams::WithParamSpec(_, spec) => {
                found_type_var(TypeVarLikeUsage::ParamSpec(Cow::Borrowed(spec)))
            }
        };
        let search_in_generics = |found_type_var: &mut C, generics: &GenericsList| {
            for g in generics.iter() {
                match g {
                    GenericItem::TypeArgument(t) => t.search_type_vars(found_type_var),
                    GenericItem::TypeArguments(_) => todo!(),
                    GenericItem::ParamSpecArgument(p) => search_params(found_type_var, &p.params),
                }
            }
        };
        match self {
            Self::Class(GenericClass {
                generics: ClassGenerics::List(generics),
                ..
            }) => search_in_generics(found_type_var, generics),
            Self::Union(u) => {
                for t in u.iter() {
                    t.search_type_vars(found_type_var);
                }
            }
            Self::FunctionOverload(intersection) => {
                for callable in intersection.iter_functions() {
                    search_params(found_type_var, &callable.params);
                    callable.result_type.search_type_vars(found_type_var)
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
                search_params(found_type_var, &content.params);
                content.result_type.search_type_vars(found_type_var)
            }
            Self::Class(..)
            | Self::Any
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
            Self::RecursiveAlias(rec) => {
                if let Some(generics) = rec.generics.as_ref() {
                    search_in_generics(found_type_var, generics)
                }
            }
            Self::ParamSpecArgs(usage) => todo!(),
            Self::ParamSpecKwargs(usage) => todo!(),
            Self::Dataclass(d) => match &d.class.generics {
                ClassGenerics::List(generics) => search_in_generics(found_type_var, generics),
                _ => (),
            },
            Self::TypedDict(d) => {
                for member in d.members.iter() {
                    member.type_.search_type_vars(found_type_var);
                }
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
        already_checked: &mut Vec<Rc<RecursiveAlias>>,
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
            Self::Any => true,
            Self::NewType(n) => n.type_(i_s).has_any(i_s),
            Self::RecursiveAlias(recursive_alias) => {
                if let Some(generics) = &recursive_alias.generics {
                    if search_in_generics(generics, already_checked) {
                        return true;
                    }
                }
                if already_checked.contains(recursive_alias) {
                    false
                } else {
                    already_checked.push(recursive_alias.clone());
                    recursive_alias
                        .type_alias(i_s.db)
                        .type_if_valid()
                        .has_any_internal(i_s, already_checked)
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
                d.members
                    .iter()
                    .any(|m| m.type_.has_any_internal(i_s, already_checked))
            }
            Self::NamedTuple(nt) => nt.__new__.has_any_internal(i_s, already_checked),
            Self::EnumMember(_) => todo!(),
            Self::Super { .. } => todo!(),
        }
    }

    pub fn has_self_type(&self) -> bool {
        match self {
            Self::Class(GenericClass {
                generics: ClassGenerics::List(generics),
                ..
            }) => generics.iter().any(|g| match g {
                GenericItem::TypeArgument(t) => t.has_self_type(),
                GenericItem::TypeArguments(_) => todo!(),
                GenericItem::ParamSpecArgument(params) => todo!(),
            }),
            Self::Union(u) => u.iter().any(|t| t.has_self_type()),
            Self::FunctionOverload(intersection) => {
                intersection.iter_functions().any(|t| t.has_self_type())
            }
            Self::Type(t) => t.has_self_type(),
            Self::Tuple(content) => match &content.args {
                TupleTypeArguments::FixedLength(ts) => ts.iter().any(|t| match t {
                    TypeOrTypeVarTuple::Type(t) => t.has_self_type(),
                    TypeOrTypeVarTuple::TypeVarTuple(_) => false,
                }),
                TupleTypeArguments::ArbitraryLength(t) => t.has_self_type(),
            },
            Self::Callable(content) => content.has_self_type(),
            Self::Self_ => true,
            Self::Dataclass(_) => todo!(),
            Self::TypedDict(d) => todo!(),
            Self::NamedTuple(_) => {
                debug!("TODO namedtuple has_self_type");
                false
            }
            Self::EnumMember(_) => todo!(),
            Self::Class(..)
            | Self::None
            | Self::Never
            | Self::Literal { .. }
            | Self::Any
            | Self::Enum(_)
            | Self::NewType(_)
            | Self::ParamSpecArgs(_)
            | Self::ParamSpecKwargs(_)
            | Self::RecursiveAlias(_)
            | Self::Module(_)
            | Self::Namespace(_)
            | Self::CustomBehavior(_)
            | Self::TypeVar(_) => false,
            Self::Super { .. } => todo!(),
        }
    }

    pub fn is_subclassable(&self, db: &Database) -> bool {
        match self {
            Self::Class(_) | Self::Tuple(_) | Self::NewType(_) | Self::NamedTuple(_) => true,
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
                        return Some(Type::Tuple(Rc::new(TupleContent::new_fixed_length(
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
            // TODO? Type::Dataclass(d) => Some(d.class(db).mro(db)),
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
            _ => MroIterator::new(
                db,
                TypeOrClass::Type(Cow::Borrowed(self)),
                Generics::None,
                [].iter(),
                false,
            ),
        }
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
        let value_type = value.as_cow_type(i_s);
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
            Type::RecursiveAlias(r) => r
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
                Type::RecursiveAlias(r) => r
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
                _ => Type::Any,
            },
            Type::Union(u1) => match other {
                Type::Union(u2) if u1.iter().all(|x| u2.iter().any(|y| x == y)) => {
                    Type::Union(u1.clone())
                }
                _ => Type::Any,
            },
            Type::Tuple(c1) => match other {
                Type::Tuple(c2) => {
                    Type::Tuple(match (&c1.args, &c2.args) {
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
                            TupleContent::new_arbitrary_length(t1.merge_matching_parts(db, &t2)),
                        ),
                        _ => TupleContent::new_empty(),
                    })
                }
                _ => Type::Any,
            },
            Type::Callable(content1) => match other {
                Type::Callable(content2) => Type::Callable(db.python_state.any_callable.clone()),
                _ => Type::Any,
            },
            _ => Type::Any,
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
pub enum TupleTypeArguments {
    FixedLength(Rc<[TypeOrTypeVarTuple]>),
    ArbitraryLength(Box<Type>),
}

impl TupleTypeArguments {
    pub fn has_type_var_tuple(&self) -> Option<&[TypeOrTypeVarTuple]> {
        match self {
            Self::FixedLength(ts) => ts
                .iter()
                .any(|t| matches!(t, TypeOrTypeVarTuple::TypeVarTuple(_)))
                .then(|| ts.as_ref()),
            _ => None,
        }
    }

    pub fn is_any(&self) -> bool {
        match self {
            Self::ArbitraryLength(t) => matches!(t.as_ref(), Type::Any),
            Self::FixedLength(_) => false,
        }
    }

    pub fn has_any(&self, i_s: &InferenceState) -> bool {
        self.has_any_internal(i_s, &mut Vec::new())
    }

    fn has_any_internal(
        &self,
        i_s: &InferenceState,
        already_checked: &mut Vec<Rc<RecursiveAlias>>,
    ) -> bool {
        match self {
            Self::FixedLength(ts) => ts.iter().any(|t| match t {
                TypeOrTypeVarTuple::Type(t) => t.has_any_internal(i_s, already_checked),
                TypeOrTypeVarTuple::TypeVarTuple(_) => false,
            }),
            Self::ArbitraryLength(t) => t.has_any_internal(i_s, already_checked),
        }
    }

    fn common_base_type(&self, i_s: &InferenceState) -> Type {
        match self {
            Self::FixedLength(ts) => common_base_type(i_s, ts.iter()),
            Self::ArbitraryLength(t) => t.as_ref().clone(),
        }
    }

    pub fn format(&self, format_data: &FormatData) -> Box<str> {
        match self {
            Self::FixedLength(ts) if ts.is_empty() => Box::from("()"),
            Self::FixedLength(ts) => {
                join_with_commas(ts.iter().map(|g| g.format(format_data).into())).into()
            }
            Self::ArbitraryLength(t) => format!("{}, ...", t.format(format_data)).into(),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct TupleContent {
    pub args: TupleTypeArguments,
    tuple_class_generics: OnceCell<GenericsList>,
}

impl TupleContent {
    pub fn new(args: TupleTypeArguments) -> Self {
        Self {
            args,
            tuple_class_generics: OnceCell::new(),
        }
    }

    pub fn new_fixed_length(args: Rc<[TypeOrTypeVarTuple]>) -> Self {
        Self::new(TupleTypeArguments::FixedLength(args))
    }

    pub fn new_arbitrary_length(arg: Type) -> Self {
        Self::new(TupleTypeArguments::ArbitraryLength(Box::new(arg)))
    }

    pub fn new_empty() -> Rc<Self> {
        ARBITRARY_TUPLE.with(|t| t.clone())
    }

    pub fn tuple_class_generics(&self, db: &Database) -> &GenericsList {
        self.tuple_class_generics.get_or_init(|| {
            GenericsList::new_generics(Rc::new([GenericItem::TypeArgument(
                self.args.common_base_type(&InferenceState::new(db)),
            )]))
        })
    }

    pub fn format(&self, format_data: &FormatData) -> Box<str> {
        self.format_with_fallback(format_data, "")
    }

    pub fn format_with_fallback(&self, format_data: &FormatData, fallback: &str) -> Box<str> {
        let base = match format_data.style {
            FormatStyle::Short => "tuple",
            FormatStyle::Qualified | FormatStyle::MypyRevealType => "builtins.tuple",
        };
        format!("{base}[{}{fallback}]", self.args.format(format_data)).into()
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum StarredParamSpecific {
    ArbitraryLength(Type),
    ParamSpecArgs(ParamSpecUsage),
}

#[derive(Debug, Clone, PartialEq)]
pub enum DoubleStarredParamSpecific {
    ValueType(Type),
    ParamSpecKwargs(ParamSpecUsage),
}

#[derive(Debug, Clone, PartialEq)]
pub enum ParamSpecific {
    PositionalOnly(Type),
    PositionalOrKeyword(Type),
    KeywordOnly(Type),
    Starred(StarredParamSpecific),
    DoubleStarred(DoubleStarredParamSpecific),
}

impl ParamSpecific {
    pub fn param_kind(&self) -> ParamKind {
        match self {
            Self::PositionalOnly(_) => ParamKind::PositionalOnly,
            Self::PositionalOrKeyword(_) => ParamKind::PositionalOrKeyword,
            Self::KeywordOnly(_) => ParamKind::KeywordOnly,
            Self::Starred(_) => ParamKind::Starred,
            Self::DoubleStarred(_) => ParamKind::DoubleStarred,
        }
    }

    pub fn maybe_positional_type(&self) -> Option<&Type> {
        match self {
            Self::PositionalOnly(t) | Self::PositionalOrKeyword(t) => Some(t),
            _ => None,
        }
    }

    pub fn expect_positional_type(self) -> Type {
        match self {
            Self::PositionalOnly(t) | Self::PositionalOrKeyword(t) => t,
            _ => unreachable!(),
        }
    }

    pub fn expect_positional_type_as_ref(&self) -> &Type {
        match &self {
            Self::PositionalOnly(t) | Self::PositionalOrKeyword(t) => t,
            _ => unreachable!(),
        }
    }

    pub fn maybe_type(&self) -> Option<&Type> {
        match self {
            Self::PositionalOnly(t)
            | Self::PositionalOrKeyword(t)
            | Self::KeywordOnly(t)
            | Self::Starred(StarredParamSpecific::ArbitraryLength(t))
            | Self::DoubleStarred(DoubleStarredParamSpecific::ValueType(t)) => Some(t),
            Self::Starred(StarredParamSpecific::ParamSpecArgs(_)) | Self::DoubleStarred(_) => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct CallableParam {
    pub param_specific: ParamSpecific,
    pub name: Option<DbString>,
    pub has_default: bool,
}

impl CallableParam {
    pub fn new_anonymous(param_specific: ParamSpecific) -> Self {
        CallableParam {
            param_specific,
            name: None,
            has_default: false,
        }
    }

    pub fn format(&self, format_data: &FormatData) -> Box<str> {
        if !matches!(self.param_specific, ParamSpecific::PositionalOnly(_))
            || format_data.verbose && self.has_default
        {
            if let ParamSpecific::Starred(t) = &self.param_specific {
                return match t {
                    StarredParamSpecific::ArbitraryLength(t) => {
                        format!("VarArg({})", t.format(format_data))
                    }
                    StarredParamSpecific::ParamSpecArgs(u) => unreachable!(),
                }
                .into();
            } else if let ParamSpecific::DoubleStarred(t) = &self.param_specific {
                return match t {
                    DoubleStarredParamSpecific::ValueType(t) => {
                        format!("KwArg({})", t.format(format_data))
                    }
                    DoubleStarredParamSpecific::ParamSpecKwargs(_) => unreachable!(),
                }
                .into();
            } else if let Some(name) = self.name.as_ref() {
                match format_data.style {
                    FormatStyle::MypyRevealType => {
                        let mut string = match &self.param_specific {
                            ParamSpecific::PositionalOnly(t)
                            | ParamSpecific::PositionalOrKeyword(t)
                            | ParamSpecific::KeywordOnly(t) => {
                                format!(
                                    "{}: {}",
                                    name.as_str(format_data.db),
                                    t.format(format_data),
                                )
                            }
                            // TODO these two cases are probably unreachable
                            ParamSpecific::Starred(s) => format!(
                                "*{}: {}",
                                name.as_str(format_data.db),
                                match s {
                                    StarredParamSpecific::ArbitraryLength(t) =>
                                        t.format(format_data),
                                    StarredParamSpecific::ParamSpecArgs(_) => todo!(),
                                }
                            ),
                            ParamSpecific::DoubleStarred(d) => format!(
                                "**{}: {}",
                                name.as_str(format_data.db),
                                match d {
                                    DoubleStarredParamSpecific::ValueType(t) =>
                                        t.format(format_data),
                                    DoubleStarredParamSpecific::ParamSpecKwargs(_) => todo!(),
                                }
                            ),
                        };
                        if self.has_default {
                            string += " =";
                        }
                        return string.into();
                    }
                    _ => {
                        return match &self.param_specific {
                            ParamSpecific::PositionalOnly(t)
                            | ParamSpecific::PositionalOrKeyword(t) => {
                                let t = t.format(format_data);
                                if !format_data.verbose {
                                    return t;
                                }
                                let default = match self.has_default {
                                    false => "",
                                    true => "Default",
                                };
                                format!("{default}Arg({t}, '{}')", name.as_str(format_data.db))
                            }
                            ParamSpecific::KeywordOnly(t) => {
                                let default = match self.has_default {
                                    false => "",
                                    true => "Default",
                                };
                                format!(
                                    "{default}NamedArg({}, '{}')",
                                    t.format(format_data),
                                    name.as_str(format_data.db)
                                )
                            }
                            ParamSpecific::Starred(_) | ParamSpecific::DoubleStarred(_) => {
                                unreachable!()
                            }
                        }
                        .into();
                    }
                }
            } else if self.has_default {
                return match &self.param_specific {
                    ParamSpecific::PositionalOnly(t)
                    | ParamSpecific::PositionalOrKeyword(t)
                    | ParamSpecific::KeywordOnly(t) => {
                        format!("DefaultArg({})", t.format(format_data)).into()
                    }
                    _ => unreachable!(),
                };
            }
        }
        match &self.param_specific {
            ParamSpecific::PositionalOnly(t) => t.format(format_data),
            _ => unreachable!(),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct CallableContent {
    pub name: Option<DbString>,
    pub class_name: Option<StringSlice>,
    pub defined_at: PointLink,
    pub kind: FunctionKind,
    pub type_vars: TypeVarLikes,
    pub params: CallableParams,
    pub result_type: Type,
}

impl CallableContent {
    pub fn new_any(type_vars: TypeVarLikes) -> Self {
        Self::new_any_internal(PointLink::new(FileIndex(0), 0), type_vars)
    }

    pub fn name<'x>(&'x self, db: &'x Database) -> &'x str {
        self.name
            .as_ref()
            .map(|n| n.as_str(db))
            .unwrap_or("function")
    }

    fn new_any_internal(defined_at: PointLink, type_vars: TypeVarLikes) -> Self {
        Self {
            name: None,
            class_name: None,
            defined_at,
            kind: FunctionKind::Function {
                had_first_self_or_class_annotation: false,
            },
            type_vars,
            params: CallableParams::Any,
            result_type: Type::Any,
        }
    }
    pub fn new_any_with_defined_at(db: &Database, defined_at: PointLink) -> Self {
        Self::new_any_internal(defined_at, db.python_state.empty_type_var_likes.clone())
    }

    pub fn expect_simple_params(&self) -> &[CallableParam] {
        let CallableParams::Simple(params) = &self.params else {
            unreachable!()
        };
        params
    }

    pub fn remove_first_param(&self) -> Option<Self> {
        let mut c = self.clone();
        c.params = match &self.params {
            CallableParams::Simple(params) => {
                if params.len() == 0 {
                    todo!()
                }
                let mut params = params.to_vec();
                params.remove(0);
                CallableParams::Simple(params.into())
            }
            CallableParams::WithParamSpec(pre, usage) => {
                todo!()
            }
            CallableParams::Any => CallableParams::Any,
        };
        Some(c)
    }

    pub fn first_positional_type(&self) -> Option<&Type> {
        match &self.params {
            CallableParams::Simple(params) => {
                params.first().and_then(|p| match &p.param_specific {
                    ParamSpecific::PositionalOnly(t) | ParamSpecific::PositionalOrKeyword(t) => {
                        Some(t)
                    }
                    _ => todo!(),
                })
            }
            CallableParams::WithParamSpec(pre, usage) => {
                todo!()
            }
            CallableParams::Any => Some(&Type::Any),
        }
    }

    pub fn has_exactly_one_positional_parameter(&self) -> Option<WrongPositionalCount> {
        match &self.params {
            CallableParams::Simple(params) => match params.len() {
                0 => Some(WrongPositionalCount::TooFew),
                1 => None,
                _ => {
                    for param in params.iter().skip(1) {
                        if !param.has_default
                            && !matches!(
                                &param.param_specific,
                                ParamSpecific::Starred(_) | ParamSpecific::DoubleStarred(_)
                            )
                        {
                            return Some(WrongPositionalCount::TooMany);
                        }
                    }
                    None
                }
            },
            CallableParams::WithParamSpec(_, _) => Some(WrongPositionalCount::TooMany),
            CallableParams::Any => None,
        }
    }

    fn has_any_internal(
        &self,
        i_s: &InferenceState,
        already_checked: &mut Vec<Rc<RecursiveAlias>>,
    ) -> bool {
        self.result_type.has_any_internal(i_s, already_checked)
            || self.params.has_any_internal(i_s, already_checked)
    }

    pub fn has_self_type(&self) -> bool {
        self.result_type.has_self_type() || match &self.params {
            CallableParams::Simple(params) => {
                params.iter().any(|param| match &param.param_specific {
                    ParamSpecific::PositionalOnly(t)
                    | ParamSpecific::PositionalOrKeyword(t)
                    | ParamSpecific::KeywordOnly(t)
                    | ParamSpecific::Starred(StarredParamSpecific::ArbitraryLength(t))
                    | ParamSpecific::DoubleStarred(DoubleStarredParamSpecific::ValueType(t)) => {
                        t.has_self_type()
                    }
                    ParamSpecific::Starred(StarredParamSpecific::ParamSpecArgs(_)) => false,
                    ParamSpecific::DoubleStarred(DoubleStarredParamSpecific::ParamSpecKwargs(
                        _,
                    )) => false,
                })
            }
            CallableParams::Any => false,
            CallableParams::WithParamSpec(types, param_spec) => {
                todo!()
            }
        }
    }

    pub fn format(&self, format_data: &FormatData) -> String {
        if format_data.style == FormatStyle::MypyRevealType {
            return format_pretty_callable(format_data, self).into();
        }
        let result = self.result_type.format(format_data);
        let params = self.params.format(format_data, ParamsStyle::CallableParams);
        format!("Callable[{params}, {result}]")
    }
}

pub enum WrongPositionalCount {
    TooMany,
    TooFew,
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

#[derive(Debug, Clone)]
pub struct RecursiveAlias {
    pub link: PointLink,
    pub generics: Option<GenericsList>,
    pub calculated_type: OnceCell<Type>,
}

impl RecursiveAlias {
    pub fn new(link: PointLink, generics: Option<GenericsList>) -> Self {
        Self {
            link,
            generics,
            calculated_type: OnceCell::new(),
        }
    }

    pub fn type_alias<'db>(&self, db: &'db Database) -> &'db TypeAlias {
        let node_ref = NodeRef::from_link(db, self.link);
        match node_ref.complex() {
            Some(ComplexPoint::TypeAlias(alias)) => alias,
            _ => unreachable!(),
        }
    }
}

impl std::cmp::PartialEq for RecursiveAlias {
    fn eq(&self, other: &Self) -> bool {
        self.link == other.link && self.generics == other.generics
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum CallableParams {
    Simple(Rc<[CallableParam]>),
    WithParamSpec(Rc<[Type]>, ParamSpecUsage),
    Any,
}

impl CallableParams {
    pub fn format(&self, format_data: &FormatData, style: ParamsStyle) -> Box<str> {
        let parts = match self {
            Self::Simple(params) => {
                let mut out_params = Vec::with_capacity(params.len());
                // Display a star only if we are displaying a "normal" function signature
                let mut had_param_spec_args = false;
                for (i, param) in params.iter().enumerate() {
                    use DoubleStarredParamSpecific::ParamSpecKwargs;
                    use ParamSpecific::{DoubleStarred, Starred};
                    use StarredParamSpecific::ParamSpecArgs;
                    match &param.param_specific {
                        Starred(ParamSpecArgs(usage1)) => match params
                            .get(i + 1)
                            .map(|p| &p.param_specific)
                        {
                            Some(DoubleStarred(ParamSpecKwargs(usage2))) if usage1 == usage2 => {
                                had_param_spec_args = true;
                            }
                            _ => todo!(),
                        },
                        DoubleStarred(ParamSpecKwargs(usage)) => match had_param_spec_args {
                            true => out_params.push(format_data.format_type_var_like(
                                // TODO is this even reachable?
                                &TypeVarLikeUsage::ParamSpec(Cow::Borrowed(usage)),
                                style,
                            )),
                            false => todo!(),
                        },
                        _ => out_params.push(param.format(format_data)),
                    }
                }
                out_params
            }
            Self::WithParamSpec(pre_types, usage) => {
                let style = match style {
                    ParamsStyle::CallableParams if !pre_types.is_empty() => {
                        ParamsStyle::CallableParamsInner
                    }
                    _ => style,
                };
                let spec = format_data.format_type_var_like(
                    &TypeVarLikeUsage::ParamSpec(Cow::Borrowed(usage)),
                    style,
                );
                if pre_types.len() == 0 {
                    return spec;
                }
                let parts = pre_types.iter().map(|t| t.format(format_data));
                if spec.is_empty() {
                    parts.collect()
                } else {
                    parts.chain(std::iter::once(spec)).collect()
                }
            }
            Self::Any => return Box::from("..."),
        };
        let params = parts.join(", ");
        match style {
            ParamsStyle::CallableParams => format!("[{params}]").into(),
            _ => params.into(),
        }
    }

    fn has_any_internal(
        &self,
        i_s: &InferenceState,
        already_checked: &mut Vec<Rc<RecursiveAlias>>,
    ) -> bool {
        match self {
            Self::Simple(params) => params.iter().any(|param| match &param.param_specific {
                ParamSpecific::PositionalOnly(t)
                | ParamSpecific::PositionalOrKeyword(t)
                | ParamSpecific::KeywordOnly(t)
                | ParamSpecific::Starred(StarredParamSpecific::ArbitraryLength(t))
                | ParamSpecific::DoubleStarred(DoubleStarredParamSpecific::ValueType(t)) => {
                    t.has_any_internal(i_s, already_checked)
                }
                ParamSpecific::Starred(StarredParamSpecific::ParamSpecArgs(_)) => false,
                ParamSpecific::DoubleStarred(DoubleStarredParamSpecific::ParamSpecKwargs(_)) => {
                    false
                }
            }),
            Self::WithParamSpec(pre_types, usage) => pre_types
                .iter()
                .any(|t| t.has_any_internal(i_s, already_checked)),
            Self::Any => true,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct DataclassOptions {
    pub init: bool,
    pub eq: bool,
    pub order: bool,
    pub frozen: bool,
    pub match_args: bool,
    pub kw_only: bool,
    pub slots: bool,
    // the keyword arguments `weakref_slot = false` and `repr = true` are ignored here, because
    // they are not relevant for us as a typechecker.
}

impl Default for DataclassOptions {
    fn default() -> Self {
        Self {
            init: true,
            eq: true,
            order: false,
            frozen: false,
            match_args: true,
            kw_only: false,
            slots: false,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Dataclass {
    pub class: GenericClass,
    __init__: OnceCell<CallableContent>,
    pub options: DataclassOptions,
}

impl Dataclass {
    pub fn new(class: GenericClass, options: DataclassOptions) -> Rc<Self> {
        Rc::new(Self {
            class,
            __init__: OnceCell::new(),
            options,
        })
    }

    pub fn class<'a>(&'a self, db: &'a Database) -> Class<'a> {
        self.class.class(db)
    }

    pub fn has_defined_generics(&self) -> bool {
        !matches!(self.class.generics, ClassGenerics::NotDefinedYet)
    }

    pub fn __init__<'a>(self_: &'a Rc<Self>, db: &Database) -> &'a CallableContent {
        if self_.__init__.get().is_none() {
            // Cannot use get_or_init, because this might cycle ones for some reasons (see for
            // example the test testDeferredDataclassInitSignatureSubclass)
            self_
                .__init__
                .set(calculate_init_of_dataclass(db, self_))
                .ok();
        }
        self_.__init__.get().unwrap()
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedDictMember {
    pub name: StringSlice,
    pub type_: Type,
    pub required: bool,
}

impl TypedDictMember {
    pub fn replace_type(&self, callable: impl FnOnce(&Type) -> Type) -> Self {
        Self {
            name: self.name,
            type_: callable(&self.type_),
            required: self.required,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypedDictGenerics {
    None,
    NotDefinedYet(TypeVarLikes),
    Generics(GenericsList),
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedDict {
    pub name: Option<StringSlice>,
    pub members: Box<[TypedDictMember]>,
    pub defined_at: PointLink,
    pub generics: TypedDictGenerics,
}

impl TypedDict {
    pub fn new(
        name: Option<StringSlice>,
        members: Box<[TypedDictMember]>,
        defined_at: PointLink,
        generics: TypedDictGenerics,
    ) -> Rc<Self> {
        Rc::new(Self {
            name,
            members,
            defined_at,
            generics,
        })
    }

    pub fn new_definition(
        name: StringSlice,
        members: Box<[TypedDictMember]>,
        defined_at: PointLink,
        type_var_likes: TypeVarLikes,
    ) -> Rc<Self> {
        let generics = if type_var_likes.is_empty() {
            TypedDictGenerics::None
        } else {
            TypedDictGenerics::NotDefinedYet(type_var_likes)
        };
        Rc::new(Self {
            name: Some(name),
            members,
            defined_at,
            generics,
        })
    }

    pub fn replace_type_var_likes(&self, db: &Database, generics: GenericsList) -> Rc<Self> {
        let members = self
            .members
            .iter()
            .map(|m| {
                m.replace_type(|t| {
                    m.type_
                        .replace_type_var_likes(db, &mut |usage| generics[usage.index()].clone())
                })
            })
            .collect::<Box<[_]>>();
        TypedDict::new(
            self.name,
            members,
            self.defined_at,
            TypedDictGenerics::Generics(generics),
        )
    }

    pub fn find_member(&self, db: &Database, name: &str) -> Option<&TypedDictMember> {
        self.members.iter().find(|p| p.name.as_str(db) == name)
    }

    fn qualified_name(&self, db: &Database) -> Option<String> {
        let Some(name) = self.name else {
            return None
        };
        let module = Module::from_file_index(db, name.file_index).qualified_name(db);
        Some(format!("{module}.{}", name.as_str(db)))
    }

    pub fn union(&self, i_s: &InferenceState, other: &Self) -> Type {
        let mut members = self.members.clone().into_vec();
        'outer: for m2 in other.members.iter() {
            for m1 in members.iter() {
                if m1.name.as_str(i_s.db) == m2.name.as_str(i_s.db) {
                    if m1.required != m2.required
                        || !m1.type_.is_simple_same_type(i_s, &m2.type_).bool()
                    {
                        return Type::Never;
                    }
                    continue 'outer;
                }
            }
            members.push(m2.clone());
        }
        Type::TypedDict(Self::new(
            None,
            members.into_boxed_slice(),
            self.defined_at,
            TypedDictGenerics::None,
        ))
    }

    pub fn intersection(&self, i_s: &InferenceState, other: &Self) -> Rc<TypedDict> {
        let mut new_members = vec![];
        for m1 in self.members.iter() {
            for m2 in other.members.iter() {
                if m1.name.as_str(i_s.db) == m2.name.as_str(i_s.db) {
                    if m1.required == m2.required
                        && m1.type_.is_simple_same_type(i_s, &m2.type_).bool()
                    {
                        new_members.push(m1.clone());
                    }
                }
            }
        }
        Self::new(
            None,
            new_members.into_boxed_slice(),
            self.defined_at,
            TypedDictGenerics::None,
        )
    }

    pub fn name_or_fallback(&self, format_data: &FormatData) -> String {
        if let Some(name) = self.name {
            name.as_str(format_data.db).into()
        } else {
            self.format_full(format_data, None)
        }
    }

    pub fn format(&self, format_data: &FormatData) -> String {
        match format_data.style {
            FormatStyle::MypyRevealType => {
                self.format_full(format_data, self.qualified_name(format_data.db).as_deref())
            }
            FormatStyle::Short if !format_data.verbose => self.name_or_fallback(format_data),
            _ => self
                .qualified_name(format_data.db)
                .unwrap_or_else(|| todo!()),
        }
    }

    pub fn format_full(&self, format_data: &FormatData, name: Option<&str>) -> String {
        let rec = RecursiveAlias::new(self.defined_at, None);
        if format_data.has_already_seen_recursive_alias(&rec) {
            return "...".to_string();
        }
        let format_data = &format_data.with_seen_recursive_alias(&rec);
        let params = join_with_commas(self.members.iter().map(|p| {
            format!(
                "'{}'{}: {}",
                p.name.as_str(format_data.db),
                match p.required {
                    true => "",
                    false => "?",
                },
                p.type_.format(format_data)
            )
        }));
        if let Some(name) = name {
            format!("TypedDict('{name}', {{{params}}})").into()
        } else {
            format!("TypedDict({{{params}}})").into()
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct EnumMember {
    pub enum_: Rc<Enum>,
    member_index: usize,
    implicit: bool,
}

impl EnumMember {
    pub fn new(enum_: Rc<Enum>, member_index: usize, implicit: bool) -> Self {
        Self {
            enum_,
            member_index,
            implicit,
        }
    }

    pub fn name<'x>(&'x self, db: &'x Database) -> &'x str {
        self.enum_.members[self.member_index].name(db)
    }

    pub fn value(&self) -> Option<PointLink> {
        self.enum_.members[self.member_index].value
    }

    pub fn is_same_member(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.enum_, &other.enum_) && self.member_index == other.member_index
    }

    pub fn format(&self, format_data: &FormatData) -> String {
        let question_mark = match format_data.style {
            FormatStyle::MypyRevealType if self.implicit => "?",
            _ if self.implicit && format_data.hide_implicit_literals => {
                return self.enum_.format(format_data)
            }
            _ => "",
        };
        format!("Literal[{}]{question_mark}", self.format_inner(format_data))
    }

    pub fn format_inner(&self, format_data: &FormatData) -> String {
        format!(
            "{}.{}",
            &self.enum_.format(format_data),
            self.name(format_data.db)
        )
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct EnumMemberDefinition {
    name: DbString,
    pub value: Option<PointLink>,
}

impl EnumMemberDefinition {
    pub fn new(name: DbString, value: Option<PointLink>) -> Self {
        Self { name, value }
    }

    pub fn name<'x>(&'x self, db: &'x Database) -> &'x str {
        self.name.as_str(db)
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct Enum {
    pub name: StringSlice,
    pub class: PointLink,
    defined_at: PointLink,
    parent_scope: ParentScope,
    pub members: Box<[EnumMemberDefinition]>,
    has_customized_new: OnceCell<bool>,
}

impl Enum {
    pub fn new(
        name: StringSlice,
        class: PointLink,
        defined_at: PointLink,
        parent_scope: ParentScope,
        members: Box<[EnumMemberDefinition]>,
        has_customized_new: OnceCell<bool>,
    ) -> Rc<Self> {
        Rc::new(Self {
            name,
            defined_at,
            parent_scope,
            class,
            members,
            has_customized_new,
        })
    }

    pub fn class<'db>(&self, db: &'db Database) -> Class<'db> {
        Class::from_non_generic_link(db, self.class)
    }

    pub fn lookup(rc: &Rc<Enum>, db: &Database, name: &str, implicit: bool) -> Option<EnumMember> {
        for (index, member) in rc.members.iter().enumerate() {
            if name == member.name(db) {
                return Some(EnumMember::new(rc.clone(), index, implicit));
            }
        }
        None
    }

    pub fn has_customized_new(&self, i_s: &InferenceState) -> bool {
        *self
            .has_customized_new
            .get_or_init(|| self.class(i_s.db).has_customized_enum_new(i_s))
    }

    pub fn format(&self, format_data: &FormatData) -> String {
        let enum_name = self.name.as_str(format_data.db);
        match format_data.style {
            FormatStyle::Short if !format_data.verbose => enum_name.to_string(),
            _ => self.parent_scope.qualified_name(
                format_data.db,
                NodeRef::from_link(format_data.db, self.defined_at),
                enum_name,
            ),
        }
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
    pub fn new_function(callback: CustomBehaviorCallback) -> Self {
        Self {
            callback,
            kind: CustomBehaviorKind::Function,
        }
    }

    pub fn new_method(callback: CustomBehaviorCallback, bound: Option<Rc<Type>>) -> Self {
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

    pub fn execute<'db>(
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

enum UniqueInUnpackedUnionError {
    None,
    Multiple,
}
