use std::borrow::Cow;
use std::cell::Cell;
use std::collections::HashMap;
use std::fmt;
use std::mem;
use std::ops::AddAssign;
use std::path::Path;
use std::pin::Pin;
use std::rc::Rc;

use parsa_python_ast::Expression;
use parsa_python_ast::Name;
use parsa_python_ast::{CodeIndex, NodeIndex, ParamKind};
use std::cell::OnceCell;

use crate::debug;
use crate::file::PythonFile;
use crate::file::{
    File, FileState, FileStateLoader, FileSystemReader, LanguageFileState, PythonFileLoader, Vfs,
};
use crate::inference_state::InferenceState;
use crate::matching::Generics;
use crate::matching::{common_base_type, FormatData, Generic, ParamsStyle};
use crate::node_ref::NodeRef;
use crate::python_state::PythonState;
use crate::type_helpers::{Class, Module};
use crate::utils::{bytes_repr, str_repr, InsertOnlyVec, SymbolTable};
use crate::workspaces::{DirContent, DirOrFile, Invalidations, WorkspaceFileIndex, Workspaces};
use crate::PythonProject;

thread_local! {
    static EMPTY_TUPLE: Rc<TupleContent> = Rc::new(TupleContent {
        args: None,
        tuple_class_generics: OnceCell::new(),
    });
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FileIndex(pub u32);
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd)]
pub struct TypeVarIndex(u32);
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MroIndex(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StringSlice {
    pub file_index: FileIndex,
    start: CodeIndex,
    end: u32,
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

impl TypeVarIndex {
    pub fn as_usize(&self) -> usize {
        self.0 as usize
    }
}

impl AddAssign<i32> for TypeVarIndex {
    fn add_assign(&mut self, other: i32) {
        self.0 = (self.0 as i32 + other) as u32;
    }
}

impl From<usize> for TypeVarIndex {
    fn from(item: usize) -> Self {
        Self(item as u32)
    }
}

impl fmt::Display for FileIndex {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

type FileStateLoaders = Box<[Box<dyn FileStateLoader>]>;

// Most significant bits
// 27 bits = 134217728; 20 bits = 1048576
// oxxxx is_analyzed
// xoxxx is_invalidated
// xxooo Locality (xXxx is_external)
// xxxxxo in_module_scope  TODO remove
// xxxxxxo is_nullable  TODO remove
// xxxxxxxooo PointType
// if true rest 22 bits reserved for Point details

const IS_ANALIZED_BIT_INDEX: usize = 31;
// const IS_INVALIDATED_BIT_INDEX: usize = 30;
const LOCALITY_BIT_INDEX: usize = 27; // Uses 3 bits
                                      // const IN_MODULE_SCOPE_BIT_INDEX: usize = 26;
                                      // const IS_NULLABLE_BIT_INDEX: usize = 25;
const TYPE_BIT_INDEX: usize = 22; // Uses 3 bits

const REST_MASK: u32 = 0b11_1111_1111_1111_1111_1111;
const SPECIFIC_MASK: u32 = 0xFF; // 8 bits
                                 // const MAX_TYPE_VAR: u32 = 0xFF; // 256
                                 // const FILE_MASK: u32 = 0xFFFFFF; // 24 bits
const IS_ANALIZED_MASK: u32 = 1 << IS_ANALIZED_BIT_INDEX;
// const IN_MODULE_SCOPE_MASK: u32 = 1 << IN_MODULE_SCOPE_BIT_INDEX;
// const IS_NULLABLE_MASK: u32 = 1 << IN_MODULE_SCOPE_BIT_INDEX;
const LOCALITY_MASK: u32 = 0b111 << LOCALITY_BIT_INDEX;
const TYPE_MASK: u32 = 0b111 << TYPE_BIT_INDEX;

// const IS_EXTERN_MASK: u32 = 1 << 30;

#[derive(Copy, Clone, Eq, PartialEq, Default)]
pub struct Point {
    flags: u32,
    node_index: u32,
}

impl Point {
    #[inline]
    fn calculate_flags(type_: PointType, rest: u32, locality: Locality) -> u32 {
        debug_assert!(rest & !REST_MASK == 0);
        rest | IS_ANALIZED_MASK
            | (locality as u32) << LOCALITY_BIT_INDEX
            | (type_ as u32) << TYPE_BIT_INDEX
    }

    pub fn new_redirect(file: FileIndex, node_index: NodeIndex, locality: Locality) -> Self {
        let flags = Self::calculate_flags(PointType::Redirect, file.0, locality);
        Self { flags, node_index }
    }

    pub fn new_multi_definition(node_index: NodeIndex, locality: Locality) -> Self {
        let flags = Self::calculate_flags(PointType::MultiDefinition, 0, locality);
        Self { flags, node_index }
    }

    pub fn new_complex_point(complex_index: u32, locality: Locality) -> Self {
        let flags = Self::calculate_flags(PointType::Complex, complex_index, locality);
        Self {
            flags,
            node_index: 0,
        }
    }

    pub fn new_unknown(locality: Locality) -> Self {
        let flags = Self::calculate_flags(PointType::Unknown, 0, locality);
        Self {
            flags,
            node_index: 0,
        }
    }

    pub fn new_simple_specific(type_: Specific, locality: Locality) -> Self {
        let flags = Self::calculate_flags(PointType::Specific, type_ as u32, locality);
        Self {
            flags,
            node_index: 0,
        }
    }

    pub fn new_calculating() -> Self {
        Self {
            flags: Specific::Calculating as u32,
            node_index: 0,
        }
    }

    pub fn new_specific(type_: Specific, node_index: NodeIndex, locality: Locality) -> Self {
        todo!()
    }

    pub fn new_file_reference(file: FileIndex, locality: Locality) -> Self {
        let flags = Self::calculate_flags(PointType::FileReference, file.0, locality);
        Self {
            flags,
            node_index: 0,
        }
    }

    pub fn new_node_analysis(locality: Locality) -> Self {
        Self {
            flags: Self::calculate_flags(PointType::NodeAnalysis, 0, locality),
            node_index: 0,
        }
    }

    pub fn new_node_analysis_with_node_index(locality: Locality, node_index: NodeIndex) -> Self {
        Self {
            flags: Self::calculate_flags(PointType::NodeAnalysis, node_index, locality),
            node_index,
        }
    }

    pub fn new_uncalculated() -> Self {
        Self {
            flags: 0,
            node_index: 0,
        }
    }

    pub fn type_(self) -> PointType {
        debug_assert!(self.calculated());
        unsafe { mem::transmute((self.flags & TYPE_MASK) >> TYPE_BIT_INDEX) }
    }

    pub fn locality(self) -> Locality {
        unsafe { mem::transmute((self.flags & LOCALITY_MASK) >> LOCALITY_BIT_INDEX) }
    }

    pub fn calculated(self) -> bool {
        (self.flags & IS_ANALIZED_MASK) != 0
    }

    pub fn calculating(self) -> bool {
        self.flags == Specific::Calculating as u32
    }

    pub fn file_index(self) -> FileIndex {
        debug_assert!(
            self.type_() == PointType::Redirect || self.type_() == PointType::FileReference,
            "{:?}",
            self.type_()
        );
        FileIndex(self.flags & REST_MASK)
    }

    pub fn complex_index(self) -> usize {
        debug_assert!(
            self.type_() == PointType::Complex,
            "Expected complex, got {self:?}",
        );
        (self.flags & REST_MASK) as usize
    }

    pub fn maybe_complex_index(self) -> Option<usize> {
        if self.calculated() && self.type_() == PointType::Complex {
            return Some(self.complex_index());
        }
        None
    }

    pub fn node_index(self) -> NodeIndex {
        debug_assert!(
            self.type_() == PointType::Redirect
                || self.type_() == PointType::NodeAnalysis
                || self.type_() == PointType::MultiDefinition
        );
        self.node_index
    }

    pub fn as_redirected_node_ref(self, db: &Database) -> NodeRef {
        debug_assert!(self.type_() == PointType::Redirect);
        let file = db.loaded_python_file(self.file_index());
        NodeRef::new(file, self.node_index())
    }

    pub fn maybe_specific(self) -> Option<Specific> {
        if self.type_() == PointType::Specific {
            Some(self.specific())
        } else {
            None
        }
    }

    pub fn specific(self) -> Specific {
        debug_assert!(self.type_() == PointType::Specific, "{:?}", self);
        unsafe { mem::transmute(self.flags & SPECIFIC_MASK) }
    }
}

impl fmt::Debug for Point {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut s = f.debug_struct("Point");
        if self.calculating() {
            s.field("calculating", &self.calculating());
        } else if !self.calculated() {
            s.field("calculated", &self.calculated());
        } else {
            s.field("type", &self.type_())
                .field("locality", &self.locality())
                .field("node_index", &self.node_index);
            if self.type_() == PointType::Specific {
                s.field("specific", &self.specific());
            }
            if self.type_() == PointType::Redirect || self.type_() == PointType::FileReference {
                s.field("file_index", &self.file_index().0);
            }
        }
        s.finish()
    }
}

#[derive(Debug)]
pub struct Points(Vec<Cell<Point>>);

impl Points {
    pub fn new(length: usize) -> Self {
        Self(vec![Default::default(); length])
    }

    #[inline]
    pub fn get(&self, index: NodeIndex) -> Point {
        self.0[index as usize].get()
    }

    #[inline]
    pub fn set(&self, index: NodeIndex, point: Point) {
        self.0[index as usize].set(point);
    }

    pub fn invalidate_references_to(&mut self, file_index: FileIndex) {
        for cell in &self.0 {
            let locality = cell.get().locality();
            if locality == Locality::DirectExtern && cell.get().file_index() == file_index {
                cell.set(Point::new_uncalculated());
            } else if locality as u32 >= Locality::ComplexExtern as u32 {
                cell.set(Point::new_uncalculated())
            }
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
#[repr(u32)]
pub enum PointType {
    Specific,
    Redirect,
    MultiDefinition,
    Complex,
    // In case of a reference it's missing otherwise unknown.
    Unknown,
    FileReference,
    // Basically stuff like if/for nodes
    NodeAnalysis,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[repr(u32)]
pub enum Specific {
    // This is reserved, because if everything is initialized as zero, this is the value it takes.
    ReservedBecauseUnused,
    Calculating,
    Cycle,
    OverloadUnreachable,
    Any,

    String,
    Float,
    Complex,
    Bytes,
    Int,
    Bool,
    None,
    // Literals are used for things like Literal[42]
    StringLiteral,
    BytesLiteral,
    IntLiteral,
    BoolLiteral,

    Ellipsis,
    GeneratorComprehension,

    SelfParam,
    Param,
    LazyInferredClass, // A class that will be inferred later.
    DecoratedFunction, // A function that will be inferred later.
    Function,          // The node point so the index of the result
    Closure,           // TODO remove this?
    // NoReturnFunction,  // TODO Remove or use?
    AnnotationOrTypeCommentClassInstance,
    AnnotationOrTypeCommentWithTypeVars,
    SimpleGeneric, // primary: primary '[' slices ']'

    TypingProtocol,
    TypingGeneric,
    TypingTuple,
    TypingCallable,
    TypingType,
    TypingClassVar,
    TypingUnion,
    TypingOptional,
    TypingCast,
    TypingNewType,
    TypingTypeVarClass,
    TypingTypeVarTupleClass,
    TypingParamSpecClass,
    TypingConcatenateClass,
    TypingLiteralString,
    TypingUnpack,
    TypingTypeAlias,
    TypingFinal,
    TypingLiteral,
    TypingSelf,
    TypingAnnotated,
    // TODO maybe NoReturn?
    TypingAny,
    TypedDict,
    RevealTypeFunction,
    TypingNamedTuple,      // typing.NamedTuple
    CollectionsNamedTuple, // collections.namedtuple

    MypyExtensionsArg,
    MypyExtensionsDefaultArg,
    MypyExtensionsNamedArg,
    MypyExtensionsDefaultNamedArg,
    MypyExtensionsVarArg,
    MypyExtensionsKwArg,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[repr(u32)]
pub enum Locality {
    // Intern: 0xx
    Stmt,
    ClassOrFunction,
    MostOuterClassOrFunction,
    File,

    // Extern: 1xx
    DirectExtern,   // Contains a direct link that can be checked
    ComplexExtern,  // Means we have to recalculate the value all the links
    ImplicitExtern, // Contains star imports for now (always recheck on invalidation of the module)
    Todo,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct PointLink {
    pub file: FileIndex,
    pub node_index: NodeIndex,
}

impl PointLink {
    pub fn new(file: FileIndex, node_index: NodeIndex) -> Self {
        Self { file, node_index }
    }

    pub fn into_redirect_point(self, locality: Locality) -> Point {
        Point::new_redirect(self.file, self.node_index, locality)
    }
}

impl From<LocalityLink> for PointLink {
    fn from(item: LocalityLink) -> Self {
        PointLink::new(item.file, item.node_index)
    }
}

#[derive(Clone, Copy)]
pub struct LocalityLink {
    pub file: FileIndex,
    pub node_index: NodeIndex,
    pub locality: Locality,
}

impl LocalityLink {
    pub fn into_point_redirect(self) -> Point {
        Point::new_redirect(self.file, self.node_index, self.locality)
    }
}

// This is a core data structure and it should be kept as small as possible, because it's used in
// arrays. It therefore uses a lot of Rcs.
#[derive(Debug, Clone, PartialEq)]
pub enum ComplexPoint {
    TypeInstance(DbType),
    Class(Box<ClassStorage>),
    ClassInfos(Box<ClassInfos>),
    TypeVarLikes(TypeVarLikes),
    FunctionOverload(Box<OverloadDefinition>),
    NewTypeDefinition(Rc<NewType>),
    // e.g. X = NamedTuple('X', []), does not include classes.
    NamedTupleDefinition(Rc<DbType>),

    // Relevant for types only (not inference)
    TypeVarLike(TypeVarLike),
    TypeAlias(Box<TypeAlias>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypeArguments {
    pub args: TupleTypeArguments,
}

impl TypeArguments {
    pub fn new_fixed_length(args: Box<[TypeOrTypeVarTuple]>) -> Self {
        Self {
            args: TupleTypeArguments::FixedLength(args),
        }
    }

    pub fn new_arbitrary_length(arg: DbType) -> Self {
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
    TypeArgument(DbType),
    // For TypeVarTuple
    TypeArguments(TypeArguments),
    // For ParamSpec
    ParamSpecArgument(ParamSpecArgument),
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
        self.0
            .iter()
            .map(|g| Generic::new(g).format(format_data))
            .collect::<Vec<_>>()
            .join(", ")
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
    pub type_: DbType,
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

    pub fn iter(&self) -> impl Iterator<Item = &DbType> {
        self.entries.iter().map(|u| &u.type_)
    }

    pub fn sort_for_priority(&mut self) {
        self.entries.sort_by_key(|t| match t.type_ {
            DbType::Literal(_) => -1,
            DbType::None => 2,
            DbType::TypeVar(_) => 3,
            DbType::Any => 4,
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
                    .take_while(|t| matches!(t, DbType::Literal(_)))
                    .count();
                if count > 1 {
                    let lit = format!(
                        "Literal[{}]",
                        iterator
                            .by_ref()
                            .take(count)
                            .map(|t| match t.type_ {
                                DbType::Literal(l) => l.format_inner(format_data.db),
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
                (!format_as_optional || !matches!(e.type_, DbType::None))
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
    pub content: Rc<DirContent>,
}

impl Namespace {
    pub fn qualified_name(&self, db: &Database) -> String {
        db.vfs.dir_and_name(&self.path).1.into()
    }

    pub fn name(&self, db: &Database) -> &str {
        db.vfs.dir_and_name(&self.path).1
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
    pub fn new(functions: Box<[CallableContent]>) -> Self {
        debug_assert!(!functions.is_empty());
        Self(functions)
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

// PartialEq is only here for optimizations, it is not a reliable way to check if a type matches
// with another type.
#[derive(Debug, Clone, PartialEq)]
pub enum DbType {
    Class(PointLink, ClassGenerics),
    Union(UnionType),
    FunctionOverload(Rc<FunctionOverload>),
    TypeVar(TypeVarUsage),
    Type(Rc<DbType>),
    Tuple(Rc<TupleContent>),
    Callable(Rc<CallableContent>),
    RecursiveAlias(Rc<RecursiveAlias>),
    NewType(Rc<NewType>),
    ParamSpecArgs(ParamSpecUsage),
    ParamSpecKwargs(ParamSpecUsage),
    Literal(Literal),
    NamedTuple(Rc<NamedTuple>),
    Module(FileIndex),
    Namespace(Rc<Namespace>),
    Self_,
    None,
    Any,
    Never,
}

impl DbType {
    pub fn union(self, db: &Database, other: DbType) -> Self {
        self.union_with_details(db, other, false)
    }

    pub fn make_optional(&mut self, db: &Database) {
        *self = mem::replace(self, Self::Never).union_with_details(db, DbType::None, true);
    }

    pub fn union_with_details(
        self,
        db: &Database,
        other: DbType,
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
                    DbType::Never => (), // `X | Never is always X`
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
                    if self == other || matches!(other, DbType::Never) {
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

    pub fn union_in_place(&mut self, db: &Database, other: DbType) {
        *self = mem::replace(self, Self::Never).union(db, other);
    }

    pub fn format_short(&self, db: &Database) -> Box<str> {
        self.format(&FormatData::new_short(db))
    }
    pub fn format(&self, format_data: &FormatData) -> Box<str> {
        match self {
            Self::Class(link, generics) => {
                Class::from_db_type(format_data.db, *link, generics).format(format_data)
            }
            Self::Union(union) => union.format(format_data),
            Self::FunctionOverload(callables) => match format_data.style {
                FormatStyle::MypyRevealType => format!(
                    "Overload({})",
                    callables
                        .iter_functions()
                        .map(|t| t.format(format_data))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
                .into(),
                _ => Box::from("overloaded function"),
            },
            Self::TypeVar(t) => format_data.format_type_var_like(
                &TypeVarLikeUsage::TypeVar(Cow::Borrowed(t)),
                ParamsStyle::Unreachable,
            ),
            Self::Type(db_type) => format!("Type[{}]", db_type.format(format_data)).into(),
            Self::Tuple(content) => content.format(format_data),
            Self::Callable(content) => content.format(format_data).into(),
            Self::Any => Box::from("Any"),
            Self::None => Box::from("None"),
            Self::Never => Box::from("<nothing>"),
            Self::Literal(literal) => literal.format(format_data),
            Self::NewType(n) => n.format(format_data),
            Self::RecursiveAlias(rec) => {
                if let Some(generics) = &rec.generics {
                    let alias = rec.type_alias(format_data.db);
                    format!(
                        "{}[{}]",
                        alias.name(format_data.db).unwrap(),
                        generics.format(format_data)
                    )
                    .into()
                } else if format_data.has_already_seen_recursive_alias(rec) {
                    let alias = rec.type_alias(format_data.db);
                    Box::from(alias.name(format_data.db).unwrap())
                } else {
                    let format_data = format_data.with_seen_recursive_alias(rec);
                    rec.calculated_db_type(format_data.db).format(&format_data)
                }
            }
            Self::Self_ => Box::from("Self"),
            Self::ParamSpecArgs(usage) => {
                format!("{}.args", usage.param_spec.name(format_data.db)).into()
            }
            Self::ParamSpecKwargs(usage) => {
                format!("{}.kwargs", usage.param_spec.name(format_data.db)).into()
            }
            Self::NamedTuple(nt) => {
                use crate::type_helpers::NamedTupleValue;
                match format_data.style {
                    FormatStyle::Short => NamedTupleValue::new(format_data.db, nt)
                        .format_with_name(
                            format_data,
                            nt.name(format_data.db),
                            Generics::NotDefinedYet,
                        ),
                    _ => NamedTupleValue::new(format_data.db, nt).format_with_name(
                        format_data,
                        &nt.qualified_name(format_data.db),
                        Generics::NotDefinedYet,
                    ),
                }
            }
            Self::Module(file_index) => format_data
                .db
                .python_state
                .module_db_type()
                .format(format_data),
            Self::Namespace(_) => "object".into(),
        }
    }

    pub fn expect_class_generics(&self) -> &GenericsList {
        match self {
            Self::Class(link, ClassGenerics::List(generics)) => generics,
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
            Self::Class(_, ClassGenerics::List(generics)) => {
                search_in_generics(found_type_var, generics)
            }
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
            Self::Type(db_type) => db_type.search_type_vars(found_type_var),
            Self::Tuple(content) => match &content.args {
                Some(TupleTypeArguments::FixedLength(ts)) => {
                    for t in ts.iter() {
                        match t {
                            TypeOrTypeVarTuple::Type(t) => t.search_type_vars(found_type_var),
                            TypeOrTypeVarTuple::TypeVarTuple(t) => {
                                found_type_var(TypeVarLikeUsage::TypeVarTuple(Cow::Borrowed(t)))
                            }
                        }
                    }
                }
                Some(TupleTypeArguments::ArbitraryLength(t)) => t.search_type_vars(found_type_var),
                None => (),
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
            | Self::NewType(_) => (),
            Self::RecursiveAlias(rec) => {
                if let Some(generics) = rec.generics.as_ref() {
                    search_in_generics(found_type_var, generics)
                }
            }
            Self::ParamSpecArgs(usage) => todo!(),
            Self::ParamSpecKwargs(usage) => todo!(),
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
            Self::Class(_, ClassGenerics::List(generics)) => {
                search_in_generics(generics, already_checked)
            }
            Self::Class(_, ClassGenerics::NotDefinedYet) => {
                todo!()
            }
            Self::Union(u) => u.iter().any(|t| t.has_any_internal(i_s, already_checked)),
            Self::FunctionOverload(intersection) => intersection
                .iter_functions()
                .any(|callable| callable.has_any_internal(i_s, already_checked)),
            Self::TypeVar(t) => false,
            Self::Type(db_type) => db_type.has_any_internal(i_s, already_checked),
            Self::Tuple(content) => content
                .args
                .as_ref()
                .map(|args| args.has_any_internal(i_s, already_checked))
                .unwrap_or(true),
            Self::Callable(content) => content.has_any_internal(i_s, already_checked),
            Self::Class(
                _,
                ClassGenerics::None
                | ClassGenerics::ExpressionWithClassType(_)
                | ClassGenerics::SlicesWithClassTypes(_),
            )
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
                        .db_type_if_valid()
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
            | Self::Namespace(_) => false,
            Self::NamedTuple(nt) => todo!(),
        }
    }

    pub fn has_self_type(&self) -> bool {
        match self {
            Self::Class(_, ClassGenerics::List(generics)) => generics.iter().any(|g| match g {
                GenericItem::TypeArgument(t) => t.has_self_type(),
                GenericItem::TypeArguments(_) => todo!(),
                GenericItem::ParamSpecArgument(params) => todo!(),
            }),
            Self::Union(u) => u.iter().any(|t| t.has_self_type()),
            Self::FunctionOverload(intersection) => {
                intersection.iter_functions().any(|t| t.has_self_type())
            }
            Self::Type(t) => t.has_self_type(),
            Self::Tuple(content) => content.args.as_ref().is_some_and(|args| match args {
                TupleTypeArguments::FixedLength(ts) => ts.iter().any(|t| match t {
                    TypeOrTypeVarTuple::Type(t) => t.has_self_type(),
                    TypeOrTypeVarTuple::TypeVarTuple(_) => false,
                }),
                TupleTypeArguments::ArbitraryLength(t) => t.has_self_type(),
            }),
            Self::Callable(content) => content.has_self_type(),
            Self::Self_ => true,
            Self::NamedTuple(_) => {
                debug!("TODO namedtuple has_self_type");
                false
            }
            Self::Class(..)
            | Self::None
            | Self::Never
            | Self::Literal { .. }
            | Self::Any
            | Self::NewType(_)
            | Self::ParamSpecArgs(_)
            | Self::ParamSpecKwargs(_)
            | Self::RecursiveAlias(_)
            | Self::Module(_)
            | Self::Namespace(_)
            | Self::TypeVar(_) => false,
        }
    }

    pub fn is_subclassable(&self) -> bool {
        matches!(
            self,
            Self::Class(..) | Self::Tuple(..) | Self::NewType(..) | Self::NamedTuple(_)
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FunctionKind {
    Function,
    Property,
    ClassMethod,
}

#[derive(Debug, Clone, PartialEq)]
pub struct OverloadDefinition {
    pub implementing_function: Option<CallableContent>,
    pub old_functions: Box<[PointLink]>,
    pub functions: Rc<FunctionOverload>,
}

impl OverloadDefinition {
    pub fn iter_functions(&self) -> impl Iterator<Item = &CallableContent> {
        self.functions.iter_functions()
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeOrTypeVarTuple {
    Type(DbType),
    TypeVarTuple(TypeVarTupleUsage),
}

impl TypeOrTypeVarTuple {
    #[allow(dead_code)] // TODO remove this
    fn as_db_type(&self) -> DbType {
        match self {
            Self::Type(t) => t.clone(),
            Self::TypeVarTuple(t) => {
                DbType::Tuple(Rc::new(TupleContent::new_fixed_length(Box::new([
                    TypeOrTypeVarTuple::TypeVarTuple(t.clone()),
                ]))))
            }
        }
    }

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
    FixedLength(Box<[TypeOrTypeVarTuple]>),
    ArbitraryLength(Box<DbType>),
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

    fn common_base_type(&self, i_s: &InferenceState) -> DbType {
        match self {
            Self::FixedLength(ts) => common_base_type(i_s, ts.iter()),
            Self::ArbitraryLength(t) => t.as_ref().clone(),
        }
    }

    pub fn format(&self, format_data: &FormatData) -> Box<str> {
        match self {
            Self::FixedLength(ts) => ts
                .iter()
                .map(|g| g.format(format_data))
                .collect::<Vec<_>>()
                .join(", ")
                .into(),
            Self::ArbitraryLength(t) => format!("{}, ...", t.format(format_data)).into(),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct TupleContent {
    pub args: Option<TupleTypeArguments>,
    tuple_class_generics: OnceCell<GenericsList>,
}

impl TupleContent {
    pub fn new(args: TupleTypeArguments) -> Self {
        Self {
            args: Some(args),
            tuple_class_generics: OnceCell::new(),
        }
    }

    pub fn new_fixed_length(args: Box<[TypeOrTypeVarTuple]>) -> Self {
        Self::new(TupleTypeArguments::FixedLength(args))
    }

    pub fn new_arbitrary_length(arg: DbType) -> Self {
        Self::new(TupleTypeArguments::ArbitraryLength(Box::new(arg)))
    }

    pub fn new_empty() -> Rc<Self> {
        EMPTY_TUPLE.with(|t| t.clone())
    }

    pub fn tuple_class_generics(&self, db: &Database) -> &GenericsList {
        self.tuple_class_generics.get_or_init(|| {
            GenericsList::new_generics(Rc::new([GenericItem::TypeArgument(
                self.args
                    .as_ref()
                    .map(|args| args.common_base_type(&InferenceState::new(db)))
                    .unwrap_or(DbType::Any),
            )]))
        })
    }

    pub fn format(&self, format_data: &FormatData) -> Box<str> {
        let base = match format_data.style {
            FormatStyle::Short => "tuple",
            FormatStyle::Qualified | FormatStyle::MypyRevealType => "builtins.tuple",
        };
        if let Some(args) = self.args.as_ref() {
            format!("{base}[{}]", args.format(format_data)).into()
        } else {
            format!("{base}[Any, ...]").into()
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum StarredParamSpecific {
    ArbitraryLength(DbType),
    ParamSpecArgs(ParamSpecUsage),
}

#[derive(Debug, Clone, PartialEq)]
pub enum DoubleStarredParamSpecific {
    ValueType(DbType),
    ParamSpecKwargs(ParamSpecUsage),
}

#[derive(Debug, Clone, PartialEq)]
pub enum ParamSpecific {
    PositionalOnly(DbType),
    PositionalOrKeyword(DbType),
    KeywordOnly(DbType),
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

    pub fn maybe_positional_db_type(&self) -> Option<&DbType> {
        match self {
            Self::PositionalOnly(t) | Self::PositionalOrKeyword(t) => Some(t),
            _ => None,
        }
    }

    pub fn expect_positional_db_type(self) -> DbType {
        match self {
            Self::PositionalOnly(t) | Self::PositionalOrKeyword(t) => t,
            _ => unreachable!(),
        }
    }

    pub fn expect_positional_db_type_as_ref(&self) -> &DbType {
        match &self {
            Self::PositionalOnly(t) | Self::PositionalOrKeyword(t) => t,
            _ => unreachable!(),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct CallableParam {
    pub param_specific: ParamSpecific,
    pub name: Option<StringSlice>,
    pub has_default: bool,
}

impl CallableParam {
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
            } else if let Some(name) = self.name {
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
    pub name: Option<StringSlice>,
    pub class_name: Option<StringSlice>,
    pub defined_at: PointLink,
    pub kind: FunctionKind,
    pub type_vars: Option<TypeVarLikes>,
    pub params: CallableParams,
    pub result_type: DbType,
}

impl CallableContent {
    pub fn new_any() -> Self {
        Self::new_any_with_defined_at(PointLink::new(FileIndex(0), 0))
    }

    pub fn new_any_with_defined_at(defined_at: PointLink) -> Self {
        Self {
            name: None,
            class_name: None,
            defined_at,
            kind: FunctionKind::Function,
            type_vars: None,
            params: CallableParams::Any,
            result_type: DbType::Any,
        }
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

    pub fn first_positional_type(&self) -> Option<&DbType> {
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
            CallableParams::Any => Some(&DbType::Any),
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

    fn has_self_type(&self) -> bool {
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
        let result = self.result_type.format(format_data);
        let params = self.params.format(
            format_data,
            match format_data.style {
                FormatStyle::MypyRevealType => ParamsStyle::FunctionParams,
                _ => ParamsStyle::CallableParams,
            },
        );
        match format_data.style {
            FormatStyle::MypyRevealType => {
                let type_vars = self.type_vars.as_ref().map(|t| {
                    format!(
                        " [{}]",
                        t.iter()
                            .map(|t| match t {
                                TypeVarLike::TypeVar(t) => {
                                    let mut name = t.name(format_data.db).to_owned();
                                    if let Some(bound) = &t.bound {
                                        name += " <: ";
                                        name += &bound.format(format_data);
                                    }
                                    name
                                }
                                TypeVarLike::TypeVarTuple(_) => todo!(),
                                TypeVarLike::ParamSpec(p) => p.name(format_data.db).to_owned(),
                            })
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                });
                let type_vars = type_vars.as_deref().unwrap_or("");
                if result.as_ref() == "None" {
                    format!("def{type_vars} ({params})")
                } else {
                    format!("def{type_vars} ({params}) -> {result}")
                }
            }
            _ => format!("Callable[{params}, {result}]"),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct NewType {
    pub name_string: PointLink,
    type_expression: PointLink,
    // TODO locality needs to be checked, because this is lazily calculated.
    type_: OnceCell<DbType>,
}

impl NewType {
    pub fn new(name_string: PointLink, type_expression: PointLink) -> Self {
        Self {
            name_string,
            type_expression,
            type_: OnceCell::new(),
        }
    }

    pub fn type_(&self, i_s: &InferenceState) -> &DbType {
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

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Literal {
    pub kind: LiteralKind,
    pub implicit: bool,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum LiteralKind {
    String(PointLink),
    Int(i64), // TODO this does not work for Python ints > usize
    Bytes(PointLink),
    Bool(bool),
}

#[derive(PartialEq, Eq, Debug)]
pub enum LiteralValue<'db> {
    String(Cow<'db, str>),
    Int(i64),
    Bytes(Cow<'db, [u8]>),
    Bool(bool),
}

impl Literal {
    pub fn value(self, db: &Database) -> LiteralValue {
        match self.kind {
            LiteralKind::Int(i) => LiteralValue::Int(i),
            LiteralKind::String(link) => {
                let node_ref = NodeRef::from_link(db, link);
                LiteralValue::String(
                    node_ref
                        .maybe_str()
                        .unwrap()
                        .as_python_string()
                        .into_cow()
                        .unwrap(), // Can unwrap, because we know that there was never an f-string.
                )
            }
            LiteralKind::Bool(b) => LiteralValue::Bool(b),
            LiteralKind::Bytes(link) => {
                let node_ref = NodeRef::from_link(db, link);
                LiteralValue::Bytes(node_ref.as_bytes_literal().content_as_bytes())
            }
        }
    }

    fn format_inner(self, db: &Database) -> Cow<str> {
        match self.value(db) {
            LiteralValue::String(s) => Cow::Owned(str_repr(s)),
            LiteralValue::Int(i) => Cow::Owned(format!("{i}")),
            LiteralValue::Bool(true) => Cow::Borrowed("True"),
            LiteralValue::Bool(false) => Cow::Borrowed("False"),
            LiteralValue::Bytes(b) => Cow::Owned(bytes_repr(b)),
        }
    }

    pub fn format(self, format_data: &FormatData) -> Box<str> {
        format!("Literal[{}]", self.format_inner(format_data.db)).into()
    }
}

#[derive(Debug, Clone)]
pub struct RecursiveAlias {
    pub link: PointLink,
    pub generics: Option<GenericsList>,
    pub calculated_db_type: OnceCell<DbType>,
}

impl RecursiveAlias {
    pub fn new(link: PointLink, generics: Option<GenericsList>) -> Self {
        Self {
            link,
            generics,
            calculated_db_type: OnceCell::new(),
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

#[derive(Debug)]
pub struct UnresolvedTypeVarLike {
    pub type_var_like: TypeVarLike,
    pub most_outer_callable: Option<PointLink>,
}

#[derive(Debug)]
pub struct CallableWithParent {
    pub defined_at: PointLink,
    pub parent_callable: Option<PointLink>,
}

struct CallableAncestors<'a> {
    callables: &'a [CallableWithParent],
    next: Option<PointLink>,
}

impl Iterator for CallableAncestors<'_> {
    type Item = PointLink;

    fn next(&mut self) -> Option<Self::Item> {
        // This algorithm seems a bit weird in terms of Big O, but it shouldn't matter at all,
        // because this will have at most 3-5 callables (more typical is 0-1).
        if let Some(next) = self.next {
            let result = next;
            for callable_with_parent in self.callables {
                if callable_with_parent.defined_at == next {
                    self.next = callable_with_parent.parent_callable;
                    return Some(result);
                }
            }
            self.next = None;
            Some(result)
        } else {
            None
        }
    }
}

#[derive(Default, Debug)]
pub struct TypeVarManager {
    pub type_vars: Vec<UnresolvedTypeVarLike>,
    callables: Vec<CallableWithParent>,
}

impl TypeVarManager {
    pub fn position(&self, type_var: &TypeVarLike) -> Option<usize> {
        self.type_vars
            .iter()
            .position(|t| &t.type_var_like == type_var)
    }

    pub fn add(
        &mut self,
        type_var_like: TypeVarLike,
        in_callable: Option<PointLink>,
    ) -> TypeVarIndex {
        if let Some(index) = self.position(&type_var_like) {
            self.type_vars[index].most_outer_callable = self.calculate_most_outer_callable(
                self.type_vars[index].most_outer_callable,
                in_callable,
            );
            index.into()
        } else {
            self.type_vars.push(UnresolvedTypeVarLike {
                type_var_like,
                most_outer_callable: in_callable,
            });
            (self.type_vars.len() - 1).into()
        }
    }

    pub fn register_callable(&mut self, c: CallableWithParent) {
        self.callables.push(c)
    }

    pub fn move_index(&mut self, old_index: TypeVarIndex, force_index: TypeVarIndex) {
        let removed = self.type_vars.remove(old_index.as_usize());
        self.type_vars.insert(force_index.as_usize(), removed);
    }

    pub fn has_late_bound_type_vars(&self) -> bool {
        self.type_vars
            .iter()
            .any(|t| t.most_outer_callable.is_some())
    }

    pub fn has_type_vars(&self) -> bool {
        !self.type_vars.is_empty()
    }

    pub fn has_type_var_tuples(&self) -> bool {
        self.type_vars
            .iter()
            .any(|t| matches!(t.type_var_like, TypeVarLike::TypeVarTuple(_)))
    }

    pub fn into_type_vars(self) -> TypeVarLikes {
        TypeVarLikes(
            self.type_vars
                .into_iter()
                .filter_map(|t| t.most_outer_callable.is_none().then_some(t.type_var_like))
                .collect(),
        )
    }

    pub fn iter(&self) -> impl Iterator<Item = &UnresolvedTypeVarLike> {
        self.type_vars.iter()
    }
    pub fn len(&self) -> usize {
        self.type_vars.len()
    }

    fn calculate_most_outer_callable(
        &self,
        first: Option<PointLink>,
        second: Option<PointLink>,
    ) -> Option<PointLink> {
        for ancestor1 in (CallableAncestors {
            callables: &self.callables,
            next: first,
        }) {
            for ancestor2 in (CallableAncestors {
                callables: &self.callables,
                next: second,
            }) {
                if ancestor1 == ancestor2 {
                    return Some(ancestor1);
                }
            }
        }
        None
    }

    fn remap_internal(&self, usage: &TypeVarLikeUsage) -> Option<(TypeVarIndex, PointLink)> {
        let mut index = 0;
        let mut in_definition = None;
        for t in self.type_vars.iter().rev() {
            let matched = match &t.type_var_like {
                TypeVarLike::TypeVar(type_var) => match usage {
                    TypeVarLikeUsage::TypeVar(u) => type_var.as_ref() == u.type_var.as_ref(),
                    _ => false,
                },
                TypeVarLike::TypeVarTuple(t) => match usage {
                    TypeVarLikeUsage::TypeVarTuple(u) => t.as_ref() == u.type_var_tuple.as_ref(),
                    _ => false,
                },
                TypeVarLike::ParamSpec(p) => match usage {
                    TypeVarLikeUsage::ParamSpec(u) => p.as_ref() == u.param_spec.as_ref(),
                    _ => false,
                },
            };
            if matched {
                if t.most_outer_callable.is_some() {
                    in_definition = t.most_outer_callable;
                } else {
                    return None;
                }
            } else if in_definition == t.most_outer_callable {
                index += 1;
            }
        }
        in_definition.map(|d| (index.into(), d))
    }

    pub fn remap_type_var(&self, usage: &TypeVarUsage) -> TypeVarUsage {
        if let Some((index, in_definition)) =
            self.remap_internal(&TypeVarLikeUsage::TypeVar(Cow::Borrowed(usage)))
        {
            TypeVarUsage {
                type_var: usage.type_var.clone(),
                in_definition,
                index,
            }
        } else {
            usage.clone()
        }
    }

    pub fn remap_type_var_tuple(&self, usage: &TypeVarTupleUsage) -> TypeVarTupleUsage {
        todo!()
    }

    pub fn remap_param_spec(&self, usage: &ParamSpecUsage) -> ParamSpecUsage {
        if let Some((index, in_definition)) =
            self.remap_internal(&TypeVarLikeUsage::ParamSpec(Cow::Borrowed(usage)))
        {
            ParamSpecUsage {
                param_spec: usage.param_spec.clone(),
                in_definition,
                index,
            }
        } else {
            usage.clone()
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u32)]
pub enum Variance {
    Invariant = 0,
    Covariant,
    Contravariant,
}

impl Variance {
    pub fn invert(self) -> Self {
        match self {
            Variance::Covariant => Variance::Contravariant,
            Variance::Contravariant => Variance::Covariant,
            Variance::Invariant => Variance::Invariant,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypeVarLikes(Rc<[TypeVarLike]>);

impl TypeVarLikes {
    pub fn new(rc: Rc<[TypeVarLike]>) -> Self {
        Self(rc)
    }

    pub fn from_vec(vec: Vec<TypeVarLike>) -> Self {
        Self(Rc::from(vec))
    }

    pub fn into_vec(self) -> Vec<TypeVarLike> {
        Vec::from(self.0.as_ref())
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn find(
        &self,
        type_var_like: TypeVarLike,
        in_definition: PointLink,
    ) -> Option<TypeVarLikeUsage<'static>> {
        self.0
            .iter()
            .position(|t| t == &type_var_like)
            .map(|index| match type_var_like {
                TypeVarLike::TypeVar(type_var) => {
                    TypeVarLikeUsage::TypeVar(Cow::Owned(TypeVarUsage {
                        type_var,
                        index: index.into(),
                        in_definition,
                    }))
                }
                TypeVarLike::TypeVarTuple(type_var_tuple) => {
                    TypeVarLikeUsage::TypeVarTuple(Cow::Owned(TypeVarTupleUsage {
                        type_var_tuple,
                        index: index.into(),
                        in_definition,
                    }))
                }
                TypeVarLike::ParamSpec(param_spec) => {
                    TypeVarLikeUsage::ParamSpec(Cow::Owned(ParamSpecUsage {
                        param_spec,
                        index: index.into(),
                        in_definition,
                    }))
                }
            })
    }

    pub fn as_any_generic_list(&self) -> GenericsList {
        GenericsList::new_generics(self.iter().map(|tv| tv.as_any_generic_item()).collect())
    }

    pub fn iter(&self) -> std::slice::Iter<TypeVarLike> {
        self.0.iter()
    }
}

impl std::ops::Index<usize> for TypeVarLikes {
    type Output = TypeVarLike;

    fn index(&self, index: usize) -> &TypeVarLike {
        &self.0[index]
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeVarLike {
    TypeVar(Rc<TypeVar>),
    TypeVarTuple(Rc<TypeVarTuple>),
    ParamSpec(Rc<ParamSpec>),
}

impl TypeVarLike {
    pub fn name<'db>(&self, db: &'db Database) -> &'db str {
        match self {
            Self::TypeVar(t) => t.name(db),
            Self::TypeVarTuple(t) => todo!(), //t.name(db),
            Self::ParamSpec(s) => s.name(db),
        }
    }

    pub fn as_type_var_like_usage(
        &self,
        index: TypeVarIndex,
        in_definition: PointLink,
    ) -> TypeVarLikeUsage<'static> {
        match self {
            Self::TypeVar(type_var) => TypeVarLikeUsage::TypeVar(Cow::Owned(TypeVarUsage {
                type_var: type_var.clone(),
                index,
                in_definition,
            })),
            Self::TypeVarTuple(t) => {
                TypeVarLikeUsage::TypeVarTuple(Cow::Owned(TypeVarTupleUsage {
                    type_var_tuple: t.clone(),
                    index,
                    in_definition,
                }))
            }
            Self::ParamSpec(p) => TypeVarLikeUsage::ParamSpec(Cow::Owned(ParamSpecUsage {
                param_spec: p.clone(),
                index,
                in_definition,
            })),
        }
    }

    pub fn as_any_generic_item(&self) -> GenericItem {
        match self {
            TypeVarLike::TypeVar(_) => GenericItem::TypeArgument(DbType::Any),
            TypeVarLike::TypeVarTuple(_) => {
                GenericItem::TypeArguments(TypeArguments::new_arbitrary_length(DbType::Any))
            }
            TypeVarLike::ParamSpec(_) => {
                GenericItem::ParamSpecArgument(ParamSpecArgument::new_any())
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeVarName {
    PointLink(PointLink),
    Self_,
}

#[derive(Debug, Clone)]
pub struct TypeVar {
    pub name_string: TypeVarName,
    pub restrictions: Box<[DbType]>,
    pub bound: Option<DbType>,
    pub variance: Variance,
}

impl PartialEq for TypeVar {
    fn eq(&self, other: &Self) -> bool {
        self.name_string == other.name_string
    }
}

impl TypeVar {
    pub fn name<'db>(&self, db: &'db Database) -> &'db str {
        match self.name_string {
            TypeVarName::PointLink(link) => {
                NodeRef::from_link(db, link).maybe_str().unwrap().content()
            }
            TypeVarName::Self_ => "Self",
        }
    }

    pub fn qualified_name(&self, db: &Database) -> Box<str> {
        match self.name_string {
            TypeVarName::PointLink(link) => {
                let node_ref = NodeRef::from_link(db, link);
                format!(
                    "{}.{}",
                    node_ref.in_module().qualified_name(db),
                    node_ref.maybe_str().unwrap().content()
                )
                .into()
            }
            TypeVarName::Self_ => Box::from("Self"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct TypeVarTuple {
    pub name_string: PointLink,
    pub default: Option<DbType>,
}

impl TypeVarTuple {
    pub fn name<'db>(&self, db: &'db Database) -> &'db str {
        NodeRef::from_link(db, self.name_string)
            .maybe_str()
            .unwrap()
            .content()
    }
}

impl PartialEq for TypeVarTuple {
    fn eq(&self, other: &Self) -> bool {
        self.name_string == other.name_string
    }
}

#[derive(Debug, Clone)]
pub struct ParamSpec {
    pub name_string: PointLink,
}

impl ParamSpec {
    pub fn name<'db>(&self, db: &'db Database) -> &'db str {
        NodeRef::from_link(db, self.name_string)
            .maybe_str()
            .unwrap()
            .content()
    }
}

impl PartialEq for ParamSpec {
    fn eq(&self, other: &Self) -> bool {
        self.name_string == other.name_string
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct TypeVarUsage {
    pub type_var: Rc<TypeVar>,
    pub index: TypeVarIndex,
    pub in_definition: PointLink,
}

#[derive(Debug, PartialEq, Clone)]
pub struct TypeVarTupleUsage {
    pub type_var_tuple: Rc<TypeVarTuple>,
    pub index: TypeVarIndex,
    pub in_definition: PointLink,
}

#[derive(Debug, PartialEq, Clone)]
pub struct ParamSpecUsage {
    pub param_spec: Rc<ParamSpec>,
    pub index: TypeVarIndex,
    pub in_definition: PointLink,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ParamSpecTypeVars {
    pub type_vars: TypeVarLikes,
    pub in_definition: PointLink,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ParamSpecArgument {
    pub params: CallableParams,
    pub type_vars: Option<ParamSpecTypeVars>,
}

impl ParamSpecArgument {
    pub fn new(params: CallableParams, type_vars: Option<ParamSpecTypeVars>) -> Self {
        Self { params, type_vars }
    }

    pub fn new_any() -> Self {
        Self {
            params: CallableParams::Any,
            type_vars: None,
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum TypeVarLikeUsage<'a> {
    TypeVar(Cow<'a, TypeVarUsage>),
    TypeVarTuple(Cow<'a, TypeVarTupleUsage>),
    ParamSpec(Cow<'a, ParamSpecUsage>),
}

impl<'a> TypeVarLikeUsage<'a> {
    pub fn in_definition(&self) -> PointLink {
        match self {
            Self::TypeVar(t) => t.in_definition,
            Self::TypeVarTuple(t) => t.in_definition,
            Self::ParamSpec(p) => p.in_definition,
        }
    }

    pub fn add_to_index(&mut self, amount: i32) {
        match self {
            Self::TypeVar(t) => t.to_mut().index += amount,
            Self::TypeVarTuple(t) => t.to_mut().index += amount,
            Self::ParamSpec(p) => p.to_mut().index += amount,
        }
    }

    pub fn index(&self) -> TypeVarIndex {
        match self {
            Self::TypeVar(t) => t.index,
            Self::TypeVarTuple(t) => t.index,
            Self::ParamSpec(p) => p.index,
        }
    }

    pub fn as_type_var_like(&self) -> TypeVarLike {
        match self {
            Self::TypeVar(t) => TypeVarLike::TypeVar(t.type_var.clone()),
            Self::TypeVarTuple(t) => TypeVarLike::TypeVarTuple(t.type_var_tuple.clone()),
            Self::ParamSpec(p) => TypeVarLike::ParamSpec(p.param_spec.clone()),
        }
    }

    pub fn into_generic_item(self) -> GenericItem {
        match self {
            TypeVarLikeUsage::TypeVar(usage) => {
                GenericItem::TypeArgument(DbType::TypeVar(usage.into_owned()))
            }
            TypeVarLikeUsage::TypeVarTuple(usage) => {
                todo!()
            }
            TypeVarLikeUsage::ParamSpec(usage) => {
                GenericItem::ParamSpecArgument(ParamSpecArgument::new(
                    CallableParams::WithParamSpec(Rc::new([]), usage.into_owned()),
                    None,
                ))
            }
        }
    }

    pub fn into_generic_item_with_new_index(self, index: TypeVarIndex) -> GenericItem {
        match self {
            TypeVarLikeUsage::TypeVar(usage) => {
                let mut usage = usage.into_owned();
                usage.index = index;
                GenericItem::TypeArgument(DbType::TypeVar(usage))
            }
            TypeVarLikeUsage::TypeVarTuple(usage) => {
                let mut usage = usage.into_owned();
                usage.index = index;
                todo!()
            }
            TypeVarLikeUsage::ParamSpec(usage) => {
                let mut usage = usage.into_owned();
                usage.index = index;
                GenericItem::ParamSpecArgument(ParamSpecArgument::new(
                    CallableParams::WithParamSpec(Rc::new([]), usage),
                    None,
                ))
            }
        }
    }

    pub fn update_in_definition_and_index(
        &mut self,
        in_definition: PointLink,
        index: TypeVarIndex,
    ) {
        match self {
            Self::TypeVar(t) => {
                let t = t.to_mut();
                t.index = index;
                t.in_definition = in_definition;
            }
            Self::TypeVarTuple(t) => {
                let t = t.to_mut();
                t.index = index;
                t.in_definition = in_definition;
            }
            Self::ParamSpec(p) => {
                let p = p.to_mut();
                p.index = index;
                p.in_definition = in_definition;
            }
        }
    }

    pub fn format_without_matcher(
        &self,
        db: &Database,
        style: FormatStyle,
        params_style: ParamsStyle,
    ) -> Box<str> {
        match self {
            Self::TypeVar(type_var_usage) => type_var_usage.type_var.name(db).into(),
            Self::TypeVarTuple(t) => format!("*{}", t.type_var_tuple.name(db)).into(),
            Self::ParamSpec(p) => {
                let name = p.param_spec.name(db);
                match params_style {
                    ParamsStyle::FunctionParams => format!("*{name}.args, **{name}.kwargs").into(),
                    ParamsStyle::CallableParams => name.into(),
                    ParamsStyle::CallableParamsInner => format!("**{}", name).into(),
                    ParamsStyle::Unreachable => unreachable!(),
                }
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum CallableParams {
    Simple(Rc<[CallableParam]>),
    WithParamSpec(Rc<[DbType]>, ParamSpecUsage),
    Any,
}

impl CallableParams {
    pub fn format(&self, format_data: &FormatData, style: ParamsStyle) -> Box<str> {
        let parts = match self {
            Self::Simple(params) => {
                let mut out_params = Vec::with_capacity(params.len());
                // Display a star only if we are displaying a "normal" function signature
                let mut display_star = !matches!(style, ParamsStyle::FunctionParams);
                let mut had_param_spec_args = false;
                for (i, param) in params.iter().enumerate() {
                    if !display_star {
                        match param.param_specific {
                            ParamSpecific::KeywordOnly(_) => {
                                display_star = true;
                                out_params.push(Box::from("*"));
                            }
                            ParamSpecific::Starred(_) => display_star = true,
                            _ => (),
                        }
                    }
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
                if matches!(style, ParamsStyle::CallableParams) {
                    return spec;
                }
                let parts = pre_types.iter().map(|t| t.format(format_data));
                if spec.is_empty() {
                    parts.collect()
                } else {
                    parts.chain(std::iter::once(spec)).collect()
                }
            }
            Self::Any => {
                return match style {
                    ParamsStyle::FunctionParams => Box::from("*Any, **Any"),
                    _ => Box::from("..."),
                }
            }
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

#[derive(Debug, PartialEq, Clone)]
pub struct NamedTuple {
    pub name: StringSlice,
    // Basically __new__
    pub constructor: Rc<CallableContent>,
    tuple: OnceCell<Rc<TupleContent>>,
}

impl NamedTuple {
    pub fn new(name: StringSlice, constructor: CallableContent) -> Self {
        Self {
            name,
            constructor: Rc::new(constructor),
            tuple: OnceCell::new(),
        }
    }

    pub fn clone_with_new_init_class(&self, name: StringSlice) -> Rc<NamedTuple> {
        let mut nt = self.clone();
        let mut callable = nt.constructor.as_ref().clone();
        callable.name = Some(name);
        nt.constructor = Rc::new(callable);
        Rc::new(nt)
    }

    pub fn params(&self) -> &[CallableParam] {
        let CallableParams::Simple(params) = &self.constructor.params else {
            unreachable!();
        };
        params
    }

    pub fn name<'a>(&self, db: &'a Database) -> &'a str {
        self.name.as_str(db)
    }

    pub fn qualified_name(&self, db: &Database) -> String {
        let module = Module::from_file_index(db, self.name.file_index).qualified_name(db);
        format!("{module}.{}", self.name(db))
    }

    pub fn as_tuple(&self) -> &TupleContent {
        self.tuple.get_or_init(|| {
            Rc::new(TupleContent::new_fixed_length(
                self.params()
                    .iter()
                    .map(|t| {
                        TypeOrTypeVarTuple::Type(
                            t.param_specific.expect_positional_db_type_as_ref().clone(),
                        )
                    })
                    .collect::<Box<_>>(),
            ))
        })
    }
}

#[derive(Debug, PartialEq, Clone)]
struct CalculatedTypeAlias {
    // This is intentionally private, it should not be used anywhere else, because the behavior of
    // a type alias that has `is_recursive` is different.
    db_type: Rc<DbType>,
    is_recursive: bool,
}

#[derive(Debug, PartialEq, Clone)]
enum TypeAliasState {
    Valid(CalculatedTypeAlias),
    Invalid,
}

#[derive(Debug, PartialEq, Clone)]
pub struct TypeAlias {
    pub type_vars: Option<TypeVarLikes>,
    pub location: PointLink,
    pub name: Option<PointLink>,
    // The two attributes around is_recursive are calculated after the TypeAlias is
    // added to the DB.
    state: OnceCell<TypeAliasState>,
}

impl TypeAlias {
    pub fn new(
        type_vars: Option<TypeVarLikes>,
        location: PointLink,
        name: Option<PointLink>,
    ) -> Self {
        Self {
            type_vars,
            location,
            name,
            state: OnceCell::new(),
        }
    }

    pub fn new_valid(
        type_vars: Option<TypeVarLikes>,
        location: PointLink,
        name: Option<PointLink>,
        db_type: Rc<DbType>,
        is_recursive: bool,
    ) -> Self {
        let slf = Self::new(type_vars, location, name);
        slf.state
            .set(TypeAliasState::Valid(CalculatedTypeAlias {
                db_type,
                is_recursive,
            }))
            .unwrap();
        slf
    }

    pub fn is_recursive(&self) -> bool {
        match self.state.get().unwrap() {
            TypeAliasState::Invalid => unreachable!(),
            TypeAliasState::Valid(a) => a.is_recursive,
        }
    }

    pub fn is_invalid(&self) -> bool {
        matches!(self.state.get().unwrap(), TypeAliasState::Invalid)
    }

    pub fn db_type_if_valid(&self) -> &DbType {
        match self.state.get().unwrap() {
            TypeAliasState::Invalid => unreachable!(),
            TypeAliasState::Valid(a) => a.db_type.as_ref(),
        }
    }

    pub fn calculating(&self) -> bool {
        self.state.get().is_none()
    }

    pub fn set_valid(&self, db_type: DbType, is_recursive: bool) {
        self.state
            .set(TypeAliasState::Valid(CalculatedTypeAlias {
                db_type: Rc::new(db_type),
                is_recursive,
            }))
            .unwrap()
    }

    pub fn set_invalid(&self) {
        self.state.set(TypeAliasState::Invalid).unwrap()
    }

    pub fn name<'db>(&self, db: &'db Database) -> Option<&'db str> {
        self.name.map(|name| NodeRef::from_link(db, name).as_code())
    }

    pub fn is_class(&self) -> bool {
        !self.is_invalid() && matches!(self.db_type_if_valid(), DbType::Class(_, _))
    }
}

impl fmt::Debug for Database {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("Database")
            .field("file_count", &self.files.len())
            .finish()
    }
}

pub struct Database {
    in_use: bool,
    pub vfs: Box<dyn Vfs>,
    file_state_loaders: FileStateLoaders,
    files: InsertOnlyVec<dyn FileState>,
    path_to_file: HashMap<&'static str, FileIndex>,
    pub workspaces: Workspaces,
    in_memory_files: HashMap<Box<str>, FileIndex>,

    pub python_state: PythonState,
}

impl Database {
    pub fn new(file_state_loaders: FileStateLoaders, project: PythonProject) -> Self {
        let mut workspaces = Workspaces::default();
        for p in &project.sys_path {
            workspaces.add(file_state_loaders.as_ref(), p.to_owned())
        }
        workspaces.add(file_state_loaders.as_ref(), project.path.clone());
        let mut this = Self {
            in_use: false,
            vfs: Box::<FileSystemReader>::default(),
            file_state_loaders,
            files: Default::default(),
            path_to_file: Default::default(),
            workspaces,
            in_memory_files: Default::default(),
            python_state: PythonState::reserve(project),
        };
        this.initial_python_load();
        this
    }

    pub fn acquire(&mut self) {
        assert!(!self.in_use);
        self.in_use = true;
    }

    pub fn release(&mut self) {
        assert!(self.in_use);
        self.in_use = false;
        // todo handle watcher events here
    }

    pub fn file_state(&self, index: FileIndex) -> &(dyn FileState + 'static) {
        self.files.get(index.0 as usize).unwrap()
    }

    pub fn file_state_mut(&mut self, index: FileIndex) -> &mut (dyn FileState + 'static) {
        &mut self.files[index.0 as usize]
    }

    pub fn file_path(&self, index: FileIndex) -> &str {
        self.file_state(index).path()
    }

    pub fn file_state_index_by_path(&self, path: &str) -> Option<FileIndex> {
        self.path_to_file.get(path).copied()
    }

    pub fn loaded_file(&self, index: FileIndex) -> &(dyn File + 'static) {
        let f = self.file_state(index).file(&*self.vfs).unwrap();
        f.ensure_initialized(&self.python_state.project);
        f
    }

    fn loader(&self, path: &str) -> Option<&dyn FileStateLoader> {
        for loader in self.file_state_loaders.iter() {
            let extension = Path::new(path).extension().and_then(|e| e.to_str());
            if let Some(e) = extension {
                if loader.responsible_for_file_endings().contains(&e) {
                    return Some(loader.as_ref());
                }
            } else {
                return Some(&PythonFileLoader {});
            }
        }
        None
    }

    fn add_file_state(&self, file_state: Pin<Box<dyn FileState>>) -> FileIndex {
        self.files.push(file_state);
        let file_index = FileIndex(self.files.len() as u32 - 1);
        self.files.last().unwrap().set_file_index(file_index);
        file_index
    }

    fn update_file_state(&mut self, file_index: FileIndex, file_state: Pin<Box<dyn FileState>>) {
        file_state.set_file_index(file_index);
        self.files.set(file_index.0 as usize, file_state);
    }

    pub fn load_sub_file(&self, file: PythonFile) -> &PythonFile {
        let index = self.add_file_state(Box::pin(LanguageFileState::new_parsed("".into(), file)));
        self.loaded_python_file(index)
    }

    pub fn load_file_from_workspace(
        &self,
        dir: Rc<DirContent>,
        path: Box<str>,
        index: &WorkspaceFileIndex,
    ) {
        // A loader should be available for all files in the workspace.
        let loader = self.loader(&path).unwrap();
        let file_index = self.add_file_state(if let Some(code) = self.vfs.read_file(&path) {
            loader.load_parsed(dir, path, code.into())
        } else {
            //loader.inexistent_file_state(path)
            todo!()
        });
        index.set(file_index);
    }

    pub fn load_in_memory_file(&mut self, path: Box<str>, code: Box<str>) -> FileIndex {
        // First unload the old file, if there is already one
        let in_mem_file = self.in_memory_file(&path);
        if let Some(file_index) = in_mem_file {
            self.unload_file(file_index);
        }

        // Then load the new one
        let ensured = self.workspaces.ensure_file(&*self.vfs, &path);
        // TODO there could be no loader...
        let loader = self.loader(&path).unwrap();
        let file_state = loader.load_parsed(ensured.directory.clone(), path.clone(), code);
        let file_index = if let Some(file_index) = in_mem_file {
            self.update_file_state(file_index, file_state);
            file_index
        } else {
            let file_index = self.add_file_state(file_state);
            self.in_memory_files.insert(path.clone(), file_index);
            file_index
        };
        ensured.set_file_index(file_index);
        if cfg!(feature = "zuban_debug") {
            for invalidation in &ensured.invalidations.iter() {
                let p = self.file_state_mut(*invalidation).path();
                debug!("Invalidate {p} because we're loading {path}");
            }
        }
        self.invalidate_files(file_index, ensured.invalidations);
        file_index
    }

    pub fn in_memory_file(&mut self, path: &str) -> Option<FileIndex> {
        self.in_memory_files.get(path).cloned()
    }

    fn unload_file(&mut self, file_index: FileIndex) {
        let file_state = &mut self.files[file_index.0 as usize];
        self.workspaces.unload_file(&*self.vfs, file_state.path());
        let invalidations = file_state.unload_and_return_invalidations();
        self.invalidate_files(file_index, invalidations)
    }

    fn invalidate_files(&mut self, original_file_index: FileIndex, invalidations: Invalidations) {
        for invalid_index in invalidations.into_iter() {
            let file_state = self.file_state_mut(invalid_index);
            let invalidations = file_state.take_invalidations();
            if let Some(file) = file_state.maybe_loaded_file_mut() {
                file.invalidate_references_to(original_file_index);
            }

            if cfg!(feature = "zuban_debug") {
                for invalidation in &invalidations.iter() {
                    let p = self.file_state(*invalidation).path();
                    debug!(
                        "Invalidate {p} because we have invalidated {}",
                        self.file_state(invalid_index).path()
                    );
                }
            }
            self.invalidate_files(original_file_index, invalidations);
        }
    }

    pub fn add_invalidates(&self, file: FileIndex, invalidates: FileIndex) {
        self.file_state(file).add_invalidates(invalidates)
    }

    pub fn delete_directory(&mut self, mut dir_path: &str) -> Result<(), String> {
        if let Some(p) = dir_path.strip_suffix('/') {
            dir_path = p;
        }

        let indexes: Vec<_> = self
            .in_memory_files
            .iter()
            .filter_map(|(path, file_index)| {
                let matches = path.starts_with(dir_path)
                    && path
                        .as_bytes()
                        .get(dir_path.len())
                        .is_some_and(|chr| *chr == self.vfs.separator_u8());
                matches.then_some(*file_index)
            })
            .collect();
        for index in indexes {
            self.unload_file(index);
        }
        self.workspaces.delete_directory(&*self.vfs, dir_path)
    }

    pub fn unload_in_memory_file(&mut self, path: &str) -> Result<(), &'static str> {
        if let Some(file_index) = self.in_memory_files.get(path) {
            self.unload_file(*file_index);
            self.in_memory_files.remove(path);
            Ok(())
        } else {
            Err("The path is not known to be an in memory file")
        }
    }

    pub fn unload_all_in_memory_files(&mut self) {
        let in_memory_files = mem::take(&mut self.in_memory_files);
        for (path, file_index) in in_memory_files.into_iter() {
            self.unload_file(file_index);
        }
    }

    fn py_load_tmp(&self, dir: &Rc<DirContent>, p: &'static str) -> &PythonFile {
        // TODO give this function a better name and put it into a workspace
        let loader = self.loader(p).unwrap();
        let code = self.vfs.read_file(p).unwrap();
        let file_index =
            self.add_file_state(loader.load_parsed(dir.clone(), p.into(), code.into()));
        self.loaded_python_file(file_index)
    }

    pub fn loaded_python_file(&self, index: FileIndex) -> &PythonFile {
        self.loaded_file(index).as_any().downcast_ref().unwrap()
    }

    fn initial_python_load(&mut self) {
        // TODO this is wrong, because it's just a random dir...
        let dir = self.workspaces.directories().next().unwrap().1.clone();

        let builtins = self.py_load_tmp(&dir, "../typeshed/stdlib/builtins.pyi") as *const _;
        let typing = self.py_load_tmp(&dir, "../typeshed/stdlib/typing.pyi") as *const _;
        let typeshed =
            self.py_load_tmp(&dir, "../typeshed/stdlib/_typeshed/__init__.pyi") as *const _;
        let types = self.py_load_tmp(&dir, "../typeshed/stdlib/types.pyi") as *const _;
        let abc = self.py_load_tmp(&dir, "../typeshed/stdlib/abc.pyi") as *const _;
        let typing_extensions =
            self.py_load_tmp(&dir, "../typeshed/stdlib/typing_extensions.pyi") as *const _;
        let mypy_extensions = self.py_load_tmp(
            &dir,
            "../typeshed/stubs/mypy-extensions/mypy_extensions.pyi",
        ) as *const _;

        let collections_dir = match &dir.search("collections").unwrap().type_ {
            DirOrFile::Directory(c) => c.clone(),
            _ => unreachable!(),
        };
        let collections = self.py_load_tmp(
            &collections_dir.content,
            "../typeshed/stdlib/collections/__init__.pyi",
        ) as *const _;

        PythonState::initialize(
            self,
            builtins,
            typing,
            typeshed,
            collections,
            types,
            abc,
            typing_extensions,
            mypy_extensions,
        );
    }
}

#[derive(Debug)]
pub enum ParentScope {
    Module,
    Function(NodeIndex),
    Class(NodeIndex),
}

#[derive(Debug)]
pub struct ClassStorage {
    pub class_symbol_table: SymbolTable,
    pub self_symbol_table: SymbolTable,
    pub parent_scope: ParentScope,
    pub promote_to: Cell<Option<PointLink>>,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum MetaclassState {
    None,
    Unknown,
    Some(PointLink),
}

#[derive(Debug, Clone, PartialEq)]
pub enum ClassType {
    Normal,
    Protocol,
    NamedTuple(Rc<NamedTuple>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct BaseClass {
    pub type_: DbType,
    pub is_direct_base: bool,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ClassInfos {
    pub mro: Box<[BaseClass]>, // Does never include `object`
    pub metaclass: MetaclassState,
    pub class_type: ClassType,
    pub incomplete_mro: bool,
}

impl std::clone::Clone for ClassStorage {
    fn clone(&self) -> Self {
        unreachable!("This should never happen, because should never be cloned");
    }
}

impl std::cmp::PartialEq for ClassStorage {
    fn eq(&self, other: &Self) -> bool {
        unreachable!("Should never happen with classes")
    }
}

#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub enum FormatStyle {
    Short,
    Qualified,
    MypyRevealType,
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_sizes() {
        use super::*;
        use std::mem::size_of;
        assert_eq!(size_of::<ClassGenerics>(), 24);
        assert_eq!(size_of::<UnionType>(), 24);
        assert_eq!(size_of::<TupleContent>(), 40);
        assert_eq!(size_of::<DbType>(), 40); // TODO Would like it to be 32, but ClassGenerics is 24
        assert_eq!(size_of::<ComplexPoint>(), size_of::<DbType>());
        assert_eq!(size_of::<ClassStorage>(), 120);
        assert_eq!(size_of::<ClassInfos>(), 48);
        assert_eq!(size_of::<PointLink>(), 8);
        assert_eq!(size_of::<StringSlice>(), 12);
    }

    #[test]
    fn test_emtpy_point() {
        use super::*;
        let p = Point::new_simple_specific(Specific::ReservedBecauseUnused, Locality::Stmt);
        assert_eq!(p.flags & !IS_ANALIZED_MASK, 0);
        assert_eq!(p.node_index, 0);
        assert!(p.calculated());
        assert_eq!(p.type_(), PointType::Specific);
        assert_eq!(p.specific(), Specific::ReservedBecauseUnused);
    }
}
