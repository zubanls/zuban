use std::borrow::Cow;
use std::cell::Cell;
use std::collections::HashMap;
use std::fmt;
use std::mem;
use std::path::Path;
use std::pin::Pin;
use std::rc::Rc;

use once_cell::unsync::OnceCell;
use parsa_python_ast::{CodeIndex, NodeIndex, ParamKind};

use crate::file::PythonFile;
use crate::file_state::{
    File, FileState, FileStateLoader, FileSystemReader, LanguageFileState, PythonFileLoader, Vfs,
};
use crate::matching::{FormatData, Generics};
use crate::node_ref::NodeRef;
use crate::python_state::PythonState;
use crate::utils::{InsertOnlyVec, Invalidations, SymbolTable};
use crate::value::{Class, Value};
use crate::workspaces::{DirContent, DirOrFile, WorkspaceFileIndex, Workspaces};

pub type CallableParams = Option<Box<[CallableParam]>>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FileIndex(pub u32);
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd)]
pub struct TypeVarIndex(u32);
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MroIndex(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StringSlice {
    file_index: FileIndex,
    start: CodeIndex,
    end: u32,
}

impl StringSlice {
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
const IS_INVALIDATED_BIT_INDEX: usize = 30;
const LOCALITY_BIT_INDEX: usize = 27; // Uses 3 bits
const IN_MODULE_SCOPE_BIT_INDEX: usize = 26;
const IS_NULLABLE_BIT_INDEX: usize = 25;
const TYPE_BIT_INDEX: usize = 22; // Uses 3 bits

const REST_MASK: u32 = 0b11_1111_1111_1111_1111_1111;
const SPECIFIC_MASK: u32 = 0xFF; // 8 bits
const MAX_TYPE_VAR: u32 = 0xFF; // 256
const FILE_MASK: u32 = 0xFFFFFF; // 24 bits
const IS_ANALIZED_MASK: u32 = 1 << IS_ANALIZED_BIT_INDEX;
const IN_MODULE_SCOPE_MASK: u32 = 1 << IN_MODULE_SCOPE_BIT_INDEX;
const IS_NULLABLE_MASK: u32 = 1 << IN_MODULE_SCOPE_BIT_INDEX;
const LOCALITY_MASK: u32 = 0b111 << LOCALITY_BIT_INDEX;
const TYPE_MASK: u32 = 0b111 << TYPE_BIT_INDEX;

const IS_EXTERN_MASK: u32 = 1 << 30;

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

    pub fn new_unknown(file: FileIndex, locality: Locality) -> Self {
        let flags = Self::calculate_flags(PointType::Unknown, file.0, locality);
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
        let flags = Self::calculate_flags(PointType::FileReference, file.0 as u32, locality);
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

    fn is_recursion_error(self) -> bool {
        unimplemented!();
        //self.flags & REST_MASK & 1 == 1
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
        debug_assert!(self.type_() == PointType::Specific);
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

    String,
    Bytes,
    Float,
    Integer,
    Complex,
    Boolean,
    None,

    Ellipsis,
    GeneratorComprehension,
    List,
    ListComprehension,
    Dict,

    // SelfParam, TODO Use maybe?
    Param,
    LazyInferredClass,        // A class that will be inferred later.
    LazyInferredDynamicClass, // A class defined in a function that will be inferred later.
    LazyInferredFunction,     // A function that will be inferred later.
    LazyInferredClosure,      // A closure that will be inferred later.
    Function,                 // The node point so the index of the result
    Closure,
    NoReturnFunction,
    BoundMethod,

    InstanceWithArguments, // A primary node
    AnnotationClassInstance,
    AnnotationWithTypeVars,
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
    TypingTypeVarClass,
    TypingTypeVarTupleClass,
    TypingLiteralString,
    TypingUnpack,

    // TODO reactivate these or remove
    //TypingFinal,
    //TypingLiteral,
    //TypingTypeAlias,
    //TypingConcatenate,
    //TypingAnnotated,

    //TypingAliasClass,
    //TypingAliasInstance,
    TypingAny,
    //TypedDict,
    RevealTypeFunction,

    MypyExtensionsArg,
    MypyExtensionsDefaultArg,
    MypyExtensionsNamedArg,
    MypyExtensionsDefaultNamedArg,
    MypyExtensionsVarArg,
    MypyExtensionsKwArg,
}

#[derive(Debug, PartialEq, Eq)]
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

#[derive(Debug, Copy, Clone, PartialEq)]
pub struct PointLink {
    pub file: FileIndex,
    pub node_index: NodeIndex,
}

impl PointLink {
    pub fn new(file: FileIndex, node_index: NodeIndex) -> Self {
        Self { file, node_index }
    }
}

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

#[derive(Debug, Clone, PartialEq)]
pub enum AnyLink {
    Reference(PointLink),
    Complex(Box<ComplexPoint>),
    SimpleSpecific(Specific),
    Unknown,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ComplexPoint {
    Class(Box<ClassStorage>),
    Union(Box<[AnyLink]>),
    ExecutionInstance(PointLink, Box<Execution>),
    BoundMethod(AnyLink, MroIndex, PointLink),
    Closure(PointLink, Box<Execution>),
    GenericClass(PointLink, GenericsList),
    Instance(PointLink, Option<GenericsList>),
    ClassInfos(Box<ClassInfos>),
    TypeVarLikes(TypeVarLikes),
    FunctionOverload(Box<Overload>),
    TypeInstance(Box<DbType>),

    // Relevant for types only (not inference)
    TypeVarLike(Rc<TypeVarLike>),
    TypeAlias(Box<TypeAlias>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Execution {
    pub function: PointLink,
    pub in_: Option<Box<Execution>>,
    pub argument_node: PointLink,
}

impl Execution {
    pub fn new(function: PointLink, argument_node: PointLink, in_: Option<&Execution>) -> Self {
        Self {
            function,
            in_: in_.map(|x| Box::new(x.clone())),
            argument_node,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct GenericsList(Box<[DbType]>);

impl GenericsList {
    pub fn new_generics(parts: Box<[DbType]>) -> Self {
        Self(parts)
    }

    pub fn as_slice_ref(&self) -> &[DbType] {
        &self.0
    }

    pub fn generics_from_vec(parts: Vec<DbType>) -> Self {
        Self::new_generics(parts.into_boxed_slice())
    }

    pub fn nth(&self, index: TypeVarIndex) -> Option<&DbType> {
        self.0.get(index.0 as usize)
    }

    pub fn iter(&self) -> std::slice::Iter<DbType> {
        self.0.iter()
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn format(&self, format_data: &FormatData) -> Box<str> {
        self.0
            .iter()
            .map(|g| g.format(format_data))
            .collect::<Vec<_>>()
            .join(", ")
            .into()
    }
}

impl std::ops::Index<TypeVarIndex> for GenericsList {
    type Output = DbType;

    fn index(&self, index: TypeVarIndex) -> &DbType {
        &self.0[index.0 as usize]
    }
}

impl IntoIterator for GenericsList {
    type Item = DbType;
    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        Vec::from(self.0).into_iter()
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct IntersectionType {
    pub entries: Box<[DbType]>,
    pub format_as_overload: bool,
}

impl IntersectionType {
    pub fn new_overload(entries: Box<[DbType]>) -> Self {
        debug_assert!(entries.len() > 1);
        Self {
            entries,
            format_as_overload: true,
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = &DbType> {
        self.entries.iter()
    }

    pub fn format(&self, format_data: &FormatData) -> Box<str> {
        if self.format_as_overload {
            Box::from("overloaded function")
        } else {
            todo!()
        }
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
            DbType::TypeVarLike(_) => 2,
            DbType::None => 3,
            DbType::Any => 4,
            _ => t.type_.has_type_vars().into(),
        });
    }

    pub fn format(&self, format_data: &FormatData) -> Box<str> {
        let mut unsorted = self
            .entries
            .iter()
            .filter_map(|e| {
                (!self.format_as_optional || !matches!(e.type_, DbType::None))
                    .then(|| (e.format_index, e.type_.format(format_data)))
            })
            .collect::<Vec<_>>();
        unsorted.sort_by_key(|(format_index, _)| *format_index);
        let sorted = unsorted
            .into_iter()
            .map(|(_, t)| t)
            .collect::<Vec<_>>()
            .join(" | ")
            .into();
        if self.format_as_optional {
            format!("Optional[{sorted}]").into()
        } else {
            sorted
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum DbType {
    Class(PointLink, Option<GenericsList>),
    Union(UnionType),
    Intersection(IntersectionType),
    TypeVarLike(TypeVarUsage),
    Type(Box<DbType>),
    Tuple(TupleContent),
    Callable(Box<CallableContent>),
    RecursiveAlias(Rc<RecursiveAlias>),
    None,
    Any,
    Never,
}

impl DbType {
    pub fn union(self, other: DbType) -> Self {
        let mut format_as_optional = false;
        let entries = match self {
            Self::Union(u1) => {
                let mut vec = u1.entries.into_vec();
                match other {
                    Self::Union(u2) => {
                        format_as_optional |= u2.format_as_optional;
                        for mut o in u2.entries.into_vec().into_iter() {
                            if !vec.contains(&o) {
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

    pub fn union_in_place(&mut self, other: DbType) {
        *self = mem::replace(self, Self::Never).union(other);
    }

    pub fn format(&self, format_data: &FormatData) -> Box<str> {
        let class_name = |link| {
            let class = Class::from_position(
                NodeRef::from_link(format_data.db, link),
                Generics::Any,
                None,
            )
            .unwrap();
            match format_data.style {
                FormatStyle::Short => Box::from(class.name()),
                FormatStyle::Qualified | FormatStyle::MypyRevealType => {
                    class.qualified_name(format_data.db).into()
                }
            }
        };
        match self {
            Self::Class(link, None) => class_name(*link),
            Self::Class(link, Some(generics_lst)) => format!(
                "{}[{}]",
                &class_name(*link),
                generics_lst.format(format_data)
            )
            .into(),
            Self::Union(union) => union.format(format_data),
            Self::Intersection(intersection) => intersection.format(format_data),
            Self::TypeVarLike(t) => format_data.format_type_var(t),
            Self::Type(db_type) => format!("Type[{}]", db_type.format(format_data)).into(),
            Self::Tuple(content) => content.format(format_data),
            Self::Callable(content) => content.format(format_data).into(),
            Self::Any => Box::from("Any"),
            Self::None => Box::from("None"),
            Self::Never => Box::from("<nothing>"),
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
        }
    }

    pub fn expect_class_generics(&self) -> &GenericsList {
        match self {
            Self::Class(link, Some(generics)) => generics,
            _ => unreachable!(),
        }
    }

    pub fn search_type_vars(&self, found_type_var: &mut impl FnMut(&TypeVarUsage)) {
        let mut search_in_generics = |generics: &GenericsList| {
            for t in generics.iter() {
                t.search_type_vars(found_type_var);
            }
        };
        match self {
            Self::Class(_, Some(generics)) => search_in_generics(generics),
            Self::Union(u) => {
                for t in u.iter() {
                    t.search_type_vars(found_type_var);
                }
            }
            Self::Intersection(intersection) => {
                for t in intersection.iter() {
                    t.search_type_vars(found_type_var);
                }
            }
            Self::TypeVarLike(t) => found_type_var(t),
            Self::Type(db_type) => db_type.search_type_vars(found_type_var),
            Self::Tuple(content) => {
                if let Some(generics) = &content.generics {
                    search_in_generics(generics)
                }
            }
            Self::Callable(content) => {
                if let Some(params) = &content.params {
                    for param in params.iter() {
                        param.db_type.search_type_vars(found_type_var)
                    }
                }
                content.result_type.search_type_vars(found_type_var)
            }
            Self::Class(_, None) | Self::Any | Self::None | Self::Never => (),
            Self::RecursiveAlias(rec) => {
                if let Some(generics) = rec.generics.as_ref() {
                    search_in_generics(generics)
                }
            }
        }
    }

    fn has_type_vars(&self) -> bool {
        let mut result = false;
        self.search_type_vars(&mut |_| result = true);
        result
    }

    pub fn has_any(&self) -> bool {
        let search_in_generics = |generics: &GenericsList| generics.iter().any(|t| t.has_any());
        match self {
            Self::Class(_, Some(generics)) => search_in_generics(generics),
            Self::Union(u) => u.iter().any(|t| t.has_any()),
            Self::Intersection(intersection) => intersection.iter().any(|t| t.has_any()),
            Self::TypeVarLike(t) => false,
            Self::Type(db_type) => db_type.has_any(),
            Self::Tuple(content) => {
                if let Some(generics) = &content.generics {
                    search_in_generics(generics)
                } else {
                    true
                }
            }
            Self::Callable(content) => {
                if let Some(params) = &content.params {
                    params.iter().any(|param| param.db_type.has_any())
                } else {
                    true
                }
            }
            Self::Class(_, None) | Self::None | Self::Never => false,
            Self::Any => true,
            Self::RecursiveAlias(_) => todo!(),
        }
    }

    pub fn replace_type_vars(&self, callable: &mut impl FnMut(&TypeVarUsage) -> Self) -> Self {
        let mut remap_generics = |generics: &GenericsList| {
            GenericsList::new_generics(
                generics
                    .iter()
                    .map(|g| g.replace_type_vars(callable))
                    .collect(),
            )
        };
        match self {
            Self::Any => Self::Any,
            Self::None => Self::None,
            Self::Never => Self::Never,
            Self::Class(link, generics) => {
                Self::Class(*link, generics.as_ref().map(remap_generics))
            }
            Self::Intersection(intersection) => Self::Intersection(IntersectionType {
                entries: intersection
                    .entries
                    .iter()
                    .map(|e| e.replace_type_vars(callable))
                    .collect(),
                format_as_overload: intersection.format_as_overload,
            }),
            Self::Union(u) => Self::Union(UnionType {
                entries: u
                    .entries
                    .iter()
                    .map(|e| UnionEntry {
                        type_: e.type_.replace_type_vars(callable),
                        format_index: e.format_index,
                    })
                    .collect(),
                format_as_optional: u.format_as_optional,
            }),
            Self::TypeVarLike(t) => callable(t),
            Self::Type(db_type) => Self::Type(Box::new(db_type.replace_type_vars(callable))),
            Self::Tuple(content) => Self::Tuple(TupleContent {
                generics: content
                    .generics
                    .as_ref()
                    .map(|generics| remap_generics(generics)),
                arbitrary_length: content.arbitrary_length,
            }),
            Self::Callable(content) => Self::Callable(Box::new(CallableContent {
                defined_at: content.defined_at,
                type_vars: content.type_vars.clone(), // TODO should this change as well?
                params: content.params.as_ref().map(|params| {
                    params
                        .iter()
                        .map(|p| CallableParam {
                            param_kind: p.param_kind,
                            has_default: p.has_default,
                            name: p.name,
                            db_type: p.db_type.replace_type_vars(callable),
                        })
                        .collect()
                }),
                result_type: content.result_type.replace_type_vars(callable),
            })),
            Self::RecursiveAlias(rec) => Self::RecursiveAlias(Rc::new(RecursiveAlias::new(
                rec.link,
                rec.generics.as_ref().map(remap_generics),
            ))),
        }
    }

    pub fn rewrite_late_bound_callables(&self, manager: &TypeVarManager) -> Self {
        let rewrite_generics = |generics: &GenericsList| {
            GenericsList::new_generics(
                generics
                    .iter()
                    .map(|g| g.rewrite_late_bound_callables(manager))
                    .collect(),
            )
        };
        match self {
            Self::Any => Self::Any,
            Self::None => Self::None,
            Self::Never => Self::Never,
            Self::Class(link, generics) => {
                Self::Class(*link, generics.as_ref().map(rewrite_generics))
            }
            Self::Union(u) => Self::Union(UnionType {
                entries: u
                    .entries
                    .iter()
                    .map(|e| UnionEntry {
                        type_: e.type_.rewrite_late_bound_callables(manager),
                        format_index: e.format_index,
                    })
                    .collect(),
                format_as_optional: u.format_as_optional,
            }),
            Self::Intersection(intersection) => Self::Intersection(IntersectionType {
                entries: intersection
                    .entries
                    .iter()
                    .map(|e| e.rewrite_late_bound_callables(manager))
                    .collect(),
                format_as_overload: intersection.format_as_overload,
            }),
            Self::TypeVarLike(t) => DbType::TypeVarLike(manager.remap_type_var(t)),
            Self::Type(db_type) => {
                Self::Type(Box::new(db_type.rewrite_late_bound_callables(manager)))
            }
            Self::Tuple(content) => Self::Tuple(TupleContent {
                generics: content
                    .generics
                    .as_ref()
                    .map(|generics| rewrite_generics(generics)),
                arbitrary_length: content.arbitrary_length,
            }),
            Self::Callable(content) => {
                let type_vars = manager
                    .type_vars
                    .iter()
                    .filter_map(|t| {
                        (t.most_outer_callable == Some(content.defined_at))
                            .then(|| t.type_var.clone())
                    })
                    .collect::<Box<_>>();
                Self::Callable(Box::new(CallableContent {
                    defined_at: content.defined_at,
                    type_vars: (!type_vars.is_empty()).then(|| TypeVarLikes(type_vars)),
                    params: content.params.as_ref().map(|params| {
                        params
                            .iter()
                            .map(|p| CallableParam {
                                param_kind: p.param_kind,
                                has_default: p.has_default,
                                name: p.name,
                                db_type: p.db_type.rewrite_late_bound_callables(manager),
                            })
                            .collect()
                    }),
                    result_type: content.result_type.rewrite_late_bound_callables(manager),
                }))
            }
            Self::RecursiveAlias(_) => todo!(),
        }
    }

    pub fn merge_matching_parts(self, other: Self) -> Self {
        if self == other {
            return self;
        }
        let merge_generics = |g1: Option<GenericsList>, g2: Option<GenericsList>| {
            g1.map(|g1| {
                GenericsList::new_generics(
                    g1.into_iter()
                        .zip(g2.unwrap().into_iter())
                        .map(|(t1, t2)| t1.merge_matching_parts(t2))
                        .collect(),
                )
            })
        };
        match self {
            Self::Class(link1, g1) => match other {
                Self::Class(link2, g2) if link1 == link2 => {
                    Self::Class(link1, merge_generics(g1, g2))
                }
                _ => Self::Any,
            },
            Self::Union(u1) => match other {
                Self::Union(u2) if u1.iter().all(|x| u2.iter().any(|y| x == y)) => Self::Union(u1),
                _ => Self::Any,
            },
            Self::Tuple(c1) => match other {
                Self::Tuple(c2) => Self::Tuple({
                    if c1.arbitrary_length == c2.arbitrary_length
                        && c1.generics.as_ref().map(|g| g.len())
                            == c2.generics.as_ref().map(|g| g.len())
                    {
                        TupleContent {
                            arbitrary_length: c1.arbitrary_length,
                            generics: merge_generics(c1.generics, c2.generics),
                        }
                    } else {
                        TupleContent::new_empty()
                    }
                }),
                _ => Self::Any,
            },
            Self::Callable(content1) => match other {
                Self::Callable(content2) => Self::Callable(Box::new(CallableContent {
                    defined_at: content1.defined_at,
                    type_vars: None,
                    params: None,
                    result_type: Self::Any,
                })),
                _ => Self::Any,
            },
            _ => Self::Any,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum FunctionType {
    Function,
    Property,
    ClassMethod,
    StaticMethod,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Overload {
    pub implementing_function: Option<PointLink>,
    pub functions: Box<[PointLink]>,
    pub function_type: FunctionType,
    pub is_async: bool,
}

impl Overload {
    pub fn add_another_overload(&self, function: PointLink) -> Self {
        let mut functions = Vec::with_capacity(self.functions.len() + 1);
        functions.extend_from_slice(self.functions.as_ref());
        functions.push(function);
        Self {
            implementing_function: self.implementing_function,
            functions: functions.into_boxed_slice(),
            function_type: self.function_type,
            is_async: self.is_async,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct TupleContent {
    pub generics: Option<GenericsList>,
    pub arbitrary_length: bool, // Is also homogenous
}

impl TupleContent {
    fn new_empty() -> Self {
        Self {
            generics: None,
            arbitrary_length: true,
        }
    }

    pub fn format(&self, format_data: &FormatData) -> Box<str> {
        let base = match format_data.style {
            FormatStyle::Short => "tuple",
            FormatStyle::Qualified | FormatStyle::MypyRevealType => "builtins.tuple",
        };
        if let Some(generics) = self.generics.as_ref() {
            let list = generics.format(format_data);
            if self.arbitrary_length {
                format!("{base}[{list}, ...]").into()
            } else {
                format!("{base}[{list}]").into()
            }
        } else {
            format!("{base}[Any, ...]").into()
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct CallableParam {
    pub param_kind: ParamKind,
    pub name: Option<StringSlice>,
    pub has_default: bool,
    pub db_type: DbType,
}

impl CallableParam {
    pub fn format(&self, format_data: &FormatData) -> Box<str> {
        if self.param_kind != ParamKind::PositionalOnly || format_data.verbose && self.has_default {
            let t = self.db_type.format(format_data);
            if self.param_kind == ParamKind::Starred {
                return format!("VarArg({t})").into();
            } else if self.param_kind == ParamKind::DoubleStarred {
                return format!("KwArg({t})").into();
            } else if let Some(name) = self.name {
                match format_data.style {
                    FormatStyle::MypyRevealType => {
                        let mut string = match self.param_kind {
                            ParamKind::PositionalOnly
                            | ParamKind::PositionalOrKeyword
                            | ParamKind::KeywordOnly => {
                                format!("{}: ", name.as_str(format_data.db))
                            }
                            ParamKind::Starred => format!("*{}: ", name.as_str(format_data.db)),
                            ParamKind::DoubleStarred => {
                                format!("*{}: ", name.as_str(format_data.db))
                            }
                        };
                        string += &t;
                        if self.has_default {
                            string += " =";
                        }
                        return string.into();
                    }
                    _ => {
                        return match self.param_kind {
                            ParamKind::PositionalOnly | ParamKind::PositionalOrKeyword => {
                                if !format_data.verbose {
                                    return t;
                                }
                                if self.has_default {
                                    format!("DefaultArg({t}, '{}')", name.as_str(format_data.db))
                                } else {
                                    format!("Arg({t}, '{}')", name.as_str(format_data.db))
                                }
                            }
                            ParamKind::KeywordOnly => {
                                if self.has_default {
                                    todo!()
                                } else {
                                    format!("NamedArg({t}, '{}')", name.as_str(format_data.db))
                                }
                            }
                            ParamKind::Starred | ParamKind::DoubleStarred => unreachable!(),
                        }
                        .into();
                    }
                }
            } else if self.has_default {
                return format!("DefaultArg({t})").into();
            }
        }
        self.db_type.format(format_data)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct CallableContent {
    pub defined_at: PointLink,
    pub type_vars: Option<TypeVarLikes>,
    pub params: CallableParams,
    pub result_type: DbType,
}

impl CallableContent {
    pub fn format(&self, format_data: &FormatData) -> String {
        let mut params = self.params.as_ref().map(|params| {
            params
                .iter()
                .map(|p| p.format(format_data))
                .collect::<Vec<_>>()
        });
        let result = self.result_type.format(format_data);
        match format_data.style {
            FormatStyle::MypyRevealType => {
                if let Some(params) = params.as_mut() {
                    for (i, p) in self.params.as_ref().unwrap().iter().enumerate() {
                        match p.param_kind {
                            ParamKind::KeywordOnly => {
                                params.insert(i, Box::from("*"));
                                break;
                            }
                            ParamKind::Starred => break,
                            _ => (),
                        }
                    }
                }
                let param_string = params.map(|p| p.join(", "));
                let param_str = param_string.as_deref().unwrap_or("*Any, **Any");
                let type_vars = self.type_vars.as_ref().map(|t| {
                    format!(
                        " [{}]",
                        t.iter()
                            .map(|t| match t.as_ref() {
                                TypeVarLike::TypeVar(t) => {
                                    let mut name = t.name(format_data.db).to_owned();
                                    if let Some(bound) = &t.bound {
                                        name += " <: ";
                                        name += &bound.format(format_data);
                                    }
                                    name
                                }
                                TypeVarLike::TypeVarTuple(_) => todo!(),
                                TypeVarLike::ParamSpec(_) => todo!(),
                            })
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                });
                let type_vars = type_vars.as_deref().unwrap_or("");
                if result.as_ref() == "None" {
                    format!("def{type_vars} ({param_str})")
                } else {
                    format!("def{type_vars} ({param_str}) -> {result}")
                }
            }
            _ => {
                let param_string = params.map(|p| format!("[{}]", p.join(", ")));
                let param_str = param_string.as_deref().unwrap_or("...");
                format!("Callable[{param_str}, {result}]")
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct RecursiveAlias {
    pub link: PointLink,
    pub generics: Option<GenericsList>,
    calculated_db_type: OnceCell<DbType>,
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

    pub fn calculated_db_type<'db: 'slf, 'slf>(&'slf self, db: &'db Database) -> &'slf DbType {
        let alias = self.type_alias(db);
        if self.generics.is_none() {
            alias.db_type.as_ref()
        } else {
            self.calculated_db_type.get_or_init(|| {
                self.type_alias(db)
                    .replace_type_vars(true, &mut |t| {
                        self.generics
                            .as_ref()
                            .map(|g| g.nth(t.index).unwrap().clone())
                            .unwrap()
                    })
                    .into_owned()
            })
        }
    }
}

impl std::cmp::PartialEq for RecursiveAlias {
    fn eq(&self, other: &Self) -> bool {
        self.link == other.link && self.generics == other.generics
    }
}

#[derive(Debug)]
struct UnresolvedTypeVarLike {
    type_var: Rc<TypeVarLike>,
    most_outer_callable: Option<PointLink>,
}

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

#[derive(Default)]
pub struct TypeVarManager {
    type_vars: Vec<UnresolvedTypeVarLike>,
    callables: Vec<CallableWithParent>,
}

impl TypeVarManager {
    pub fn position(&self, type_var: &TypeVarLike) -> Option<usize> {
        self.type_vars
            .iter()
            .position(|t| t.type_var.as_ref() == type_var)
    }

    pub fn add(
        &mut self,
        type_var: Rc<TypeVarLike>,
        in_callable: Option<PointLink>,
    ) -> TypeVarIndex {
        if let Some(index) = self.position(type_var.as_ref()) {
            self.type_vars[index].most_outer_callable = self.calculate_most_outer_callable(
                self.type_vars[index].most_outer_callable,
                in_callable,
            );
            index.into()
        } else {
            self.type_vars.push(UnresolvedTypeVarLike {
                type_var,
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

    pub fn lookup_for_remap(&self, tv: &TypeVarUsage) -> TypeVarUsage {
        TypeVarUsage {
            type_var_like: tv.type_var_like.clone(),
            index: self.position(&tv.type_var_like).unwrap().into(),
            in_definition: tv.in_definition,
        }
    }

    pub fn has_late_bound_type_vars(&self) -> bool {
        self.type_vars
            .iter()
            .any(|t| t.most_outer_callable.is_some())
    }

    pub fn has_type_vars(&self) -> bool {
        !self.type_vars.is_empty()
    }

    pub fn into_type_vars(self) -> TypeVarLikes {
        TypeVarLikes(
            self.type_vars
                .into_iter()
                .filter_map(|t| t.most_outer_callable.is_none().then(|| t.type_var))
                .collect(),
        )
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

    fn remap_type_var(&self, usage: &TypeVarUsage) -> TypeVarUsage {
        let mut index = 0;
        let mut in_definition = None;
        for t in self.type_vars.iter().rev() {
            if t.type_var == usage.type_var_like {
                if t.most_outer_callable.is_some() {
                    in_definition = t.most_outer_callable;
                } else {
                    return usage.clone();
                }
            } else if in_definition == t.most_outer_callable {
                index += 1;
            }
        }
        if let Some(in_definition) = in_definition {
            TypeVarUsage {
                type_var_like: usage.type_var_like.clone(),
                in_definition,
                index: index.into(),
            }
        } else {
            usage.clone()
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
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
pub struct TypeVarLikes(Box<[Rc<TypeVarLike>]>);

impl TypeVarLikes {
    pub fn from_vec(vec: Vec<Rc<TypeVarLike>>) -> Self {
        Self(vec.into_boxed_slice())
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn find(
        &self,
        type_var_like: Rc<TypeVarLike>,
        in_definition: PointLink,
    ) -> Option<TypeVarUsage> {
        self.0
            .iter()
            .position(|t| t == &type_var_like)
            .map(|index| TypeVarUsage {
                type_var_like,
                index: index.into(),
                in_definition,
            })
    }

    pub fn iter(&self) -> impl Iterator<Item = &Rc<TypeVarLike>> {
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
    TypeVar(TypeVar),
    TypeVarTuple(TypeVarTuple),
    ParamSpec(ParamSpec),
}

impl TypeVarLike {
    pub fn name<'db>(&self, db: &'db Database) -> &'db str {
        match self {
            Self::TypeVar(t) => t.name(db),
            Self::TypeVarTuple(t) => todo!(), //t.name(db),
            Self::ParamSpec(s) => todo!(),    // s.name(db),
        }
    }
}

#[derive(Debug, Clone)]
pub struct TypeVar {
    pub name_string: PointLink,
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
        NodeRef::from_link(db, self.name_string)
            .maybe_str()
            .unwrap()
            .content()
    }

    pub fn qualified_name(&self, db: &Database) -> Box<str> {
        let node_ref = NodeRef::from_link(db, self.name_string);
        format!(
            "{}.{}",
            node_ref.in_module(db).qualified_name(db),
            node_ref.maybe_str().unwrap().content()
        )
        .into()
    }
}

#[derive(Debug, Clone)]
pub struct TypeVarTuple {
    pub name_string: PointLink,
    pub default: Option<DbType>,
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

impl PartialEq for ParamSpec {
    fn eq(&self, other: &Self) -> bool {
        self.name_string == other.name_string
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct TypeVarUsage {
    pub type_var_like: Rc<TypeVarLike>,
    pub index: TypeVarIndex,
    pub in_definition: PointLink,
}

#[derive(Debug, PartialEq, Clone)]
pub struct TypeAlias {
    pub type_vars: TypeVarLikes,
    pub location: PointLink,
    pub name: Option<PointLink>,
    // This is intentionally private, it should not be used anywhere else, because the behavior of
    // a type alias that has `is_recursive` is different.
    // TODO make this private again
    pub db_type: Rc<DbType>,
    pub is_recursive: bool,
}

impl TypeAlias {
    pub fn new(
        type_vars: TypeVarLikes,
        location: PointLink,
        name: Option<PointLink>,
        db_type: Rc<DbType>,
        is_recursive: bool,
    ) -> Self {
        Self {
            type_vars,
            location,
            name,
            db_type,
            is_recursive,
        }
    }
    pub fn as_db_type_and_set_type_vars_any(&self) -> DbType {
        if self.is_recursive {
            return DbType::RecursiveAlias(Rc::new(RecursiveAlias::new(
                self.location,
                (!self.type_vars.is_empty()).then(|| {
                    GenericsList::new_generics(
                        std::iter::repeat(DbType::Any)
                            .take(self.type_vars.len())
                            .collect(),
                    )
                }),
            )));
        }
        if self.type_vars.is_empty() {
            self.db_type.as_ref().clone()
        } else {
            self.db_type
                .replace_type_vars(&mut |t| match t.in_definition == self.location {
                    true => DbType::Any,
                    false => DbType::TypeVarLike(t.clone()),
                })
        }
    }

    pub fn replace_type_vars(
        &self,
        remove_recursive_wrapper: bool,
        callable: &mut impl FnMut(&TypeVarUsage) -> DbType,
    ) -> Cow<DbType> {
        if self.is_recursive && !remove_recursive_wrapper {
            return Cow::Owned(DbType::RecursiveAlias(Rc::new(RecursiveAlias::new(
                self.location,
                (!self.type_vars.is_empty()).then(|| {
                    GenericsList::new_generics(
                        self.type_vars
                            .iter()
                            .enumerate()
                            .map(|(i, type_var)| {
                                callable(&TypeVarUsage {
                                    type_var_like: type_var.clone(),
                                    index: i.into(),
                                    in_definition: self.location,
                                })
                            })
                            .collect(),
                    )
                }),
            ))));
        }
        if self.type_vars.is_empty() {
            Cow::Borrowed(self.db_type.as_ref())
        } else {
            Cow::Owned(self.db_type.replace_type_vars(callable))
        }
    }

    pub fn name<'db>(&self, db: &'db Database) -> Option<&'db str> {
        self.name.map(|name| NodeRef::from_link(db, name).as_code())
    }

    pub fn is_class(&self) -> bool {
        matches!(self.db_type.as_ref(), DbType::Class(_, _))
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
    pub fn new(file_state_loaders: FileStateLoaders, workspaces: Workspaces) -> Self {
        let mut this = Self {
            in_use: false,
            vfs: Box::<FileSystemReader>::new(Default::default()),
            file_state_loaders,
            files: Default::default(),
            path_to_file: Default::default(),
            workspaces,
            in_memory_files: Default::default(),
            python_state: PythonState::reserve(),
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
        f.ensure_initialized();
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
        let index =
            self.add_file_state(Box::pin(LanguageFileState::new_parsed("".to_owned(), file)));
        self.loaded_python_file(index)
    }

    pub fn load_file_from_workspace(
        &self,
        dir: Rc<DirContent>,
        path: String,
        index: &WorkspaceFileIndex,
    ) {
        // A loader should be available for all files in the workspace.
        let loader = self.loader(&path).unwrap();
        let file_index = self.add_file_state(if let Some(code) = self.vfs.read_file(&path) {
            loader.load_parsed(dir, path, code)
        } else {
            //loader.inexistent_file_state(path)
            todo!()
        });
        index.set(file_index);
    }

    pub fn load_in_memory_file(&mut self, path: String, code: String) -> FileIndex {
        // First unload the old file, if there is already one
        let in_mem_file = self.in_memory_file(&path);
        if let Some(file_index) = in_mem_file {
            self.unload_file(file_index);
        }

        // Then load the new one
        // TODO there could be no loader...
        let ensured = self.workspaces.ensure_file(&*self.vfs, &path);
        let loader = self.loader(&path).unwrap();
        let file_state = loader.load_parsed(ensured.directory.clone(), path.clone(), code);
        let file_index = if let Some(file_index) = in_mem_file {
            self.update_file_state(file_index, file_state);
            file_index
        } else {
            let file_index = self.add_file_state(file_state);
            self.in_memory_files.insert(path.clone().into(), file_index);
            file_index
        };
        ensured.set_file_index(file_index);
        self.invalidate_file(file_index, ensured.invalidations);
        file_index
    }

    pub fn in_memory_file(&mut self, path: &str) -> Option<FileIndex> {
        self.in_memory_files.get(path).cloned()
    }

    fn unload_file(&mut self, file_index: FileIndex) {
        let file_state = &mut self.files[file_index.0 as usize];
        self.workspaces
            .unload_if_not_available(&*self.vfs, file_state.path());
        let invalidations = file_state.unload_and_return_invalidations();
        self.invalidate_file(file_index, invalidations)
    }

    fn invalidate_file(&mut self, original_file_index: FileIndex, invalidations: Invalidations) {
        for invalid_index in invalidations.into_iter() {
            let file_state = self.file_state_mut(invalid_index);
            let invalidations = file_state.take_invalidations();
            if let Some(file) = file_state.maybe_loaded_file_mut() {
                file.invalidate_references_to(original_file_index);
            }

            self.invalidate_file(original_file_index, invalidations);
        }
    }

    pub fn add_invalidates(&self, file: FileIndex, invalidates: FileIndex) {
        self.file_state(file).add_invalidates(invalidates)
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
        let file_index = self.add_file_state(loader.load_parsed(dir.clone(), p.to_owned(), code));
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
        let types = self.py_load_tmp(&dir, "../typeshed/stdlib/types.pyi") as *const _;
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
            &collections_dir,
            "../typeshed/stdlib/collections/__init__.pyi",
        ) as *const _;

        PythonState::initialize(
            self,
            builtins,
            typing,
            collections,
            types,
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
}

#[derive(Debug, Clone, PartialEq)]
pub struct ClassInfos {
    pub mro: Box<[DbType]>, // Does never include `object`
    pub is_protocol: bool,
    pub incomplete_mro: bool,
}

impl std::clone::Clone for ClassStorage {
    fn clone(&self) -> Self {
        unreachable!("This should never happen, because should never be cloned");
    }
}

impl<'db> std::cmp::PartialEq for ClassStorage {
    fn eq(&self, other: &Self) -> bool {
        unreachable!("Should never happen with classes")
    }
}

#[derive(PartialEq, Eq, Copy, Clone)]
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
        assert_eq!(size_of::<ClassStorage>(), 104);
        assert_eq!(size_of::<ClassInfos>(), 24);
        assert_eq!(size_of::<PointLink>(), 8);
        assert_eq!(size_of::<AnyLink>(), 16);
        assert_eq!(size_of::<Execution>(), 24);
        assert_eq!(size_of::<ComplexPoint>(), 32);
        assert_eq!(size_of::<DbType>(), 32);
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
