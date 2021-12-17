use once_cell::unsync::OnceCell;
use parsa_python_ast::{Name, NodeIndex};
use std::cell::Cell;
use std::collections::HashMap;
use std::fmt;
use std::iter::repeat;
use std::mem;
use std::path::{Path, PathBuf};
use std::pin::Pin;
use walkdir::WalkDir;

use crate::file::PythonFile;
use crate::file_state::{
    File, FileState, FileStateLoader, FileSystemReader, VirtualFileSystemReader,
};
use crate::inferred::NodeReference;
use crate::python_state::PythonState;
use crate::utils::{InsertOnlyVec, SymbolTable};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FileIndex(pub u32);
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TypeVarIndex(u32);

impl TypeVarIndex {
    pub fn new(i: usize) -> Self {
        Self(i as u32)
    }

    pub fn is_zero(&self) -> bool {
        self.0 == 0
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
const TYPE_VAR_BIT_INDEX: usize = 8;

const REST_MASK: u32 = 0b11_1111_1111_1111_1111_1111;
const SPECIFIC_MASK: u32 = 0xFF; // 8 bits
const MAX_TYPE_VAR: u32 = 0xFF; // 256
const TYPE_VAR_MASK: u32 = MAX_TYPE_VAR << TYPE_VAR_BIT_INDEX; // 8 bits
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

    pub fn new_missing_file() -> Self {
        // Imports that point nowhere
        todo!()
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

    pub fn new_numbered_type_var(
        specific: Specific,
        index: TypeVarIndex,
        locality: Locality,
    ) -> Self {
        assert!(index.0 <= MAX_TYPE_VAR);
        debug_assert!(matches!(
            specific,
            Specific::ClassTypeVar | Specific::FunctionTypeVar
        ));
        let flags = Self::calculate_flags(
            PointType::Specific,
            specific as u32 | index.0 << TYPE_VAR_BIT_INDEX,
            locality,
        );
        Self {
            flags,
            node_index: 0,
        }
    }

    pub fn type_(self) -> PointType {
        unsafe { mem::transmute((self.flags & TYPE_MASK) >> TYPE_BIT_INDEX) }
    }

    pub fn locality(self) -> Locality {
        unsafe { mem::transmute((self.flags & LOCALITY_MASK) >> LOCALITY_BIT_INDEX) }
    }

    pub fn calculated(self) -> bool {
        (self.flags & IS_ANALIZED_MASK) != 0
    }

    pub fn calculating(self) -> bool {
        self.flags == 1
    }

    fn is_recursion_error(self) -> bool {
        unimplemented!();
        //self.flags & REST_MASK & 1 == 1
    }

    pub fn file_index(self) -> FileIndex {
        debug_assert!(
            self.type_() == PointType::Redirect || self.type_() == PointType::FileReference
        );
        FileIndex(self.flags & REST_MASK)
    }

    pub fn complex_index(self) -> usize {
        debug_assert!(
            self.type_() == PointType::Complex,
            "Expected complex, got {:?}",
            self
        );
        (self.flags & REST_MASK) as usize
    }

    pub fn maybe_complex_index(self) -> Option<usize> {
        if self.type_() == PointType::Complex {
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

    pub fn type_var_index(self) -> TypeVarIndex {
        debug_assert!(self.type_() == PointType::Specific);
        TypeVarIndex(unsafe { mem::transmute((self.flags & TYPE_VAR_MASK) >> TYPE_VAR_BIT_INDEX) })
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

    pub fn set_on_name(&self, name: &Name, point: Point) {
        debug_assert!(point.type_() != PointType::MultiDefinition);
        let mut index = name.index();
        let current = self.get(index);
        if current.calculated() && current.type_() == PointType::MultiDefinition {
            index -= 1 // Set it on NameDefinition
        }
        self.set(index, point);
    }
}

#[derive(Debug, PartialEq, Eq)]
#[repr(u32)]
pub enum PointType {
    Redirect,
    MultiDefinition,
    Complex,
    // In case of a reference it's missing otherwise unknown.
    Unknown,
    Specific,
    FileReference,
    // Basically stuff like if/for nodes
    NodeAnalysis,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[repr(u32)]
pub enum Specific {
    String,
    Bytes,
    Float,
    Integer,
    Complex,
    Boolean,
    None,

    Ellipsis,
    Tuple,
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
    AnnotationInstance,
    SimpleGeneric,      // primary: primary '[' slices ']'
    TypingWithGenerics, // Same as SimpleGeneric, but with a Typing*Class instead

    TypingProtocol,
    TypingGeneric,
    TypingTuple,
    TypingCallable,
    TypingType,

    // TODO reactivate these or remove
    //TypingClassVar,
    //TypingFinal,
    //TypingLiteral,
    //TypingTypeAlias,
    //TypingConcatenate,
    //TypingAnnotated,
    //TypingUnion,
    //TypingOptional,

    //TypingAliasClass,
    //TypingAliasInstance,
    //TypingAny,
    //TypedDict,
    ClassTypeVar,
    FunctionTypeVar,
}

#[derive(Debug)]
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
    Specific(Specific),
}

#[derive(Debug, Clone, PartialEq)]
pub enum ComplexPoint {
    Class(Box<ClassStorage>),
    Union(Box<[PointLink]>),
    ExecutionInstance(PointLink, Box<Execution>),
    BoundMethod(AnyLink, PointLink),
    Closure(PointLink, Box<Execution>),
    GenericClass(PointLink, GenericsList),
    Instance(PointLink, Option<GenericsList>),
    ClassInfos(Box<ClassInfos>),
    FunctionTypeVars(Box<[PointLink]>),
    FunctionOverload(Box<Overload>),
    TupleClass(TupleContent),
    Tuple(TupleContent),
    Callable(CallableContent),
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
pub struct ClassInfos {
    pub type_vars: Box<[PointLink]>,
    pub mro: Box<[MroClass]>, // Does never include `object`
    pub is_protocol: bool,
}

impl ClassInfos {
    pub fn find_type_var_index(&self, link: PointLink) -> Option<TypeVarIndex> {
        self.type_vars
            .iter()
            .position(|&r| r == link)
            .map(|i| TypeVarIndex(i as u32))
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct GenericsList(Box<[GenericPart]>);

impl GenericsList {
    pub fn new(parts: Box<[GenericPart]>) -> Self {
        debug_assert!(parts.len() > 0);
        Self(parts)
    }

    pub fn new_unknown(length: usize) -> Self {
        debug_assert!(length > 0);
        let vec: Vec<_> = repeat(GenericPart::Unknown).take(length).collect();
        Self(vec.into_boxed_slice())
    }

    pub fn set_generic(&mut self, index: TypeVarIndex, generic: GenericPart) {
        self.0[index.0 as usize].union_in_place(generic);
    }

    pub fn nth(&self, index: TypeVarIndex) -> Option<&GenericPart> {
        self.0.get(index.0 as usize)
    }

    pub fn iter(&self) -> std::slice::Iter<GenericPart> {
        self.0.iter()
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum GenericPart {
    Class(PointLink),
    GenericClass(PointLink, GenericsList),
    Union(Box<[GenericPart]>),
    TypeVar(PointLink),
    Type(Box<GenericPart>),
    Tuple(TupleContent),
    Callable(CallableContent),
    Unknown,
}

impl GenericPart {
    pub fn union(self, other: GenericPart) -> Self {
        match self {
            Self::Union(list) => {
                let mut vec = list.into_vec();
                match other {
                    Self::Union(other_list) => {
                        for o in other_list.into_vec().into_iter() {
                            if !vec.contains(&o) {
                                vec.push(o);
                            }
                        }
                    }
                    Self::Unknown => (),
                    _ => {
                        if !vec.contains(&other) {
                            vec.push(other)
                        }
                    }
                };
                Self::Union(vec.into_boxed_slice())
            }
            Self::Unknown => other,
            _ => match other {
                Self::Union(list) => {
                    if list.contains(&self) {
                        Self::Union(list)
                    } else {
                        let mut vec = list.into_vec();
                        vec.push(self);
                        Self::Union(vec.into_boxed_slice())
                    }
                }
                Self::Unknown => self,
                _ => {
                    if self == other {
                        self
                    } else {
                        Self::Union(Box::new([self, other]))
                    }
                }
            },
        }
    }

    fn union_in_place(&mut self, other: GenericPart) {
        *self = mem::replace(self, Self::Unknown).union(other);
    }

    pub fn as_type_string(&self, db: &Database) -> String {
        let class_name = |link| {
            NodeReference::from_link(db, link)
                .maybe_class()
                .unwrap()
                .name()
                .as_str()
        };
        match self {
            Self::Class(link) => class_name(*link).to_owned(),
            Self::GenericClass(link, generics) => {
                format!(
                    "{}[{}]",
                    class_name(*link),
                    Self::generics_as_string(db, &generics.0)
                )
            }
            Self::Union(list) => {
                format!("Union[{}]", Self::generics_as_string(db, list))
            }
            Self::TypeVar(link) => NodeReference::from_link(db, *link)
                .as_name()
                .as_str()
                .to_owned(),
            Self::Type(generic_part) => format!("Type[{}]", generic_part.as_type_string(db)),
            Self::Tuple(content) => format!(
                "Tuple[{}]",
                content
                    .generics
                    .as_ref()
                    .map(|list| Self::generics_as_string(db, &list.0))
                    .unwrap_or_else(|| "Tuple".to_owned())
            ),
            Self::Callable(content) => todo!(),
            Self::Unknown => "Unknown".to_owned(),
        }
    }

    fn generics_as_string(db: &Database, list: &[GenericPart]) -> String {
        list.iter()
            .map(|g| g.as_type_string(db))
            .fold(String::new(), |a, b| a + &b + ",")
    }

    pub fn replace_type_vars<C: FnMut(PointLink) -> Self>(self, callable: &mut C) -> Self {
        let replace_list = |list: &mut Box<[GenericPart]>, callable: &mut C| {
            for item in list.iter_mut() {
                let g = std::mem::replace(&mut *item, GenericPart::Unknown);
                *item = g.replace_type_vars(callable);
            }
        };
        match self {
            Self::Class(_) | Self::Unknown => self,
            Self::GenericClass(link, generics) => Self::GenericClass(link, generics),
            Self::Union(list) => {
                todo!()
            }
            Self::TypeVar(link) => callable(link),
            Self::Type(mut generic_part) => {
                let g = std::mem::replace(&mut *generic_part, GenericPart::Unknown);
                *generic_part = g.replace_type_vars(callable);
                Self::Type(generic_part)
            }
            Self::Tuple(mut content) => {
                if let Some(generics) = content.generics.as_mut() {
                    replace_list(&mut generics.0, callable)
                }
                Self::Tuple(content)
            }
            Self::Callable(content) => todo!(),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct MroClass {
    pub class: PointLink,
    pub type_var_remap: Box<[Option<TypeVarRemap>]>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeVarRemap {
    TypeVar(TypeVarIndex),
    MroClass(MroClass),
}

impl MroClass {
    pub fn remap_with_sub_class(&self, sub_class: &MroClass) -> Self {
        Self {
            class: self.class,
            type_var_remap: self
                .type_var_remap
                .iter()
                .map(|t| {
                    t.as_ref().and_then(|t| match &t {
                        TypeVarRemap::TypeVar(i) => sub_class.type_var_remap[i.0 as usize].clone(),
                        TypeVarRemap::MroClass(c) => {
                            Some(TypeVarRemap::MroClass(c.remap_with_sub_class(sub_class)))
                        }
                    })
                })
                .collect(),
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
        debug_assert!(self.implementing_function.is_none());
        let mut functions = Vec::with_capacity(self.functions.len() + 1);
        functions.extend_from_slice(self.functions.as_ref());
        functions.push(function);
        Self {
            implementing_function: None,
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

#[derive(Debug, Clone, PartialEq)]
pub struct CallableContent {}

pub struct Database {
    in_use: bool,
    pub file_system_reader: Box<dyn VirtualFileSystemReader>,
    file_state_loaders: FileStateLoaders,
    files: InsertOnlyVec<dyn FileState>,
    path_to_file: HashMap<&'static str, FileIndex>,
    pub workspaces: Vec<Workspace>,
    files_managed_by_client: HashMap<PathBuf, FileIndex>,

    pub python_state: PythonState,
}

impl Database {
    pub fn new(file_state_loaders: FileStateLoaders, workspaces: Vec<Workspace>) -> Self {
        let mut this = Self {
            in_use: false,
            file_system_reader: Box::<FileSystemReader>::new(Default::default()),
            file_state_loaders,
            files: Default::default(),
            path_to_file: Default::default(),
            workspaces,
            files_managed_by_client: Default::default(),
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

    pub fn file_path(&self, index: FileIndex) -> &str {
        self.file_state(index).path()
    }

    pub fn file_state_index_by_path(&self, path: &str) -> Option<FileIndex> {
        self.path_to_file.get(path).copied()
    }

    pub fn loaded_file(&self, index: FileIndex) -> &(dyn File + 'static) {
        self.file_state(index).file(self).unwrap()
    }

    fn loader(&self, path: &str) -> Option<&dyn FileStateLoader> {
        for loader in self.file_state_loaders.iter() {
            let extension = Path::new(path).extension().and_then(|e| e.to_str());
            if let Some(e) = extension {
                if loader.responsible_for_file_endings().contains(&e) {
                    return Some(loader.as_ref());
                }
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

    pub fn load_file(&self, path: String, code: String) -> FileIndex {
        // This is the explicit version where we know that there's a loader.
        let loader = self.loader(&path).unwrap();
        self.add_file_state(loader.load_parsed(path, code))
    }

    pub fn load_file_from_workspace(&self, path: String, index: &WorkspaceFileIndex) {
        // A loader should be available for all files in the workspace.
        let loader = self.loader(&path).unwrap();
        let file_index = self.add_file_state(
            if let Some(code) = self.file_system_reader.read_file(&path) {
                loader.load_parsed(path, code)
            } else {
                loader.inexistent_file_state(path)
            },
        );
        index.set(file_index);
    }

    pub fn load_unparsed(&self, path: String) -> Option<FileIndex> {
        self.loader(&path)
            .map(|loader| self.add_file_state(loader.load_unparsed(path)))
    }

    fn py_load_tmp(&self, p: &'static str) -> &PythonFile {
        let file_index = self.load_unparsed(p.to_owned()).unwrap();
        self.loaded_python_file(file_index)
    }

    pub fn loaded_python_file(&self, index: FileIndex) -> &PythonFile {
        self.loaded_file(index).as_any().downcast_ref().unwrap()
    }

    fn initial_python_load(&mut self) {
        let builtins = self.py_load_tmp("../typeshed/stdlib/3/builtins.pyi") as *const _;
        let typing = self.py_load_tmp("../typeshed/stdlib/3/typing.pyi") as *const _;
        PythonState::initialize(self, builtins, typing);
    }
}

#[derive(Debug)]
pub struct Workspace {
    root: DirectoryOrFile,
    //watcher: dyn notify::Watcher,
}

impl Workspace {
    pub fn new(loaders: &[Box<dyn FileStateLoader>], root: String) -> Self {
        let mut stack = vec![(
            PathBuf::from(&root),
            DirectoryOrFile::Directory(root, vec![]),
        )];
        // TODO optimize if there are a lot of files
        for entry in WalkDir::new(&stack[0].1.name())
            .follow_links(true)
            .into_iter()
            .filter_entry(|entry| {
                entry
                    .file_name()
                    .to_str()
                    .map(|name| {
                        !loaders.iter().any(|l| l.should_be_ignored(name))
                            && loaders.iter().any(|l| l.might_be_relevant(name))
                    })
                    .unwrap_or(false)
            })
            .filter_map(|e| e.ok())
            .skip(1)
        {
            while !entry.path().starts_with(&stack.last().unwrap().0) {
                let n = stack.pop().unwrap().1;
                stack
                    .last_mut()
                    .unwrap()
                    .1
                    .directory_entries_mut()
                    .unwrap()
                    .push(n);
            }
            let name = entry.file_name();
            if let Some(name) = name.to_str() {
                match entry.metadata() {
                    Ok(m) => {
                        if m.is_dir() {
                            stack.push((
                                entry.path().to_owned(),
                                DirectoryOrFile::Directory(name.to_owned(), vec![]),
                            ));
                        } else {
                            stack
                                .last_mut()
                                .unwrap()
                                .1
                                .directory_entries_mut()
                                .unwrap()
                                .push(DirectoryOrFile::File(
                                    name.to_owned(),
                                    WorkspaceFileIndex::none(),
                                ));
                        }
                    }
                    Err(e) => {
                        // Just ignore it for now
                        panic!("Need to investigate")
                    }
                }
            }
        }
        while let Some(current) = stack.pop() {
            if let Some(parent) = stack.last_mut() {
                parent.1.directory_entries_mut().unwrap().push(current.1)
            } else {
                return Self { root: current.1 };
            }
        }
        unreachable!()
    }

    pub fn root(&self) -> &DirectoryOrFile {
        &self.root
    }
}

#[derive(Debug, Clone)]
pub struct WorkspaceFileIndex(Cell<Option<FileIndex>>);

impl WorkspaceFileIndex {
    fn none() -> Self {
        Self(Cell::new(None))
    }

    fn set(&self, index: FileIndex) {
        self.0.set(Some(index));
    }

    pub fn get(&self) -> Option<FileIndex> {
        self.0.get()
    }
}

#[derive(Debug)]
pub enum DirectoryOrFile {
    File(String, WorkspaceFileIndex),
    Directory(String, Vec<DirectoryOrFile>),
}

impl DirectoryOrFile {
    pub fn name(&self) -> &str {
        match self {
            Self::Directory(name, _) => name,
            Self::File(name, _) => name,
        }
    }

    pub fn directory_entries(&self) -> Option<&[DirectoryOrFile]> {
        match self {
            DirectoryOrFile::Directory(_, entries) => Some(entries),
            _ => None,
        }
    }

    pub fn directory_entries_mut(&mut self) -> Option<&mut Vec<DirectoryOrFile>> {
        match self {
            DirectoryOrFile::Directory(_, entries) => Some(entries),
            _ => None,
        }
    }
}

#[derive(Debug)]
pub struct ClassStorage {
    pub symbol_table: SymbolTable,
}

impl ClassStorage {
    pub fn new(symbol_table: SymbolTable) -> Self {
        Self { symbol_table }
    }
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

#[cfg(test)]
mod tests {
    #[test]
    fn test_sizes() {
        use super::*;
        use std::mem::size_of;
        assert_eq!(size_of::<ClassStorage>(), 48);
        assert_eq!(size_of::<ClassInfos>(), 40);
        assert_eq!(size_of::<PointLink>(), 8);
        assert_eq!(size_of::<AnyLink>(), 16);
        assert_eq!(size_of::<Execution>(), 24);
        assert_eq!(size_of::<ComplexPoint>(), 32);
    }
}
