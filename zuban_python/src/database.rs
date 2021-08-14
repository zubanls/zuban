use std::mem;
use std::fmt;
use std::ptr::null;
use std::path::{Path, PathBuf};
use std::collections::HashMap;
use std::pin::Pin;
use parsa::NodeIndex;

use crate::file::{PythonFile, FileState, File, FileStateLoader, VirtualFileSystemReader, FileSystemReader};
use crate::utils::InsertOnlyVec;
use crate::value::Class;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FileIndex(pub u32);

type FileStateLoaders = Box<[Box<dyn FileStateLoader>]>;

// Most significant bits
// 27 bits = 134217728; 20 bits = 1048576
// oxxxx is_analyzed
// xoxxx is_invalidated
// xxooo Locality (xXxx is_external)
// xxxxxo in_module_scope
// xxxxxxo is_nullable
// xxxxxxxooo ValueOrReferenceType
// if true rest 22 bits reserved for ValueOrReference details

const IS_ANALIZED_BIT_INDEX: usize = 31;
const IS_INVALIDATED_BIT_INDEX: usize = 30;
const LOCALITY_BIT_INDEX: usize = 27; // Uses 3 bits
const IN_MODULE_SCOPE_BIT_INDEX: usize = 26;
const IS_NULLABLE_BIT_INDEX: usize = 25;
const TYPE_BIT_INDEX: usize = 22; // Uses 3 bits

const REST_MASK: u32 = 0b11_1111_1111_1111_1111_1111;
const FILE_MASK: u32 = 0xFFFFFF; // 24 bits
const IS_ANALIZED_MASK: u32 = 1 << IS_ANALIZED_BIT_INDEX;
const IN_MODULE_SCOPE_MASK: u32 = 1 << IN_MODULE_SCOPE_BIT_INDEX;
const IS_NULLABLE_MASK: u32 = 1 << IN_MODULE_SCOPE_BIT_INDEX;
const LOCALITY_MASK: u32 = 0b111 << LOCALITY_BIT_INDEX;
const TYPE_MASK: u32 = 0b111 << TYPE_BIT_INDEX;

const IS_EXTERN_MASK: u32 = 1 << 30;

#[derive(Copy, Clone, Eq, PartialEq, Default)]
pub struct ValueOrReference {
    flags: u32,
    node_or_complex_index: u32,
}

impl ValueOrReference {
    #[inline]
    fn calculate_flags(type_: ValueOrReferenceType, rest: u32, locality: Locality,
                       is_nullable: bool, in_module_scope: bool) -> u32 {
        debug_assert!(rest & !REST_MASK == 0);
        rest
        | IS_ANALIZED_MASK
        | (locality as u32) << LOCALITY_BIT_INDEX
        | (is_nullable as u32) << IS_NULLABLE_BIT_INDEX
        | (in_module_scope as u32) << IN_MODULE_SCOPE_BIT_INDEX
        | (type_ as u32) << TYPE_BIT_INDEX
    }

    pub fn new_redirect(module: FileIndex, node_index: NodeIndex,
                        locality: Locality, is_nullable: bool, in_module_scope: bool) -> Self {
        let flags = Self::calculate_flags(
            ValueOrReferenceType::Redirect, module.0, locality, is_nullable, in_module_scope);
        Self {flags, node_or_complex_index: node_index}
    }

    pub fn new_multi_definition() -> Self {
        todo!()
    }

    pub fn new_complex_value(complex_index: u32, locality: Locality) -> Self {
        let flags = Self::calculate_flags(
            ValueOrReferenceType::Complex, complex_index, locality, false, false);
        Self {flags, node_or_complex_index: 0}
    }

    pub fn new_missing_or_unknown(module: FileIndex, locality: Locality) -> Self {
        let flags = Self::calculate_flags(
            ValueOrReferenceType::MissingOrUnknown, module.0, locality, false, false);
        Self {flags, node_or_complex_index: 0}
    }

    pub fn new_simple_language_specific(
        type_: ValueEnum, locality: Locality, is_nullable: bool,
        in_module_scope: bool
    ) -> Self {
        let flags = Self::calculate_flags(
            ValueOrReferenceType::LanguageSpecific, type_ as u32, locality, is_nullable, in_module_scope);
        Self {flags, node_or_complex_index: 0}
    }

    pub fn new_language_specific(
        type_: ValueEnum,
        node_index: NodeIndex, locality: Locality, is_nullable: bool) -> Self {
        todo!()
    }

    pub fn new_file_reference() -> Self {
        todo!()
    }

    pub fn new_missing_file() -> Self {
        // Imports that point nowhere
        todo!()
    }

    pub fn new_node_analysis(locality: Locality) -> Self {
        Self {
            flags: Self::calculate_flags(
                ValueOrReferenceType::NodeAnalysis, 0, locality, false, false),
            node_or_complex_index: 0
        }
    }

    pub fn new_uncalculated(in_module_scope: bool) -> Self {
        Self {
            flags: (in_module_scope as u32) << IN_MODULE_SCOPE_BIT_INDEX,
            node_or_complex_index: 0,
        }
    }

    pub fn get_type(self) -> ValueOrReferenceType {
        unsafe { mem::transmute((self.flags & TYPE_MASK) >> TYPE_BIT_INDEX) }
    }

    pub fn get_locality(self) -> Locality {
        unsafe { mem::transmute((self.flags & LOCALITY_MASK) >> LOCALITY_BIT_INDEX) }
    }

    pub fn in_module_scope(self) -> bool {
        (self.flags & IN_MODULE_SCOPE_MASK) != 0
    }

    pub fn is_nullable(self) -> bool {
        (self.flags & IS_NULLABLE_MASK) != 0
    }

    pub fn is_calculated(self) -> bool {
        (self.flags & IS_ANALIZED_MASK) != 0
    }

    pub fn is_calculating(self) -> bool {
        self.flags == 1
    }

    fn is_recursion_error(self) -> bool {
        unimplemented!();
        //self.flags & REST_MASK & 1 == 1
    }

    pub fn get_file_index(self) -> FileIndex {
        debug_assert!(self.get_type() == ValueOrReferenceType::Redirect);
        FileIndex(self.flags & REST_MASK)
    }

    pub fn get_complex_index(self) -> usize {
        debug_assert!(self.get_type() == ValueOrReferenceType::Complex);
        (self.flags & REST_MASK) as usize
    }

    pub fn get_node_index(self) -> NodeIndex {
        debug_assert!(self.get_type() == ValueOrReferenceType::Redirect);
        self.node_or_complex_index
    }

    pub fn get_language_specific(self) -> ValueEnum {
        debug_assert!(self.get_type() == ValueOrReferenceType::LanguageSpecific);
        unsafe { mem::transmute(self.flags & REST_MASK) }
    }
}

impl fmt::Debug for ValueOrReference {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut s = f.debug_struct("ValueOrReference");
        if self.is_calculating() {
            s.field("is_calculating", &self.is_calculating());
        } else if !self.is_calculated() {
            s.field("is_calculated", &self.is_calculated());
        } else {
            s
             .field("type", &self.get_type())
             .field("locality", &self.get_locality())
             .field("is_nullable", &self.is_nullable());
            if self.get_type() == ValueOrReferenceType::LanguageSpecific {
                s.field("specific", &self.get_language_specific());
            }
        }
        s.field("in_module_scope", &self.in_module_scope()).finish()
    }
}

#[derive(Debug, PartialEq, Eq)]
#[repr(u32)]
pub enum ValueOrReferenceType {
    Redirect,
    MultiDefinition,
    Complex,
    // In case of a reference it's missing otherwise unknown.
    MissingOrUnknown,
    LanguageSpecific,
    FileReference,
    // Basically stuff like if/for nodes
    NodeAnalysis,
}

#[derive(Debug)]
#[repr(u32)]
pub enum ValueEnum {
    String,
    Bytes,
    Float,
    Integer,
    Complex,
    Boolean,
    None,

    Ellipsis,
    ComprehensionGenerator,
    Tuple,

    SelfParam,
    Param,
    SimpleGeneric, // primary: primary '[' slices ']'
    ParamWithDefault, // TODO Redirect to default maybe?
    LazyInferredClass, // A class that will be inferred later.
    LazyInferredFunction, // A function that will be inferred later.
    Function,  // The node point so the index of the result
    NoReturnFunction,

    TypeVar,
    Any,
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
    DirectExtern,  // Contains a direct link that can be checked
    ComplexExtern,  // Means we have to recalculate the value all the links
    ImplicitExtern,  // Contains star imports for now (always recheck on invalidation of the module)
}

#[derive(Debug, Copy, Clone)]
pub struct ValueLink {
    pub file: FileIndex,
    pub node_index: NodeIndex,
}

pub struct LocalityLink {
    pub file: FileIndex,
    pub node_index: NodeIndex,
    pub locality: Locality,
}

#[derive(Debug)]
pub enum ComplexValue {
    Class(Class),
    Union(Box<[ValueLink]>),
    Instance(Execution),
    Closure(ValueLink, Execution),
    Generic(Execution),
}

#[derive(Debug)]
pub struct Execution {
    function: ValueLink,
    //args: Box<[Value]>,
}

pub struct Database {
    in_use: bool,
    pub file_system_reader: Box<dyn VirtualFileSystemReader>,
    file_state_loaders: FileStateLoaders,
    files: InsertOnlyVec<dyn FileState>,
    path_to_file: HashMap<&'static str, FileIndex>,
    workspaces: Vec<Workspace>,
    files_managed_by_client: HashMap<PathBuf, FileIndex>,

    pub python_state: PythonState,
}

impl Database {
    pub fn new(file_state_loaders: FileStateLoaders) -> Self {
        let mut this = Self {
            in_use: false,
            file_system_reader: Box::<FileSystemReader>::new(Default::default()),
            file_state_loaders,
            files: Default::default(),
            path_to_file: Default::default(),
            workspaces: Default::default(),
            files_managed_by_client: Default::default(),

            python_state: PythonState::new()
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

    pub fn get_file_state(&self, index: FileIndex) -> &(dyn FileState+'static) {
        self.files.get(index.0 as usize).unwrap()
    }

    pub fn get_file_path(&self, index: FileIndex) -> &str {
        self.get_file_state(index).get_path()
    }

    pub fn get_file_state_index_by_path(&self, path: &str) -> Option<FileIndex> {
        self.path_to_file.get(path).copied()
    }

    pub fn get_loaded_file(&self, index: FileIndex) -> &(dyn File+'static) {
        self.get_file_state(index).get_file(self).unwrap()
    }

    fn get_loader(&self, path: &str) -> Option<&dyn FileStateLoader> {
        for loader in self.file_state_loaders.iter() {
            let extension = Path::new(path).extension().and_then(|e| e.to_str());
            if let Some(e) = extension {
                if loader.responsible_for_file_endings().contains(&e) {
                    return Some(loader.as_ref())
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
        let loader = self.get_loader(&path).unwrap();
        self.add_file_state(loader.load_parsed(path, code))
    }

    pub fn load_unparsed(&self, path: String) -> Option<FileIndex> {
        self.get_loader(&path).map(|loader| {
            self.add_file_state(loader.load_unparsed(path))
        })
    }

    fn py_load_tmp(&self, p: &'static str) -> &PythonFile {
        let file_index = self.load_unparsed(p.to_owned()).unwrap();
        self.get_loaded_file(file_index).as_any().downcast_ref().unwrap()
    }

    fn initial_python_load(&mut self) {
        self.python_state.builtins = self.py_load_tmp("../typeshed/stdlib/3/builtins.pyi");
        self.python_state.typing = self.py_load_tmp("../typeshed/stdlib/3/typing.pyi");
    }
}

struct Workspace {
    root: DirectoryOrFile,
    //watcher: dyn notify::Watcher,
}

enum DirectoryOrFile {
    File(Box<str>, Option<FileIndex>),
    Directory(Box<str>, Vec<DirectoryOrFile>),
}

pub struct PythonState {
    builtins: *const PythonFile,
    typing: *const PythonFile,
}

impl PythonState {
    fn new() -> Self {
        Self {builtins: null(), typing: null()}
    }

    #[inline]
    pub fn get_builtins(&self) -> &PythonFile {
        debug_assert!(!self.builtins.is_null());
        unsafe {&*self.builtins}
    }
}
