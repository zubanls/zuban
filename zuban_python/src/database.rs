use std::mem;
use std::fmt;
use std::ptr::null;
use std::path::{Path, PathBuf};
use std::collections::HashMap;
use std::pin::Pin;
use std::cell::Cell;
use parsa::NodeIndex;
use walkdir::WalkDir;

use crate::file::{PythonFile, FileState, File, FileStateLoader, VirtualFileSystemReader, FileSystemReader};
use crate::utils::{InsertOnlyVec, SymbolTable};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FileIndex(pub u32);

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
    node_or_complex_index: u32,
}

impl Point {
    #[inline]
    fn calculate_flags(type_: PointType, rest: u32, locality: Locality) -> u32 {
        debug_assert!(rest & !REST_MASK == 0);
        rest
        | IS_ANALIZED_MASK
        | (locality as u32) << LOCALITY_BIT_INDEX
        | (type_ as u32) << TYPE_BIT_INDEX
    }

    pub fn new_redirect(file: FileIndex, node_index: NodeIndex, locality: Locality) -> Self {
        let flags = Self::calculate_flags(
            PointType::Redirect, file.0, locality);
        Self {flags, node_or_complex_index: node_index}
    }

    pub fn new_multi_definition() -> Self {
        todo!()
    }

    pub fn new_complex_value(complex_index: u32, locality: Locality) -> Self {
        let flags = Self::calculate_flags(
            PointType::Complex, complex_index, locality);
        Self {flags, node_or_complex_index: 0}
    }

    pub fn new_missing_or_unknown(file: FileIndex, locality: Locality) -> Self {
        let flags = Self::calculate_flags(
            PointType::MissingOrUnknown, file.0, locality);
        Self {flags, node_or_complex_index: 0}
    }

    pub fn new_simple_language_specific(type_: ValueEnum, locality: Locality) -> Self {
        let flags = Self::calculate_flags(
            PointType::LanguageSpecific, type_ as u32, locality);
        Self {flags, node_or_complex_index: 0}
    }

    pub fn new_language_specific(type_: ValueEnum, node_index: NodeIndex, locality: Locality) -> Self {
        todo!()
    }

    pub fn new_file_reference(file: FileIndex, locality: Locality) -> Self {
        let flags = Self::calculate_flags(
            PointType::FileReference, file.0 as u32, locality);
        Self {flags, node_or_complex_index: 0}
    }

    pub fn new_missing_file() -> Self {
        // Imports that point nowhere
        todo!()
    }

    pub fn new_node_analysis(locality: Locality) -> Self {
        Self {
            flags: Self::calculate_flags(
                PointType::NodeAnalysis, 0, locality),
            node_or_complex_index: 0
        }
    }

    pub fn new_uncalculated() -> Self {
        Self {
            flags: 0,
            node_or_complex_index: 0,
        }
    }

    pub fn get_type(self) -> PointType {
        unsafe { mem::transmute((self.flags & TYPE_MASK) >> TYPE_BIT_INDEX) }
    }

    pub fn get_locality(self) -> Locality {
        unsafe { mem::transmute((self.flags & LOCALITY_MASK) >> LOCALITY_BIT_INDEX) }
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
        debug_assert!(
            self.get_type() == PointType::Redirect
            || self.get_type() == PointType::FileReference);
        FileIndex(self.flags & REST_MASK)
    }

    pub fn get_complex_index(self) -> usize {
        debug_assert!(self.get_type() == PointType::Complex);
        (self.flags & REST_MASK) as usize
    }

    pub fn get_node_index(self) -> NodeIndex {
        debug_assert!(self.get_type() == PointType::Redirect);
        self.node_or_complex_index
    }

    pub fn get_language_specific(self) -> ValueEnum {
        debug_assert!(self.get_type() == PointType::LanguageSpecific);
        unsafe { mem::transmute(self.flags & REST_MASK) }
    }
}

impl fmt::Debug for Point {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut s = f.debug_struct("Point");
        if self.is_calculating() {
            s.field("is_calculating", &self.is_calculating());
        } else if !self.is_calculated() {
            s.field("is_calculated", &self.is_calculated());
        } else {
            s
             .field("type", &self.get_type())
             .field("locality", &self.get_locality())
             .field("node_index", &self.node_or_complex_index);
            if self.get_type() == PointType::LanguageSpecific {
                s.field("specific", &self.get_language_specific());
            }
            if self.get_type() == PointType::Redirect
                    || self.get_type() == PointType::FileReference {
                s.field("file_index", &self.get_file_index().0);
            }
        }
        s.finish()
    }
}

#[derive(Debug, PartialEq, Eq)]
#[repr(u32)]
pub enum PointType {
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

    InstanceWithArguments, // A primary node
    AnnotationInstance,

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
    Class(ClassStorage),
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

    pub fn load_file_from_workspace(&self, path: String, index: &WorkspaceFileIndex) {
        // A loader should be available for all files in the workspace.
        let loader = self.get_loader(&path).unwrap();
        let file_index = self.add_file_state(
            if let Some(code) = self.file_system_reader.read_file(&path) {
                loader.load_parsed(path, code)
            } else {
                loader.get_inexistent_file_state(path)
            }
        );
        index.set(file_index);
    }

    pub fn load_unparsed(&self, path: String) -> Option<FileIndex> {
        self.get_loader(&path).map(|loader| {
            self.add_file_state(loader.load_unparsed(path))
        })
    }

    fn py_load_tmp(&self, p: &'static str) -> &PythonFile {
        let file_index = self.load_unparsed(p.to_owned()).unwrap();
        self.get_loaded_python_file(file_index)
    }

    pub fn get_loaded_python_file(&self, index: FileIndex) -> &PythonFile {
        self.get_loaded_file(index).as_any().downcast_ref().unwrap()
    }

    fn initial_python_load(&mut self) {
        self.python_state.builtins = self.py_load_tmp("../typeshed/stdlib/3/builtins.pyi");
        self.python_state.typing = self.py_load_tmp("../typeshed/stdlib/3/typing.pyi");
    }
}

#[derive(Debug)]
pub struct Workspace {
    root: DirectoryOrFile,
    //watcher: dyn notify::Watcher,
}


impl Workspace {
    pub fn new(loaders: &[Box<dyn FileStateLoader>], root: String) -> Self {
        let mut stack = vec![(PathBuf::from(&root), DirectoryOrFile::Directory(root, vec![]))];
        for entry in WalkDir::new(&stack[0].1.get_name())
            .follow_links(true)
            .into_iter()
            .filter_map(|e| e.ok())
            .skip(1)
        {
            while !entry.path().starts_with(&stack.last().unwrap().0) {
                let n = stack.pop().unwrap().1;
                stack
                    .last_mut()
                    .unwrap()
                    .1
                    .get_directory_entries_mut()
                    .unwrap()
                    .push(n);
            }
            let name = entry.file_name();

            if let Some(name) = name.to_str() {
                match entry.metadata() {
                    Ok(m) => {
                        if m.is_dir() {
                            stack.push((entry.path().to_owned(), DirectoryOrFile::Directory(name.to_owned(), vec![])));
                        } else {
                            stack
                                .last_mut()
                                .unwrap()
                                .1
                                .get_directory_entries_mut()
                                .unwrap()
                                .push(DirectoryOrFile::File(name.to_owned(), WorkspaceFileIndex::none()));
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
                parent.1.get_directory_entries_mut().unwrap().push(current.1)
            } else {
                return Self {root: current.1}
            }
        }
        unreachable!()
    }

    pub fn get_root(&self) -> &DirectoryOrFile {
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
    pub fn get_name(&self) -> &str {
        match self {
            Self::Directory(name, _) => name,
            Self::File(name, _) => name,
        }
    }

    pub fn get_directory_entries(&self) -> Option<&[DirectoryOrFile]> {
        match self {
            DirectoryOrFile::Directory(_, entries) => Some(entries),
            _ => None,
        }
    }

    pub fn get_directory_entries_mut(&mut self) -> Option<&mut Vec<DirectoryOrFile>> {
        match self {
            DirectoryOrFile::Directory(_, entries) => Some(entries),
            _ => None,
        }
    }
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

#[derive(Debug)]
pub struct ClassStorage {
    pub symbol_table: SymbolTable,
}

impl ClassStorage {
    pub fn new(symbol_table: SymbolTable) -> Self {
        Self {symbol_table}
    }
}
