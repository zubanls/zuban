use std::mem;
use std::path::{Path, PathBuf};
use std::collections::HashMap;
use std::pin::Pin;
use parsa::NodeIndex;

use crate::file::{FileState, FileStateLoader, VirtualFileSystemReader, FileSystemReader};
use crate::utils::InsertOnlyVec;

#[derive(Debug, Clone, Copy)]
pub struct FileIndex(pub u32);

type ComplexIndex = u32;
type FileStateLoaders = Box<[Box<dyn FileStateLoader>]>;

// Most significant bits
// 27 bits = 134217728; 20 bits = 1048576
// oxxxx is_analyzed
// xoxxx is_invalidated
// xxooo Locality (xXxx is_external)
// xxxxxo in_module_scope
// xxxxxxo is_nullable
// xxxxxxxooo InternalValueOrReferenceType
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

const IS_EXTERN_MASK: u32 = 1 << 30;

#[derive(Copy, Clone, Debug, Eq, PartialEq, Default)]
pub struct InternalValueOrReference {
    flags: u32,
    node_or_complex_index: u32,
}

impl InternalValueOrReference {
    #[inline]
    fn calculate_flags(rest: u32, locality: Locality,
                       is_nullable: bool, in_module_scope: bool) -> u32 {
        (locality as u32)
        | (is_nullable as u32) << IS_NULLABLE_BIT_INDEX
        | (in_module_scope as u32) << IN_MODULE_SCOPE_BIT_INDEX
    }

    pub fn new_redirect(module: FileIndex, node_index: NodeIndex,
                        locality: Locality, is_nullable: bool, in_module_scope: bool) -> Self {
        let flags = Self::calculate_flags(module.0, locality, is_nullable, in_module_scope);
        Self {flags, node_or_complex_index: node_index}
    }

    pub fn new_multi_definition() -> Self {
        todo!()
    }

    pub fn new_complex_value() -> Self {
        todo!()
    }

    pub fn new_missing_or_unknown(module: FileIndex, locality: Locality) -> Self {
        let flags = Self::calculate_flags(module.0, locality, false, false);
        Self {flags, node_or_complex_index: 0}
    }

    pub fn new_simple_language_specific(
        type_: PythonValueEnum, locality: Locality, is_nullable: bool,
        in_module_scope: bool
    ) -> Self {
        let flags = Self::calculate_flags(0, locality, is_nullable, in_module_scope);
        Self {flags, node_or_complex_index: 0}
    }

    pub fn new_language_specific(
        type_: PythonValueEnum,
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
        Self {flags: Self::calculate_flags(0, locality, false, false), node_or_complex_index: 0}
    }

    fn get_locality(self) -> Locality {
        unsafe { mem::transmute(self.flags << 28 & 7) }
    }

    pub fn in_module_scope(self) -> bool {
        self.flags & IN_MODULE_SCOPE_MASK != 0
    }

    pub fn is_calculated(self) -> bool {
        self.flags & IS_ANALIZED_MASK != 0
    }

    pub fn is_calculating(self) -> bool {
        self.flags == 1
    }

    fn is_recursion_error(self) -> bool {
        unimplemented!();
        //self.flags & REST_MASK & 1 == 1
    }

    /*
    fn get_x(self) -> ValueOrReference {
        if self.is_uncalculated() {
            return ValueOrReference::Uncalculated;
        }
        if self.is_calculating() {
            return ValueOrReference::Calculating;
        }
        if self.is_recursion_error() {
            return ValueOrReference::RecursionError;
        }
        if self.is_value() {
            panic!();
            //ValueOrReference::Value(1)
        } else {
            ValueOrReference::Reference(Reference::Redirect(FileIndex(self.flags & FILE_MASK), self.node_index))
        }
    }
    */
}

/*
enum ValueOrReference<T> {
    Value(Value<T>),
    Reference(Reference),
    Uncalculated,
    Calculating,
    RecursionError,
}
*/

#[derive(Debug)]
#[repr(u32)]
enum InternalValueOrReferenceType {
    Redirect = 1 << TYPE_BIT_INDEX,
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
pub enum PythonValueEnum {
    String,
    Bytes,
    Float,
    Integer,
    Complex,
    Bool,
    None,

    SelfParam,
    Param,
    SimpleGeneric, // primary: primary '[' slices ']'
    ParamWithDefault, // TODO Redirect to default maybe?
    LazyInferredClass, // A class that will be inferred later.
    LazyInferredFunction, // A function that will be inferred later.
    Class(NodeIndex), // The index to the __init__ name or 0
    Function(NodeIndex),  // Result
    NoReturnFunction,

    TypeVar,
    Any,
}

#[derive(Debug)]
#[repr(u32)]
pub enum Locality {
    // Intern: 0xx
    Stmt = 1 << LOCALITY_BIT_INDEX,
    ClassOrFunction,
    MostOuterClassOrFunction,
    File,

    // Extern: 1xx
    DirectExtern,  // Contains a direct link that can be checked
    ComplexExtern,  // Means we have to recalculate the value all the links
    ImplicitExtern,  // Contains star imports for now (always recheck on invalidation of the module)
}

struct InternalValue(u32, u32);

#[derive(Debug)]
pub struct ValueLink {
    file: FileIndex,
    node_index: NodeIndex,
}

#[derive(Debug)]
pub enum ComplexValue {
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
}

impl Database {
    pub fn new(file_state_loaders: FileStateLoaders) -> Self {
        Self {
            in_use: false,
            file_system_reader: Box::<FileSystemReader>::new(Default::default()),
            file_state_loaders,
            files: Default::default(),
            path_to_file: Default::default(),
            workspaces: Default::default(),
            files_managed_by_client: Default::default(),
        }
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

    pub fn get_file_state(&self, index: FileIndex) -> &dyn FileState {
        self.files.get(index.0 as usize).unwrap()
    }

    pub fn get_file_state_index_by_path(&self, path: &str) -> Option<FileIndex> {
        self.path_to_file.get(path).copied()
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
}

struct Workspace {
    root: DirectoryOrFile,
    //watcher: dyn notify::Watcher,
}

enum DirectoryOrFile {
    File(Box<str>, Option<FileIndex>),
    Directory(Box<str>, Vec<DirectoryOrFile>),
}
