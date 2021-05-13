use std::mem;
use std::path::{Path, PathBuf};
use std::collections::HashMap;
use std::pin::Pin;
use parsa::NodeIndex;

use crate::file::{FileState3, FileStateLoader, VirtualFileSystemReader, FileSystemReader};
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
// xxxxxo is_module_definition
// xxxxxxo is_nullable
// xxxxxxxooo InternalValueOrReferenceType
// if true rest 22 bits reserved for ValueOrReference details

const IS_ANALIZED_BIT_INDEX: usize = 31;
const IS_INVALIDATED_BIT_INDEX: usize = 30;
const LOCALITY_BIT_INDEX: usize = 27; // Uses 3 bits
const IS_MODULE_DEFINITION_BIT_INDEX: usize = 26;
const IS_NULLABLE_BIT_INDEX: usize = 25;
const TYPE_BIT_INDEX: usize = 22; // Uses 3 bits

const REST_MASK: u32 = 0b11_1111_1111_1111_1111_1111;
const FILE_MASK: u32 = 0xFFFFFF; // 24 bits
const IS_ANALIZED_MASK: u32 = 1 << IS_ANALIZED_BIT_INDEX;

const IS_EXTERN_MASK: u32 = 1 << 30;

#[derive(Copy, Clone, Debug, Eq, PartialEq, Default)]
pub struct InternalValueOrReference {
    flags: u32,
    node_or_complex_index: u32,
}

impl InternalValueOrReference {
    #[inline]
    fn calculate_flags(other_module: FileIndex, locality: Locality,
                       is_nullable: bool, is_simple_module_definition: bool) -> u32 {
        (locality as u32)
        | (is_nullable as u32)
        | (is_simple_module_definition as u32)
    }

    pub fn new_redirect(other_module: FileIndex, node_index: NodeIndex,
                        locality: Locality, is_nullable: bool) -> Self {
        let flags = Self::calculate_flags(other_module, locality, is_nullable, false);
        Self {flags, node_or_complex_index: node_index}
    }

    pub fn new_multi_definition() -> Self {
        todo!()
    }

    pub fn new_complex_value() -> Self {
        todo!()
    }

    pub fn new_missing_or_unknown() -> Self {
        todo!()
    }

    pub fn new_language_specific() -> Self {
        todo!()
    }

    pub fn new_file_reference() -> Self {
        todo!()
    }

    pub fn new_missing_file() -> Self {
        // Imports that point nowhere
        todo!()
    }

    fn get_locality(self) -> Locality {
        unsafe { mem::transmute(self.flags << 28 & 7) }
    }

    pub fn is_uncalculated(self) -> bool {
        self.flags & IS_ANALIZED_MASK == 0
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
}

#[derive(Debug)]
#[repr(u32)]
enum PythonValueEnum {
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
    files: InsertOnlyVec<dyn FileState3>,
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

    pub fn get_file_state(&self, index: FileIndex) -> &dyn FileState3 {
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

    fn add_file_state(&self, file_state: Pin<Box<dyn FileState3>>) -> FileIndex {
        self.files.push(file_state);
        FileIndex(self.files.len() as u32 - 1)
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
