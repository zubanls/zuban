use std::mem;
use std::path::{Path, PathBuf};
use std::collections::HashMap;
use parsa::NodeIndex;

use crate::file::{File, FileLoader};
use crate::utils::InsertOnlyVec;

#[derive(Debug, Clone, Copy)]
pub struct FileIndex(pub u32);

type ComplexIndex = u32;
type FileLoaders = Box<[Box<dyn FileLoader>]>;

// Most significant bits
// 27 bits = 134217728; 20 bits = 1048576
// 0xxxxx Reference
// 1xxxxx Value
// xYYYxx YYY = Locality
// -> x0xx Internal
// -> x1xx External
// -> XxxxX unused
// -> Xxxx0 non nullable
// -> Xxxx1 nullable
// -> XXXXXx is_module_definition
// -> XXXXXXx unused
// Rest 26 bits = FileIndex
// If Internal second field = Value
// If External second field = FileIndex

const IS_VALUE_BIT_INDEX: usize = 31;
const IS_VALUE_MASK: u32 = 1 << IS_VALUE_BIT_INDEX;
const LOCALITY_INDEX: usize = 28;
const LOCALITY_MASK: u32 = 0b111 << LOCALITY_INDEX;

const REST_MASK: u32 = LOCALITY_MASK | IS_VALUE_MASK;
const FILE_MASK: u32 = 0xFFFFFF; // 24 bits

const IS_EXTERN_MASK: u32 = 1 << 30;

#[derive(Copy, Clone, Debug, Eq, PartialEq, Default)]
pub struct InternalValueOrReference {
    flags: u32,
    node_index: NodeIndex,
}

impl InternalValueOrReference {
    #[inline]
    fn calculate_flags(is_value: bool, other_module: FileIndex, locality: Locality,
                       is_nullable: bool, is_simple_module_definition: bool) -> u32 {
        (is_value as u32) << IS_VALUE_BIT_INDEX
        | (locality as u32) << LOCALITY_INDEX
        | (is_nullable as u32)
        | (is_simple_module_definition as u32)
    }

    pub fn new_local_reference(node_index: NodeIndex, locality: Locality, is_nullable: bool) -> Self {
        let flags = Self::calculate_flags(false, FileIndex(0), locality, is_nullable, false);
        Self {flags, node_index}
    }

    pub fn new_reference(other_module: FileIndex, node_index: NodeIndex,
                         locality: Locality, is_nullable: bool) -> Self {
        let flags = Self::calculate_flags(false, other_module, locality, is_nullable, false);
        Self {flags, node_index}
    }

    pub fn new_local_value_reference(node_index: NodeIndex, locality: Locality,
                                     is_nullable: bool, is_simple_module_definition: bool) -> Self {
        let flags = Self::calculate_flags(false, FileIndex(0), locality, is_nullable,
                                          is_simple_module_definition);
        Self {flags, node_index}
    }

    pub fn new_value_reference(file_index: FileIndex, node_index: NodeIndex,
                               locality: Locality, is_nullable: bool,
                               is_simple_module_definition: bool) -> Self {
        let flags = Self::calculate_flags(false, file_index, locality,
                                          is_nullable, is_simple_module_definition);
        Self {flags, node_index}
    }

    pub fn new_complex_value(node_index: NodeIndex) -> Self {
        todo!()
    }

    fn get_locality(self) -> Locality {
        unsafe { mem::transmute(self.flags << 28 & 7) }
    }

    fn is_extern(self) -> bool {
        self.flags & IS_EXTERN_MASK != 0
    }

    fn is_uncalculated(self) -> bool {
        self.flags == 0
    }

    fn is_calculating(self) -> bool {
        self.flags == 1
    }

    fn is_recursion_error(self) -> bool {
        unimplemented!();
        //self.flags & REST_MASK & 1 == 1
    }

    fn is_value(self) -> bool {
        self.flags & IS_VALUE_MASK == 0
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
        } else if self.is_extern() {
            ValueOrReference::Reference(Reference::Link(FileIndex(self.flags & FILE_MASK), self.node_index))
        } else {
            ValueOrReference::Reference(Reference::LocalLink(self.node_index))
        }
    }
    */
}

enum ValueOrReference<T> {
    Value(Value<T>),
    Reference(Reference),
    Uncalculated,
    Calculating,
    RecursionError,
}

enum Reference {
    LocalLink(NodeIndex),
    Link(FileIndex, NodeIndex),
    MultiReference(NodeIndex),
    Missing,
}

enum PythonValueEnum {
    String,
    Bytes,
    Float,
    Integer,
    Complex,
    Bool,
    None,

    SelfParam,
    Any,
    SimpleGeneric, // primary: primary '[' slices ']'
    NoReturnFunction(NodeIndex),
    ParamWithDefault(NodeIndex),
    TypeVar(NodeIndex),
    Class(NodeIndex),
    Function(NodeIndex),  // Result
    Param,  // Can be optional if param has default `foo=None`
}

enum Value<T> {
    Unknown,
    Specific(T),
    LocalRedirect(NodeIndex),
    Redirect(FileIndex, NodeIndex),
    ComplexIndex(ComplexIndex),

    //Optional<Value>,
    // list literal/vs func; instance; closure
}

type Foo = Value<PythonValueEnum>;

#[derive(Debug)]
#[repr(u32)]
pub enum Locality {
    // Intern: 0xx
    File,
    MostOuterClassOrFunction,
    ClassOrFunction,
    Stmt,

    // Extern: 1xx
    IndirectExtern,
    CheckFileExtern,
    NeedsRecheckFileExtern,
    DirectExtern,
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

#[derive(Default)]
pub struct Database {
    in_use: bool,
    file_loaders: FileLoaders,
    files: InsertOnlyVec<dyn File>,
    path_to_file: HashMap<&'static str, FileIndex>,
    workspaces: Vec<Workspace>,
    files_managed_by_client: HashMap<PathBuf, FileIndex>,
}

impl Database {
    pub fn new(file_loaders: FileLoaders) -> Self {
        Self {
            file_loaders,
            ..Default::default()
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

    pub fn get_file(&self, index: FileIndex) -> &dyn File {
        self.files.get(index.0 as usize).unwrap()
    }

    pub fn get_file_index_by_path(&self, path: &str) -> Option<FileIndex> {
        self.path_to_file.get(path).copied()
    }

    pub fn load_file(&self, path: String, code: String) -> FileIndex {
        for file_loader in self.file_loaders.iter() {
            let extension = Path::new(&path).extension().unwrap();
            // Can unwrap because path is unicode.
            if file_loader.responsible_for_file_endings().contains(&extension.to_str().unwrap()) {
                let file = file_loader.load_file(path, code);
                self.files.push(file);
                return FileIndex(self.files.len() as u32 - 1)
            }
        }
        unreachable!()
    }
}

struct Workspace {
    root: DirectoryOrFile,
    //watcher: dyn notify::Watcher,
}

enum DirectoryOrFile {
    File(&'static Path, Option<FileIndex>),
    Directory(&'static Path, Vec<DirectoryOrFile>),
}
