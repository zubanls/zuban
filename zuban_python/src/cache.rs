use std::mem;
use std::pin::Pin;
use std::path::{Path, PathBuf};
use std::collections::HashMap;
use parsa_python::PythonTree;
use parsa::NodeIndex;

use crate::file::{File, FileLoader};

#[derive(Clone, Copy)]
pub struct FileIndex(pub u32);

type ComplexIndex = u32;

// Most significant bits
// 27 bits = 134217728; 20 bits = 1048576
// 0xxxxx Reference
// 1xxxxx Value
// xYYYxx YYY = Locality
// -> x0xx Internal
// -> x1xx External
// -> 1xxxX unused
// -> 1xxx0 non nullable
// -> 1xxx1 nullable
// Rest 27 bits = FileIndex
// If Internal second field = Value
// If External second field = FileIndex

const IS_REFERENCE_MASK: u32 = 1 << 31;
const IS_DEFINITION_MASK: u32 = 1 << 30;
const LOCALITY_INDEX: usize = 27;
const LOCALITY_MASK: u32 = 0b111 << LOCALITY_INDEX;
const REST_MASK: u32 = LOCALITY_MASK | IS_REFERENCE_MASK | IS_DEFINITION_MASK;
const FILE_MASK: u32 = 0xFFFFFF; // 24 bits

const IS_EXTERN_MASK: u32 = 1 << 29;

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct InternalValueOrReference {
    flags: u32,
    node_index: NodeIndex,
}

impl InternalValueOrReference {
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
        self.flags & IS_REFERENCE_MASK != 0
    }

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
}

enum ValueOrReference {
    Value(Value),
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

enum Value {
    Class(NodeIndex),
    Function(NodeIndex),  // Result
    NoReturnFunction(NodeIndex),
    String,
    Bytes,
    Float,
    Integer,
    Complex,
    Bool,
    None,

    Unknown,
    Param,  // Can be optional if param has default `foo=None`
    SelfParam,
    ParamWithDefault(NodeIndex),
    Any,
    SimpleGeneric, // primary: primary '[' slices ']'
    TypeVar(NodeIndex),

    LocalLink(NodeIndex),
    Link(FileIndex, NodeIndex),
    ComplexIndex(ComplexIndex),

    //Optional<Value>,
    // list literal/vs func; instance; closure
}

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

struct ValueLink {
    file: FileIndex,
    node_index: NodeIndex,
}

pub enum ComplexValue {
    Union(Box<[ValueLink]>),
    Instance(Execution),
    Closure(ValueLink, Execution),
    Generic(Execution),
}

struct Execution {
    function: ValueLink,
    args: Box<[Value]>,
}

struct Issue {
    issue_id: u32,
    tree_node: NodeIndex,
    locality: Locality,
}

#[derive(Default)]
pub struct Database {
    in_use: bool,
    file_loaders: Box<[Box<dyn FileLoader>]>,
    files: Vec<Pin<Box<dyn File>>>,
    path_to_file: HashMap<&'static str, FileIndex>,
    workspaces: Vec<Workspace>,
    files_managed_by_client: HashMap<PathBuf, FileIndex>,
}

impl Database {
    pub fn acquire(&mut self) {
        self.in_use = true;
    }

    pub fn release(&mut self) {
        // todo handle watcher events here
        self.in_use = false;
    }

    pub fn get_file(&self, index: FileIndex) -> &dyn File {
        &*self.files[index.0 as usize]
    }

    pub fn get_file_index_by_path(&self, path: &str) -> Option<FileIndex> {
        self.path_to_file.get(path).copied()
    }

    pub fn load_file(&self, path: String, code: String) -> (FileIndex, &dyn File) {
        for file_loader in self.file_loaders.iter() {
            let extension = Path::new(&path).extension().unwrap();
            // Can unwrap because path is unicode.
            if file_loader.responsible_for_file_endings().contains(&extension.to_str().unwrap()) {
                let file = file_loader.load_file(path, code);
                return unsafe {self.insert_file(file)}
            }
        }
        unreachable!()
    }

    unsafe fn insert_file(&self, file: Pin<Box<dyn File>>) -> (FileIndex, &dyn File) {
        //let files = self.files as *const Vec<Pin<Box<dyn File>>>;
        //let files = files as *mut Vec<_> as &mut Vec<_>;
        //files.push(file);
        //&*file
        todo!()
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
