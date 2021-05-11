use std::fs;
use parsa::{CodeIndex, NodeIndex, Node};
use parsa_python::{PythonTree, PythonTerminalType, PythonNodeType, PYTHON_GRAMMAR};
use crate::name::{Name, Names, TreeName};
use crate::database::{Database, FileIndex, Locality, InternalValueOrReference, ComplexValue};
use std::collections::HashMap;
use std::cell::{Cell, UnsafeCell};
use std::pin::Pin;
use std::fmt;

type InvalidatedDependencies = Vec<FileIndex>;
type LoadFileFunction<F> = Box<dyn Fn(&str) -> F>;

pub trait VirtualFileSystemReader {
    fn read(&self, path: &str) -> String;
}

#[derive(Default)]
pub struct FileSystemReader {
}

impl VirtualFileSystemReader for FileSystemReader {
    fn read(&self, path: &str) -> String {
        // TODO can error
        fs::read_to_string(path).unwrap()
    }
}


#[derive(Debug)]
pub enum Leaf<'a> {
    Name(Box<dyn Name<'a> + 'a>),
    String,
    Number,
    Keyword(String),
    Other,
    None
}

pub trait FileStateLoader {
    fn responsible_for_file_endings(&self) -> Vec<&str>;

    fn load_parsed(&self, path: String, code: String) -> Pin<Box<dyn FileState3>>;

    fn load_unparsed(&self, path: String) -> Pin<Box<dyn FileState3>>;
}

#[derive(Default)]
pub struct PythonFileLoader {}

impl FileStateLoader for PythonFileLoader {
    fn responsible_for_file_endings(&self) -> Vec<&str> {
        vec!("py", "pyi")
    }

    fn load_parsed(&self, path: String, code: String) -> Pin<Box<dyn FileState3>> {
        Box::pin(
            FileState2::new_parsed(
                path,
                PythonFile::new(PYTHON_GRAMMAR.parse(code))
            )
        )
    }

    fn load_unparsed(&self, path: String) -> Pin<Box<dyn FileState3>> {
        Box::pin(
            FileState2::new_unparsed(path, )
        )
    }
}

pub trait FileLoader<F> {
    fn load_file(&self, path: String, code: String) -> F;
}

pub trait File: std::fmt::Debug {
    fn get_implementation<'a>(&self, names: Names<'a>) -> Names<'a> {
        vec!()
    }
    
    fn get_leaf<'a>(&'a self, database: &'a Database, position: CodeIndex) -> Leaf<'a>;
}

pub trait FileState3 {
    fn get_path(&self) -> &str;
    fn get_file(&self) -> Option<&dyn File>;
}

impl<F: File> FileState3 for FileState2<F> {
    fn get_path(&self) -> &str {
        &self.path
    }

    fn get_file(&self) -> Option<&dyn File> {
        match unsafe {&*self.state.get()} {
            InternalFileExistence::Missing => None,
            InternalFileExistence::Parsed(f) => Some(f),
            InternalFileExistence::Unparsed(loader) => {
                unsafe {
                    *self.state.get() = InternalFileExistence::Parsed(
                        loader(&self.path)
                    )
                };
                self.get_file()
            }
        }
    }
}

#[derive(Debug)]
pub struct FileState2<F> {
    path: String,
    // Unsafe, because the file is parsed lazily
    state: UnsafeCell<InternalFileExistence<F>>,
    invalidates: Vec<FileIndex>,
}

impl<F: File> FileState2<F> {
    fn new_parsed(path: String, file: F) -> Self {
        Self {
            path,
            state: UnsafeCell::new(
                InternalFileExistence::Parsed(file)),
            invalidates: vec!()}
    }

    fn new_unparsed(path: String, loader: LoadFileFunction<F>) -> Self {
        Self {
            path,
            state: UnsafeCell::new(
                InternalFileExistence::Unparsed(loader)),
            invalidates: vec!()}
    }

    fn new_does_not_exist(path: String) -> Self {
        Self {
            path,
            state: UnsafeCell::new(
                InternalFileExistence::Missing),
            invalidates: vec!()}
    }
}

enum InternalFileExistence<F> {
    Missing,
    Unparsed(Box<dyn Fn(&str) -> F>),
    Parsed(F),
}

impl<F> fmt::Debug for InternalFileExistence<F> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // Intentionally remove the T here, because it's usually huge and we are usually not
        // interested in that while debugging.
        match *self {
            Self::Missing => write!(f, "DoesNotExist"),
            Self::Unparsed(_) => write!(f, "Unparsed"),
            Self::Parsed(_) => write!(f, "Parsed(_)"),
        }
    }
}

#[derive(Debug)]
struct Issue {
    issue_id: u32,
    tree_node: NodeIndex,
    locality: Locality,
}

impl File for PythonFile {
    fn get_implementation<'a>(&self, names: Names<'a>) -> Names<'a> {
        todo!()
    }

    fn get_leaf<'a>(&'a self, database: &'a Database, position: CodeIndex) -> Leaf<'a> {
        let node = self.tree.get_leaf_by_position(position);
        match node.get_type() {
            PythonNodeType::Terminal(t) | PythonNodeType::ErrorTerminal(t) => {
                match t {
                    PythonTerminalType::Name => Leaf::Name(Box::new(
                        TreeName::new(database, self, node)
                    )),
                    _ => Leaf::None,
                }
            }
            PythonNodeType::ErrorKeyword | PythonNodeType::Keyword => {
                Leaf::Keyword(node.get_code().to_owned())
            }
            PythonNodeType::Nonterminal(n) | PythonNodeType::ErrorNonterminal(n) => {
                panic!("{}", node.type_str())
            }
        }
    }
}

#[derive(Debug)]
pub struct PythonFile {
    tree: PythonTree,
    definition_names: Option<HashMap<*const str, NodeIndex>>,
    //reference_bloom_filter: BloomFilter<&str>,
    values_or_references: Vec<Cell<InternalValueOrReference>>,
    complex_values: Vec<ComplexValue>,
    dependencies: Vec<FileIndex>,
    issues: Vec<Issue>,
}

impl PythonFile {
    fn new(tree: PythonTree) -> Self {
        let length = tree.get_length();
        Self {
            tree,
            definition_names: None,
            values_or_references: vec!(Default::default(); length),
            complex_values: vec!(),
            dependencies: vec!(),
            issues: vec!(),
        }
    }
}
