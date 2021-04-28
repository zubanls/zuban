use parsa::{CodeIndex, NodeIndex, Node};
use parsa_python::{PythonTree, PythonTerminalType, PythonNodeType, PYTHON_GRAMMAR};
use crate::name::{Name, Names, TreeName};
use crate::cache::{Database, FileIndex, Locality, InternalValueOrReference, ComplexValue};
use std::collections::HashMap;
use std::pin::Pin;
use std::cell::Cell;
use std::fmt;

type InvalidatedDependencies = Vec<FileIndex>;

#[derive(Debug)]
pub enum Leaf<'a> {
    Name(Box<dyn Name<'a> + 'a>),
    String,
    Number,
    Keyword(String),
    Other,
    None
}

pub trait FileLoader {
    fn responsible_for_file_endings(&self) -> Vec<&str>;

    fn load_file(&self, path: String, code: String) -> Pin<Box<dyn File>>;
}

#[derive(Default)]
pub struct PythonFileLoader {}

impl FileLoader for PythonFileLoader {
    fn responsible_for_file_endings(&self) -> Vec<&str> {
        vec!("py", "pyi")
    }

    fn load_file(&self, path: String, code: String) -> Pin<Box<dyn File>> {
        Box::pin(
            PythonFile {
                path,
                state: FileState::Parsed(
                    ParsedFile::new(PYTHON_GRAMMAR.parse(code))
                )
            }
        )
    }
}

pub trait File: std::fmt::Debug {
    //fn new(path: String, code: String) -> Self;
    fn get_path(&self) -> Option<&str>;

    fn get_implementation<'a>(&self, names: Names<'a>) -> Names<'a> {
        vec!()
    }
    
    fn get_leaf<'a>(&'a self, database: &'a Database, position: CodeIndex) -> Leaf<'a>;
}


#[derive(Debug)]
struct Issue {
    issue_id: u32,
    tree_node: NodeIndex,
    locality: Locality,
}

#[derive(Debug)]
pub struct PythonFile {
    path: String,
    state: FileState<ParsedFile>,
}

impl File for PythonFile {
    fn get_path(&self) -> Option<&str> {
        Some(&self.path)
    }

    fn get_implementation<'a>(&self, names: Names<'a>) -> Names<'a> {
        todo!()
    }

    fn get_leaf<'a>(&'a self, database: &'a Database, position: CodeIndex) -> Leaf<'a> {
        let node = self.state.get_parsed().tree.get_leaf_by_position(position);
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

enum FileState<T> {
    DoesNotExist,
    Unparsed,
    Parsed(T),
    InvalidatedDependencies(T, InvalidatedDependencies),
}

impl<T> FileState<T> {
    fn get_parsed(&self) -> &T {
        match self {
            Self::Parsed(x) | Self::InvalidatedDependencies(x, _) => {
                x
            }
            Self::DoesNotExist | Self::Unparsed => panic!("Looks like a programming error")
        }
    }
}

impl<T> fmt::Debug for FileState<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // Intentionally remove the T here, because it's usually huge and we are usually not
        // interested in that while debugging.
        match *self {
            Self::DoesNotExist => write!(f, "DoesNotExist"),
            Self::Unparsed => write!(f, "Unparsed"),
            Self::Parsed(_) => write!(f, "Parsed(_)"),
            Self::InvalidatedDependencies(_, _) => write!(f, "InvalidatedDependencies(_)"),
        }
    }
}

#[derive(Debug)]
struct ParsedFile {
    tree: PythonTree,
    definition_names: Option<HashMap<&'static str, NodeIndex>>,
    //reference_bloom_filter: BloomFilter<&str>,
    values_or_references: Vec<Cell<InternalValueOrReference>>,
    complex_values: Vec<ComplexValue>,
    dependencies: Vec<FileIndex>,
    issues: Vec<Issue>,
}

impl ParsedFile {
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
