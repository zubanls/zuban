use parsa::{CodeIndex, NodeIndex, Node};
use parsa_python::{PythonTree, PythonTerminalType, PythonNodeType, PYTHON_GRAMMAR};
use crate::name::{Name, Names, TreeName};
use crate::cache::{Database, ModuleIndex, Locality, InternalValueOrReference, ComplexValue};
use std::collections::HashMap;
use std::pin::Pin;
use std::cell::Cell;

type InvalidatedDependencies = Vec<ModuleIndex>;

pub enum Leaf<'a> {
    Name(Box<dyn Name<'a> + 'a>),
    String,
    Number,
    Keyword(String),
    Other,
    None
}

pub trait ModuleLoader {
    fn responsible_for_file_endings(&self) -> Vec<&str>;

    fn load_file(&self, path: String, code: String) -> Pin<Box<dyn Module>>;
}

pub struct PythonModuleLoader {}

impl ModuleLoader for PythonModuleLoader {
    fn responsible_for_file_endings(&self) -> Vec<&str> {
        vec!(".py", ".pyi")
    }

    fn load_file(&self, path: String, code: String) -> Pin<Box<dyn Module>> {
        todo!()
        //Box::new(PythonModule {path, tree: PYTHON_GRAMMAR.parse(code)}).pin()
    }
}

pub trait Module {
    //fn new(path: String, code: String) -> Self;
    fn get_path(&self) -> Option<&str>;

    fn get_implementation<'a>(&self, names: Names<'a>) -> Names<'a> {
        vec!()
    }
    
    fn get_leaf<'a>(&'a self, database: &'a Database, position: CodeIndex) -> Leaf<'a>;
}


struct Issue {
    issue_id: u32,
    tree_node: NodeIndex,
    locality: Locality,
}

pub struct PythonModule {
    path: String,
    state: ModuleState<PythonTree>,
    definition_names: HashMap<&'static str, NodeIndex>,
    //reference_bloom_filter: BloomFilter<&str>,
    values_or_references: Vec<Cell<InternalValueOrReference>>,
    complex_values: Vec<ComplexValue>,
    dependencies: Vec<ModuleIndex>,
    issues: Vec<Issue>,
}

impl Module for PythonModule {
    fn get_path(&self) -> Option<&str> {
        Some(&self.path)
    }

    fn get_implementation<'a>(&self, names: Names<'a>) -> Names<'a> {
        todo!()
    }

    fn get_leaf<'a>(&'a self, database: &'a Database, position: CodeIndex) -> Leaf<'a> {
        let node = self.state.get_tree().get_leaf_by_position(position);
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
            PythonNodeType::Nonterminal(_) | PythonNodeType::ErrorNonterminal(_) => panic!(),
        }
    }
}

enum ModuleState<T> {
    DoesNotExist,
    Unparsed,
    Parsed(T),
    InvalidatedDependencies(T, InvalidatedDependencies),
}

impl<T> ModuleState<T> {
    fn get_tree(&self) -> &T {
        match self {
            Self::Parsed(x) | Self::InvalidatedDependencies(x, _) => {
                x
            }
            Self::DoesNotExist | Self::Unparsed => panic!("Looks like a programming error")
        }
    }
}
