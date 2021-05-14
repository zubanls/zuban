use std::fs;
use std::collections::HashMap;
use std::cell::{Cell, UnsafeCell};
use std::pin::Pin;
use std::fmt;
use parsa::{CodeIndex, NodeIndex, Node};
use parsa_python::{PythonTree, PythonTerminalType, PythonNonterminalType, PythonNode, PythonNodeType, PYTHON_GRAMMAR};
use crate::name::{Name, Names, TreeName};
use crate::database::{Database, FileIndex, Locality, InternalValueOrReference, ComplexValue};

type InvalidatedDependencies = Vec<FileIndex>;
type LoadFileFunction<F> = &'static dyn Fn(String) -> F;

pub trait VirtualFileSystemReader {
    fn read_file(&self, path: &str) -> String;
}

#[derive(Default)]
pub struct FileSystemReader {
}

impl VirtualFileSystemReader for FileSystemReader {
    fn read_file(&self, path: &str) -> String {
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
            FileState2::new_parsed(path, PythonFile::new(code))
        )
    }

    fn load_unparsed(&self, path: String) -> Pin<Box<dyn FileState3>> {
        Box::pin(
            FileState2::new_unparsed(path, &PythonFile::new)
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
    fn get_file(&self, database: &Database) -> Option<&dyn File>;
}

impl<F: File> FileState3 for FileState2<F> {
    fn get_path(&self) -> &str {
        &self.path
    }

    fn get_file(&self, database: &Database) -> Option<&dyn File> {
        match unsafe {&*self.state.get()} {
            InternalFileExistence::Missing => None,
            InternalFileExistence::Parsed(f) => Some(f),
            InternalFileExistence::Unparsed(loader) => {
                unsafe {
                    *self.state.get() = InternalFileExistence::Parsed(
                        loader(database.file_system_reader.read_file(&self.path))
                    )
                };
                self.get_file(database)
            }
        }
    }
}

#[derive(Debug)]
pub struct FileState2<F: 'static> {
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

enum InternalFileExistence<F: 'static> {
    Missing,
    Unparsed(LoadFileFunction<F>),
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
    definition_names: Option<HashMap<*const str, Box<[NodeIndex]>>>,
    //all_names_bloom_filter: Option<BloomFilter<&str>>,
    values_or_references: Vec<Cell<InternalValueOrReference>>,
    complex_values: Vec<ComplexValue>,
    dependencies: Vec<FileIndex>,
    issues: Vec<Issue>,
}

impl PythonFile {
    fn new(code: String) -> Self {
        let tree = PYTHON_GRAMMAR.parse(code);
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

    fn calculate_global_definitions_and_references(&self) {
        if self.definition_names.is_some() {
            // It was already done.
            return
        }
        for child in self.tree.get_root_node().iter_children() {
        }
    }

    fn search_definitions(&self, node: &PythonNode) {
        use PythonNonterminalType::*;
        for child in node.iter_children() {
            match child.get_type() {
                PythonNodeType::Terminal(PythonTerminalType::Name)
                | PythonNodeType::ErrorTerminal(PythonTerminalType::Name) => {
                }
                PythonNodeType::Nonterminal(expr_stmt) => {
                    todo!()
                }
                PythonNodeType::Nonterminal(function_def) => {
                    todo!()
                }
                PythonNodeType::Nonterminal(class_def) => {
                    todo!()
                }
                PythonNodeType::Nonterminal(import_name) => {
                    todo!()
                }
                PythonNodeType::Nonterminal(import_from) => {
                    todo!()
                }
                PythonNodeType::Nonterminal(for_stmt) => {
                    todo!()
                }
                PythonNodeType::Nonterminal(with_stmt) => {
                    todo!()
                }
                PythonNodeType::Nonterminal(sync_comp_for) => {
                    todo!()
                }
                PythonNodeType::Nonterminal(match_stmt) => {
                    todo!()
                }
                PythonNodeType::Nonterminal(if_stmt | while_stmt | try_stmt
                                            | async_stmt | decorated ) => {
                    self.search_definitions(&child);
                }
                PythonNodeType::Nonterminal(del_stmt) => {
                    todo!()
                }
                PythonNodeType::Nonterminal(match_stmt) => {
                    todo!()
                }
                PythonNodeType::Nonterminal(_) | PythonNodeType::ErrorNonterminal(_) => {
                    todo!("Search for references");
                }
                    PythonNodeType::Nonterminal(namedexpr_test) => {
                        todo!()
                    }
                _ => {
                    node;
                }
            }
        }
    }

    fn calculate_node_scope_definitions(&self, node: PythonNode) {
        self.calculate_global_definitions_and_references();
    }

    pub fn infer(&self, node: PythonNode) {
        let value = self.values_or_references[node.index as usize].get();
        if value.is_uncalculated() {
            if value.is_calculating() {
                todo!();
            }
            let definition = get_definition(node);
            if definition.is_some() {
            }
            panic!();
            return self.infer(node)
        }
        panic!()
    }
}

fn get_function_or_class_name() {
}

fn get_defined_names<'a>(node: &PythonNode<'a>) -> Vec<PythonNode<'a>> {
    use PythonNonterminalType::*;
    match node.get_type() {
        PythonNodeType::Nonterminal(expr_stmt) => {
            todo!()
        }
        PythonNodeType::Nonterminal(param) => {
            todo!()
        }
        PythonNodeType::Nonterminal(import_name) => {
            todo!()
        }
        PythonNodeType::Nonterminal(import_from) => {
            todo!()
        }
        PythonNodeType::Nonterminal(namedexpr_test) => {
            todo!()
        }
        PythonNodeType::Nonterminal(for_stmt) => {
            todo!()
        }
        PythonNodeType::Nonterminal(with_stmt) => {
            todo!()
        }
        PythonNodeType::Nonterminal(sync_comp_for) => {
            todo!()
        }
        PythonNodeType::Nonterminal(del_stmt) => {
            todo!()
        }
        _ => vec!()
    }
}

fn get_definition(name: PythonNode) -> Option<PythonNode> {
    use PythonNonterminalType::*;

    debug_assert!(name.get_type() == PythonNodeType::Terminal(PythonTerminalType::Name));

    let mut parent = name.get_parent().unwrap();
    match parent.get_type() {
        PythonNodeType::Nonterminal(function_def | class_def) => {
            // There shouldn't be any other names with a direct parent func/class
            Some(parent)
        }
        PythonNodeType::Nonterminal(except_clause) => {
            Some(parent)
        }
        _ => {
            loop {
                match parent.get_type() {
                    PythonNodeType::Nonterminal(
                        expr_stmt | param | sync_comp_for | with_stmt | for_stmt | import_name
                        | import_from | del_stmt | namedexpr_test) => {

                        if get_defined_names(&parent).iter().any(|n| n.index == name.index) {
                            return Some(parent)
                        }
                        return None
                    }
                    PythonNodeType::Nonterminal(suite | file) => {
                        return None;
                    }
                    _ => {}
                }
                dbg!(parent, parent.get_parent());
                parent = parent.get_parent().unwrap();
            }
        }
    }
}
