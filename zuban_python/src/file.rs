use std::fs;
use std::collections::HashMap;
use std::cell::{Cell, UnsafeCell};
use std::pin::Pin;
use std::fmt;
use parsa::{CodeIndex, NodeIndex, Node};
use parsa_python::{PythonTree, PythonTerminalType, PythonNonterminalType, PythonNode, PythonNodeType, PYTHON_GRAMMAR};
use PythonNodeType::{Nonterminal, Terminal, ErrorNonterminal, ErrorTerminal};
use crate::utils::{InsertOnlyHashMapVec, HashableRawStr};
use crate::name::{Name, Names, TreeName};
use crate::database::{Database, FileIndex, Locality, InternalValueOrReference, ComplexValue, PythonValueEnum};

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
            Terminal(t) | ErrorTerminal(t) => {
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
            Nonterminal(n) | ErrorNonterminal(n) => {
                panic!("{}", node.type_str())
            }
        }
    }
}

#[derive(Debug)]
pub struct PythonFile {
    tree: PythonTree,
    definition_names: InsertOnlyHashMapVec<HashableRawStr, NodeIndex>,
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
            definition_names: Default::default(),
            values_or_references: vec!(Default::default(); length),
            complex_values: vec!(),
            dependencies: vec!(),
            issues: vec!(),
        }
    }

    fn calculate_global_definitions_and_references(&self) {
        if self.values_or_references[0].get().is_calculated() {
            // It was already done.
            return
        }
        self.index_block(self.tree.get_root_node(), true, true);

        self.values_or_references[0].set(InternalValueOrReference::new_node_analysis(
            Locality::File
        ));
    }

    fn add_new_definition(&self, name_def: PythonNode, type_: PythonValueEnum, is_global_scope: bool) {
        debug_assert!(name_def.is_type(Nonterminal(PythonNonterminalType::name_definition)));
        let name = name_def.get_nth_child(0);
        self.definition_names.push_to_vec(HashableRawStr::new(name.get_code()), name.index as u32);
        self.values_or_references[name.index].set(
            InternalValueOrReference::new_simple_language_specific(
                type_,
                Locality::Stmt,
                false,
                is_global_scope,
            )
        );
    }

    fn index_block(&self, block_node: PythonNode, ordered: bool, is_global_scope: bool) {
        // Theory:
        // - while_stmt, for_stmt: ignore order (at least mostly)
        // - match_stmt, if_stmt, try_stmt (only in coresponding blocks and after)
        // - sync_for_if_clause: reversed order and only in scope
        // - lambda: only in scope
        // - function_def, class_def: ignore
        use PythonNonterminalType::*;
        for child in self.tree.get_root_node().iter_children() {
            if child.is_type(Nonterminal(simple_stmts)) {
                let iterator = self.tree.get_root_node().iter_children();
            } else if child.is_type(Nonterminal(function_def)) {
                self.add_new_definition(
                    child.get_nth_child(1),
                    PythonValueEnum::LazyInferredFunction,
                    is_global_scope,
                );
            } else if child.is_type(Nonterminal(class_def)) {
                self.add_new_definition(
                    child.get_nth_child(1),
                    PythonValueEnum::LazyInferredClass,
                    is_global_scope,
                );
            } else if child.is_type(Nonterminal(decorated)) {
                self.index_decorated(child);
            } else if child.is_type(Nonterminal(while_stmt)) {
                self.index_while_stmt(child);
            } else if child.is_type(Nonterminal(for_stmt)){
                self.index_for_stmt(child);
            } else if child.is_type(Nonterminal(with_stmt)){
                self.index_with_stmt(child);
            } else if child.is_type(Nonterminal(async_stmt)) {
                let iterator = self.tree.get_root_node().iter_children();
                let mut iterator = iterator.skip(1);
                let inner = iterator.next().unwrap();
                if inner.is_type(Nonterminal(function_def)) || child.is_type(Nonterminal(class_def)) {
                } else if inner.is_type(Nonterminal(for_stmt)) {
                    self.index_for_stmt(inner);
                } else if inner.is_type(Nonterminal(with_stmt)) {
                    self.index_with_stmt(child);
                }
            } else {
                assert_eq!(child.get_type(), Terminal(PythonTerminalType::Newline));
            }
        }
    }

    fn index_decorated(&self, decorated: PythonNode) {
    }

    fn index_for_stmt(&self, for_stmt: PythonNode) {
        debug_assert_eq!(for_stmt.get_type(), Nonterminal(PythonNonterminalType::for_stmt));
    }

    fn index_while_stmt(&self, while_stmt: PythonNode) {
        debug_assert_eq!(while_stmt.get_type(), Nonterminal(PythonNonterminalType::while_stmt));
    }

    fn index_with_stmt(&self, with_stmt: PythonNode) {
        debug_assert_eq!(with_stmt.get_type(), Nonterminal(PythonNonterminalType::with_stmt));
    }

    fn search_definitions(&self, node: PythonNode) {
        use PythonNonterminalType::*;
        for child in node.iter_children() {
            match child.get_type() {
                Terminal(PythonTerminalType::Name)
                | ErrorTerminal(PythonTerminalType::Name) => {
                }
                Nonterminal(assignment) => {
                    todo!()
                }
                Nonterminal(function_def) => {
                    todo!()
                }
                Nonterminal(class_def) => {
                    todo!()
                }
                Nonterminal(import_name) => {
                    todo!()
                }
                Nonterminal(import_from) => {
                    todo!()
                }
                Nonterminal(for_stmt) => {
                    todo!()
                }
                Nonterminal(with_stmt) => {
                    todo!()
                }
                Nonterminal(sync_for_if_clause) => {
                    todo!()
                }
                Nonterminal(match_stmt) => {
                    todo!()
                }
                Nonterminal(if_stmt | while_stmt | try_stmt
                                            | async_stmt | decorated ) => {
                    self.search_definitions(child);
                }
                Nonterminal(del_stmt) => {
                    todo!()
                }
                Nonterminal(match_stmt) => {
                    todo!()
                }
                Nonterminal(_) | ErrorNonterminal(_) => {
                    todo!("Search for references");
                }
                    Nonterminal(named_expression) => {
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

    fn calculate_stmt_name(&self, stmt: PythonNode, name: PythonNode) {
        panic!("IMPL tuple unpack");
        //let definition = get_definition(name);
        //if definition.is_some() {
        //}
    }

    pub fn infer_name(&self, name: PythonNode) {
        self.calculate_global_definitions_and_references();
        let value = self.values_or_references[name.index as usize].get();
        if !value.is_calculated() {
            if value.is_calculating() {
                todo!();
            }

            let stmt = name; // todo!
            /*let stmt = name.get_parent_until(
                Nonterminal(PythonNonterminalType::stmt)
            );*/

            if !self.values_or_references[stmt.index as usize].get().is_calculated() {
                self.calculate_node_scope_definitions(name);
                if is_name_reference(name) {
                    panic!("is extern");
                } else {
                    // Is a reference and should have been calculated.
                    self.calculate_stmt_name(stmt, name);
                }
            }
            let value = self.values_or_references[name.index as usize].get();
            debug_assert!(value.is_calculated());
            return self.infer_name(name)
        }
        panic!()
    }
}

fn is_name_reference(name: PythonNode) -> bool {
    debug_assert!(name.is_type(Terminal(PythonTerminalType::Name)));
    name.get_parent().unwrap().is_type(
        Nonterminal(PythonNonterminalType::name_definition)
    )
}

fn get_function_or_class_name() {
}

fn get_defined_names<'a>(node: &PythonNode<'a>) -> Vec<PythonNode<'a>> {
    use PythonNonterminalType::*;
    match node.get_type() {
        Nonterminal(assignment) => {
            todo!()
        }
        Nonterminal(param_maybe_default) => {
            todo!()
        }
        Nonterminal(import_name) => {
            todo!()
        }
        Nonterminal(import_from) => {
            todo!()
        }
        Nonterminal(named_expression) => {
            todo!()
        }
        Nonterminal(for_stmt) => {
            todo!()
        }
        Nonterminal(with_stmt) => {
            todo!()
        }
        Nonterminal(sync_for_if_clause) => {
            todo!()
        }
        Nonterminal(del_stmt) => {
            todo!()
        }
        _ => vec!()
    }
}

fn get_definition(name: PythonNode) -> Option<PythonNode> {
    use PythonNonterminalType::*;

    debug_assert!(name.get_type() == Terminal(PythonTerminalType::Name));

    let mut parent = name.get_parent().unwrap();
    match parent.get_type() {
        Nonterminal(function_def | class_def) => {
            // There shouldn't be any other names with a direct parent func/class
            Some(parent)
        }
        Nonterminal(except_clause) => {
            Some(parent)
        }
        _ => {
            loop {
                match parent.get_type() {
                    Nonterminal(
                        assignment | param_maybe_default | sync_for_if_clause | with_stmt | for_stmt | import_name
                        | import_from | del_stmt | named_expression) => {

                        if get_defined_names(&parent).iter().any(|n| n.index == name.index) {
                            return Some(parent)
                        }
                        return None
                    }
                    Nonterminal(block | file) => {
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
