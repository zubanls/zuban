use std::fs;
use std::cell::{Cell, UnsafeCell};
use std::pin::Pin;
use std::fmt;
use regex::Regex;
use parsa::{CodeIndex, NodeIndex, Node};
use parsa_python::{PythonTree, PythonTerminalType, PythonNonterminalType, PythonNode, PythonNodeType, PYTHON_GRAMMAR};
use PythonNodeType::{Nonterminal, Terminal, ErrorNonterminal, ErrorTerminal};
use crate::utils::DefinitionNames;
use crate::name::{Name, Names, TreeName, ValueNames};
use crate::database::{Database, FileIndex, Locality, InternalValueOrReference, InternalValueOrReferenceType, ComplexValue};
use crate::indexer::IndexerState;

lazy_static::lazy_static! {
    static ref NEWLINES: Regex = Regex::new(r"\n|\r\n|\r").unwrap();
}

type InvalidatedDependencies = Vec<FileIndex>;
type LoadFileFunction<F> = &'static dyn Fn(String) -> F;
pub type ValuesOrReferences = Vec<Cell<InternalValueOrReference>>;

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

    fn load_parsed(&self, path: String, code: String) -> Pin<Box<dyn FileState>>;

    fn load_unparsed(&self, path: String) -> Pin<Box<dyn FileState>>;
}

#[derive(Default)]
pub struct PythonFileLoader {}

impl FileStateLoader for PythonFileLoader {
    fn responsible_for_file_endings(&self) -> Vec<&str> {
        vec!("py", "pyi")
    }

    fn load_parsed(&self, path: String, code: String) -> Pin<Box<dyn FileState>> {
        Box::pin(
            LanguageFileState::new_parsed(path, PythonFile::new(code))
        )
    }

    fn load_unparsed(&self, path: String) -> Pin<Box<dyn FileState>> {
        Box::pin(
            LanguageFileState::new_unparsed(path, &PythonFile::new)
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
    fn set_file_index(&self, index: FileIndex);

    fn line_column_to_byte(&self, line: usize, column: usize) -> CodeIndex;
    fn byte_to_line_column(&self, byte: CodeIndex) -> (usize, usize);
}

pub trait FileState {
    fn get_path(&self) -> &str;
    fn get_file(&self, database: &Database) -> Option<&dyn File>;
    fn set_file_index(&self, index: FileIndex);
}

impl<F: File> FileState for LanguageFileState<F> {
    fn get_path(&self) -> &str {
        &self.path
    }

    fn get_file(&self, database: &Database) -> Option<&dyn File> {
        match unsafe {&*self.state.get()} {
            InternalFileExistence::Missing => None,
            InternalFileExistence::Parsed(f) => Some(f),
            InternalFileExistence::Unparsed(loader, file_index_cell) => {
                unsafe {
                    *self.state.get() = InternalFileExistence::Parsed(
                        loader(database.file_system_reader.read_file(&self.path))
                    )
                };
                let file = self.get_file(database);
                file.unwrap().set_file_index(file_index_cell.get().unwrap());
                file
            }
        }
    }

    fn set_file_index(&self, index: FileIndex) {
        match unsafe {&*self.state.get()} {
            InternalFileExistence::Missing => {},
            InternalFileExistence::Parsed(f) => f.set_file_index(index),
            InternalFileExistence::Unparsed(loader, file_index_cell) =>
                file_index_cell.set(Some(index)),
        }
    }
}

#[derive(Debug)]
pub struct LanguageFileState<F: 'static> {
    path: String,
    // Unsafe, because the file is parsed lazily
    state: UnsafeCell<InternalFileExistence<F>>,
    invalidates: Vec<FileIndex>,
}

impl<F: File> LanguageFileState<F> {
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
                InternalFileExistence::Unparsed(loader, Cell::new(None))),
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
    Unparsed(LoadFileFunction<F>, Cell<Option<FileIndex>>),
    Parsed(F),
}

impl<F> fmt::Debug for InternalFileExistence<F> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // Intentionally remove the T here, because it's usually huge and we are usually not
        // interested in that while debugging.
        match *self {
            Self::Missing => write!(f, "DoesNotExist"),
            Self::Unparsed(_, _) => write!(f, "Unparsed"),
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

    fn set_file_index(&self, index: FileIndex) {
        self.file_index.set(Some(index));
    }

    fn line_column_to_byte(&self, line: usize, column: usize) -> CodeIndex {
        let byte = self.get_lines()[line];
        // TODO column can be unicode, is that an issue?
        // TODO Also column can be bigger than the current line.
        byte + column as CodeIndex
    }

    fn byte_to_line_column(&self, byte: CodeIndex) -> (usize, usize) {
        let line = self.get_lines().partition_point(|&l| l < byte as CodeIndex);
        (line, byte as usize - line)
    }

}

#[derive(Debug)]
pub struct PythonFile {
    tree: PythonTree,
    definition_names: DefinitionNames,
    //all_names_bloom_filter: Option<BloomFilter<&str>>,
    values_or_references: ValuesOrReferences,
    complex_values: Vec<ComplexValue>,
    dependencies: Vec<FileIndex>,
    file_index: Cell<Option<FileIndex>>,
    issues: Vec<Issue>,

    new_line_indices: UnsafeCell<Option<Vec<u32>>>,
}

impl PythonFile {
    fn new(code: String) -> Self {
        let tree = PYTHON_GRAMMAR.parse(code);
        let length = tree.get_length();
        Self {
            tree,
            file_index: Cell::new(None),
            definition_names: Default::default(),
            values_or_references: vec!(Default::default(); length),
            complex_values: vec!(),
            dependencies: vec!(),
            issues: vec!(),
            new_line_indices: UnsafeCell::new(None),
        }
    }

    fn get_lines(&self) -> &[u32] {
        let ptr = unsafe {&mut *self.new_line_indices.get()};
        if ptr.is_none() {
            // TODO probably use a OnceCell or something
            let mut v = vec![0];
            for m in NEWLINES.find_iter(self.tree.get_code()) {
                v.push(m.end() as CodeIndex);
            }
            *ptr = Some(v);
        }
        ptr.as_ref().unwrap()
    }

    fn calculate_global_definitions_and_references(&self) {
        if self.values_or_references[0].get().is_calculated() {
            // It was already done.
            return
        }
        let mut indexer_state = IndexerState::new(
            &self.definition_names,
            &self.values_or_references,
            self.file_index.get().unwrap(),
            true, // is_global_scope
            None,
        );
        indexer_state.index_block(self.tree.get_root_node(), true);

        self.values_or_references[0].set(InternalValueOrReference::new_node_analysis(
            Locality::File
        ));
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
                Nonterminal(named_expression) => {
                    todo!()
                }
                Nonterminal(_) | ErrorNonterminal(_) => {
                    todo!("Search for references");
                }
                _ => {
                    todo!()
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

    pub fn infer_name(&self, name: PythonNode) -> ValueNames {
        use InternalValueOrReferenceType::*;
        self.calculate_global_definitions_and_references();
        let value = self.values_or_references[name.index as usize].get();
        if value.is_calculated() {
            match value.get_type() {
                Redirect => {
                    todo!();
                }
                LanguageSpecific => {
                    todo!();
                }
                MultiDefinition => {
                    todo!();
                }
                MissingOrUnknown => {
                    vec![]
                }
                Complex => {
                    todo!();
                }
                FileReference => {
                    todo!();
                }
                NodeAnalysis => {
                    todo!();
                }
            }
        } else {
            if value.is_calculating() {
                todo!();
            }

            let stmt = name.get_parent_until(&[
                Nonterminal(PythonNonterminalType::lambda),
                Nonterminal(PythonNonterminalType::comprehension),
                Nonterminal(PythonNonterminalType::dict_comprehension),
                Nonterminal(PythonNonterminalType::stmt),
            ]).expect("There should always be a stmt");

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
            self.infer_name(name)
        }
    }
}

fn is_name_reference(name: PythonNode) -> bool {
    debug_assert!(name.is_type(Terminal(PythonTerminalType::Name)));
    !name.get_parent().unwrap().is_type(
        Nonterminal(PythonNonterminalType::name_definition)
    )
}

fn get_function_or_class_name() {
}

                    /*
                    let parent_parent = parent.get_parent().unwrap();
                    match parent_parent.get_type() {
                        Nonterminal(dotted_as_name) => {
                            // import foo.bar.baz
                        }
                        Nonterminal(import_from_as_name) => {
                            // Name "as" name_definition | name_definition
                            first_child = parent_parent.get_nth_child(0)
                            if first_child.is_type(Nonterminal()) {
                                first_child = 
                            }
                        }
                        Nonterminal(pattern_capture_target) => {
                            // Pattern matching
                            todo!()
                        }
                        Nonterminal(named_expression) => {
                            todo!()
                        }
                        Nonterminal(t_atom) => {
                            todo!()
                        }
                        Nonterminal(single_target) => {
                            todo!()
                        }
                        Nonterminal(star_atom) => {
                            todo!()
                        }
                        Nonterminal(t_primary) => {
                            todo!()
                        }
                        _ => panic!("Should probably not happen: {:?}", parent_parent)
                    }
                    */

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
