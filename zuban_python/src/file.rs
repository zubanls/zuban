use std::fs;
use std::cell::{Cell, UnsafeCell};
use std::pin::Pin;
use std::fmt;
use std::any::Any;
use regex::Regex;
use parsa::{CodeIndex, NodeIndex, Node};
use parsa_python::{PyTree, TerminalType, NonterminalType,
                   SiblingIterator, PyNode, PyNodeType, PYTHON_GRAMMAR};
use PyNodeType::{Nonterminal, Terminal, ErrorNonterminal, ErrorTerminal};
use crate::utils::{SymbolTable, InsertOnlyVec};
use crate::name::{Name, Names, TreeName, ValueNames, WithValueName};
use crate::database::{Database, FileIndex, Locality, ValueOrReference, ValueEnum,
                      LocalityLink, ValueOrReferenceType, ComplexValue};
use crate::name_binder::NameBinder;
use crate::value::{Class, Value};
use crate::debug;

lazy_static::lazy_static! {
    static ref NEWLINES: Regex = Regex::new(r"\n|\r\n|\r").unwrap();
}

type InvalidatedDependencies = Vec<FileIndex>;
type LoadFileFunction<F> = &'static dyn Fn(String) -> F;
pub type ComplexValues = InsertOnlyVec<ComplexValue>;

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
        vec!["py", "pyi"]
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

pub trait AsAny {
    fn as_any(&self) -> &dyn Any where Self : 'static;
}

impl<T> AsAny for T {
    fn as_any(&self) -> &dyn Any where Self : 'static {
        self
    }
}

pub trait File: std::fmt::Debug+AsAny {
    fn get_implementation<'a>(&self, names: Names<'a>) -> Names<'a> {
        vec![]
    }
    fn get_leaf<'a>(&'a self, database: &'a Database, position: CodeIndex) -> Leaf<'a>;
    fn get_file_index(&self) -> FileIndex;
    fn set_file_index(&self, index: FileIndex);

    fn line_column_to_byte(&self, line: usize, column: usize) -> CodeIndex;
    fn byte_to_line_column(&self, byte: CodeIndex) -> (usize, usize);
}

pub trait FileState: fmt::Debug {
    fn get_path(&self) -> &str;
    fn get_file(&self, database: &Database) -> Option<&(dyn File + 'static)>;
    fn set_file_index(&self, index: FileIndex);
}

impl<F: File> FileState for LanguageFileState<F> {
    fn get_path(&self) -> &str {
        &self.path
    }

    fn get_file(&self, database: &Database) -> Option<&(dyn File + 'static)> {
        match unsafe {&*self.state.get()} {
            InternalFileExistence::Missing => None,
            InternalFileExistence::Parsed(f) => Some(f),
            InternalFileExistence::Unparsed(loader, file_index_cell) => {
                // It is extremely important to deal with the data given here before overwriting it
                // in `slot`. Otherwise we access memory that has different data structures.
                let file_index = file_index_cell.get().unwrap();
                unsafe {
                    *self.state.get() = InternalFileExistence::Parsed(
                        loader(database.file_system_reader.read_file(&self.path))
                    )
                };

                let file = self.get_file(database);
                file.unwrap().set_file_index(file_index);
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

pub struct LanguageFileState<F: 'static> {
    path: String,
    // Unsafe, because the file is parsed lazily
    state: UnsafeCell<InternalFileExistence<F>>,
    invalidates: Vec<FileIndex>,
}

impl<F> fmt::Debug for LanguageFileState<F> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("LanguageFileState")
         .field("path", &self.path)
         .field("state", unsafe{&*self.state.get()})
         .field("invalidates", &self.invalidates)
         .finish()
    }
}

impl<F: File> LanguageFileState<F> {
    fn new_parsed(path: String, file: F) -> Self {
        Self {
            path,
            state: UnsafeCell::new(
                InternalFileExistence::Parsed(file)),
            invalidates: vec![]}
    }

    fn new_unparsed(path: String, loader: LoadFileFunction<F>) -> Self {
        Self {
            path,
            state: UnsafeCell::new(
                InternalFileExistence::Unparsed(loader, Cell::new(None))),
            invalidates: vec![]}
    }

    fn new_does_not_exist(path: String) -> Self {
        Self {
            path,
            state: UnsafeCell::new(
                InternalFileExistence::Missing),
            invalidates: vec![]}
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
        fn calculate<'b>(file: &'b PythonFile, database: &'b Database, node: PyNode<'b>, position: CodeIndex) -> Leaf<'b> {
            match node.get_type() {
                Terminal(t) | ErrorTerminal(t) => {
                    match t {
                        TerminalType::Name => Leaf::Name(Box::new(
                            TreeName::new(database, file, node)
                        )),
                        TerminalType::Newline => {
                            if node.start() == position {
                                if let Some(prev) = node.get_previous_leaf() {
                                    if prev.end() == position {
                                        return calculate(file, database, prev, position);
                                    }
                                }
                            }
                            Leaf::None
                        }
                        _ => Leaf::None,
                    }
                }
                PyNodeType::ErrorKeyword | PyNodeType::Keyword => {
                    Leaf::Keyword(node.get_code().to_owned())
                }
                Nonterminal(n) | ErrorNonterminal(n) => {
                    panic!("{}", node.type_str())
                }
            }
        }
        calculate(self, database, self.tree.get_leaf_by_position(position), position)
    }

    fn get_file_index(&self) -> FileIndex {
        self.file_index.get().unwrap()
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

pub struct PythonFile {
    pub tree: PyTree,  // TODO should probably not be public
    symbol_table: SymbolTable,
    //all_names_bloom_filter: Option<BloomFilter<&str>>,
    values_or_references: Vec<Cell<ValueOrReference>>,
    complex_values: ComplexValues,
    dependencies: Vec<FileIndex>,
    file_index: Cell<Option<FileIndex>>,
    issues: Vec<Issue>,

    new_line_indices: UnsafeCell<Option<Vec<u32>>>,
}

impl fmt::Debug for PythonFile {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("PythonFile")
         .field("file_index", &self.file_index.get())
         .finish()
    }
}

impl<'db> PythonFile {
    fn new(code: String) -> Self {
        let tree = PYTHON_GRAMMAR.parse(code);
        let length = tree.get_length();
        Self {
            tree,
            file_index: Cell::new(None),
            symbol_table: Default::default(),
            values_or_references: vec![Default::default(); length],
            complex_values: InsertOnlyVec::default(),
            dependencies: vec![],
            issues: vec![],
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
        let mut name_binder = NameBinder::new(
            self,
            &self.symbol_table,
            &self.values_or_references,
            &self.complex_values,
            self.file_index.get().unwrap(),
            true, // is_global_scope
            None,
        );
        name_binder.index_file(self.tree.get_root_node());

        self.values_or_references[0].set(ValueOrReference::new_node_analysis(
            Locality::File
        ));
    }

    fn calculate_node_scope_definitions(&self, node: PyNode) {
        self.calculate_global_definitions_and_references();
        todo!();
    }

    pub fn infer_name(&'db self, database: &'db Database, name: PyNode) -> ValueNames<'db> {
        self.calculate_global_definitions_and_references();
        PythonInference {file: self, file_index: self.get_file_index(), database}
            .infer_arbitrary_node(name).to_value_names(database)
    }

    fn lookup_global(&self, name: &str) -> Option<LocalityLink> {
        self.calculate_global_definitions_and_references();
        self.symbol_table.lookup_symbol(name).map(|node_index| LocalityLink {
            file: self.get_file_index(),
            node_index,
            locality: Locality::DirectExtern,
        })
    }

    fn use_class(&self, node_index: NodeIndex) -> &Class {
        let v = self.values_or_references[node_index as usize].get();
        debug_assert_eq!(v.get_type(), ValueOrReferenceType::Complex);
        let complex = self.complex_values.get(v.get_complex_index() as usize).unwrap();
        match complex {
            ComplexValue::Class(c) => c,
            _ => unreachable!("Probably an issue with indexing: {:?}", &complex),
        }
    }
}

struct PythonInference<'a> {
    file: &'a PythonFile,
    file_index: FileIndex,
    database: &'a Database,
}

impl<'a> PythonInference<'a> {
    fn get_value(&self, index: NodeIndex) -> ValueOrReference {
        self.file.values_or_references[index as usize].get()
    }

    fn set_value(&self, index: NodeIndex, val: ValueOrReference) {
        self.file.values_or_references[index as usize].set(val);
    }

    fn cache_stmt_name(&self, stmt: PyNode, name: PyNode) {
        let child = stmt.get_nth_child(0);
        if child.is_type(Nonterminal(NonterminalType::simple_stmts)) {
            for node in child.iter_children() {
                if node.is_type(Nonterminal(NonterminalType::simple_stmt)) {
                    let simple_child = node.get_nth_child(0);
                    if simple_child.is_type(Nonterminal(NonterminalType::assignment)) {
                        self.cache_assignment_nodes(simple_child);
                    } else {
                        unreachable!("Found type {:?}", simple_child.get_type());
                    }
                }
            }
        } else {
            unreachable!("Found type {:?}", child.get_type());
        }
    }

    fn cache_assignment_nodes(&self, assignment_node: PyNode) {
        // | (star_targets "=" )+ (yield_expr | star_expressions)
        // | single_target ":" expression ["=" (yield_expr | star_expressions)]
        // | single_target augassign (yield_expr | star_expressions)
        use NonterminalType::*;
        let mut expression_node = None;
        let mut annotation_node = None;
        for child in assignment_node.iter_children() {
            match child.get_type() {
                Nonterminal(expression) => {
                    annotation_node = Some(child);
                }
                Nonterminal(yield_expr | star_expressions) => {
                    expression_node = Some(child);
                }
                _ => {}
            }
        }
        let inferred = match annotation_node {
            Some(annotation_node) => {
                todo!();
            }
            None => {
                let expression_node = expression_node.unwrap();
                if expression_node.is_type(Nonterminal(yield_expr)) {
                    todo!("cache yield expr");
                } else {
                    self.cache_star_expressions(expression_node)
                }
            }
        };
        for child in assignment_node.iter_children() {
            match child.get_type() {
                Nonterminal(star_targets) => {
                    match Target::new(child) {
                        Target::Tuple(target_iterator) => {
                            todo!("Tuple unpack");
                        }
                        Target::Name(n) => {
                            let val = self.get_value(n.index);
                            if val.is_calculated() {
                                todo!("{:?}", val.get_type());
                            }
                            self.set_value(n.index, inferred.value_or_ref);
                        }
                        Target::Expression(n) => {
                            todo!("{:?}", n);
                        }
                        Target::Starred(n) => {
                            todo!("Star tuple unpack");
                        }
                    };
                }
                Nonterminal(single_target) => {
                    todo!();
                }
                _ => {}
            }
        }
    }

    fn cache_star_expressions(&self, node: PyNode) -> Inferred<'a> {
        debug_assert!(node.is_type(Nonterminal(NonterminalType::star_expressions)));

        let mut iter = node.iter_children();
        let expression = iter.next().unwrap();
        if iter.next().is_none() {
            if expression.is_type(Nonterminal(NonterminalType::expression)) {
                self.cache_expression(expression)
            } else {
                debug_assert!(node.is_type(Nonterminal(NonterminalType::star_expression)));
                todo!("Add error: can't use starred expression here");
            }
        } else {
            todo!("it's a tuple, cache that!")
        }
    }

    fn cache_expression(&self, node: PyNode) -> Inferred<'a> {
        // disjunction ["if" disjunction "else" expression] | lambda
        debug_assert!(node.is_type(Nonterminal(NonterminalType::expression)));
        if let Some(result) = self.check_node_cache(node) {
            return result
        }

        let mut iter = node.iter_children();
        let first = iter.next().unwrap();
        let inferred = match first.is_type(Nonterminal(NonterminalType::lambda)) {
            true => {
                todo!("lambda")
            }
            false => {
                if iter.next().is_none() {
                    // No if
                    self.infer_expression_part(first)
                } else {
                    todo!("has an if in expression");
                }
            }
        };
        self.set_value(node.index, inferred.value_or_ref);
        inferred
    }

    fn infer_expression_part(&self, node: PyNode) -> Inferred<'a> {
        // Responsible for all
        use NonterminalType::*;
        match node.get_type() {
            Nonterminal(atom) => self.infer_atom(node),
            Nonterminal(primary) => self.infer_primary(node),
            _ => todo!("Did not handle {:?}", node),
        }
    }

    fn infer_primary(&self, node: PyNode) -> Inferred<'a> {
        //   primary "." Name
        // | primary "(" [arguments | comprehension] ")"
        // | primary "[" slices "]"
        // | atom
        use NonterminalType::*;
        let mut iter = node.iter_children();
        let first = iter.next().unwrap();
        let base = match first.get_type() {
            Nonterminal(atom) => self.infer_atom(first),
            Nonterminal(primary) => self.infer_primary(first),
            _ => unreachable!(),
        };
        let op = iter.next().unwrap();
        let second = iter.next().unwrap();
        match op.get_code() {
            "." => {
                base.run_function(|value| value.lookup(second.get_code()))
            }
            "(" => {
                todo!()
            }
            "[" => {
                todo!()
            }
            _ => unreachable!()
        }
    }

    fn infer_atom(&self, node: PyNode) -> Inferred<'a> {
        use NonterminalType::*;
        debug_assert!(node.is_type(Nonterminal(atom)));
        if let Some(result) = self.check_node_cache(node) {
            return result
        }

        let mut iter = node.iter_children();
        let first = iter.next().unwrap();
        let value_enum = match first.get_type() {
            Terminal(TerminalType::Name) => {
                return self.infer_name_reference(first)
            }
            Terminal(TerminalType::Number) => {
                let code = first.get_code();
                if code.contains('j') {
                    ValueEnum::Complex
                } else if code.contains('.') {
                    ValueEnum::Float
                } else {
                    ValueEnum::Integer
                }
            }
            Nonterminal(strings) => {
                let code = first.get_nth_child(0).get_code();
                let mut is_byte = false;
                for byte in code.bytes() {
                    if byte == b'"' || byte == b'\'' {
                        break
                    } else if byte == b'b' || byte == b'B' {
                        is_byte = true;
                        break
                    }
                }
                if is_byte {
                    ValueEnum::Bytes
                } else {
                    ValueEnum::String
                }
            }
            PyNodeType::Keyword => {
                match first.get_code() {
                    "None" => ValueEnum::None,
                    "True" | "False" => ValueEnum::Boolean,
                    "..." => ValueEnum::Ellipsis,
                    "(" => {
                        let next_node = iter.next().unwrap();
                        match next_node.get_type() {
                            Nonterminal(tuple_content) => ValueEnum::Tuple,
                            Nonterminal(yield_expr) => {
                                todo!("yield_expr");
                            }
                            Nonterminal(named_expression) => {
                                todo!("named_expression");
                            }
                            Nonterminal(comprehension) => ValueEnum::ComprehensionGenerator,
                            PyNodeType::Keyword => {
                                debug_assert_eq!(next_node.get_code(), ")");
                                ValueEnum::Tuple
                            }
                            _ => unreachable!()
                        }
                    }
                    "[" => {
                        todo!("List literal")
                    }
                    "{" => {
                        match iter.next().unwrap().get_type() {
                            Nonterminal(dict_content) | Nonterminal(dict_comprehension) => {
                                todo!("dict literal")
                            }
                            Nonterminal(star_named_expression) | Nonterminal(comprehension) => {
                                todo!("set literal")
                            }
                            _ => unreachable!()
                        }
                    }
                    _ => unreachable!()
                }
            }
            _ => unreachable!()
        };
        let val = ValueOrReference::new_simple_language_specific(
            value_enum,
            Locality::Stmt,
            false, // is_nullable
            false,
        );
        self.set_value(node.index, val);
        Inferred::new(self.file, node.index, val)
    }

    fn infer_name_reference(&self, node: PyNode) -> Inferred<'a> {
        if let Some(result) = self.check_node_cache(node) {
            return result
        }
        todo!("star import? {:?}", node)
    }

    #[inline]
    fn check_node_cache(&self, node: PyNode) -> Option<Inferred<'a>> {
        let value = self.get_value(node.index);
        if value.is_calculated() {
            debug!("Infer {:?} from cache: {:?}", node.get_code(), value.get_type());
            match value.get_type() {
                ValueOrReferenceType::Redirect => {
                    if value.get_file_index() == self.file_index {
                        Some(
                            self.infer_arbitrary_node(
                                self.file.tree.get_node_by_index(value.get_node_index())))
                    } else {
                        todo!("different file")
                    }
                }
                ValueOrReferenceType::NodeAnalysis => {
                    panic!("Invalid state, should not happen {:?}", node);
                }
                _ => {
                    Some(Inferred::new(self.file, node.index, value))
                }
            }
        } else {
            if value.is_calculating() {
                todo!("Set recursion error and return that");
            }
            None
        }
    }

    fn infer_arbitrary_node(&self, node: PyNode) -> Inferred<'a> {
        if let Some(result) = self.check_node_cache(node) {
            return result
        }
        let stmt = node.get_parent_until(&[
            Nonterminal(NonterminalType::lambda),
            Nonterminal(NonterminalType::comprehension),
            Nonterminal(NonterminalType::dict_comprehension),
            Nonterminal(NonterminalType::stmt),
        ]).expect("There should always be a stmt");

        if !self.get_value(stmt.index).is_calculated() {
            if !stmt.is_type(Nonterminal(NonterminalType::stmt)) {
                todo!()
            }
            //self.calculate_node_scope_definitions(node);
            if is_name_reference(node) {
                todo!("is extern {:?}", node);
            } else {
                // Is a reference and should have been calculated.
                self.cache_stmt_name(stmt, node);
            }
        }
        debug_assert!(self.get_value(node.index).is_calculated());
        self.infer_arbitrary_node(node)
    }
}

fn load_builtin_class_from_str<'a>(database: &'a Database, name: &'static str) -> &'a Class {
    let builtins = database.python_state.get_builtins();
    let node_index = builtins.lookup_global(name).unwrap().node_index;
    let v = builtins.values_or_references[node_index as usize].get();
    debug_assert_eq!(v.get_type(), ValueOrReferenceType::Redirect);
    debug_assert_eq!(v.get_file_index(), builtins.get_file_index());
    builtins.use_class(v.get_node_index())
}

pub struct Inferred<'a> {
    file: &'a PythonFile,
    node_index: NodeIndex,
    value_or_ref: ValueOrReference,
}

impl<'a> Inferred<'a> {
    fn new(file: &'a PythonFile, node_index: NodeIndex, value_or_ref: ValueOrReference) -> Self {
        Self {file, node_index, value_or_ref}
    }

    fn to_value_names(&self, database: &'a Database) -> ValueNames<'a> {
        use ValueOrReferenceType::*;
        match self.value_or_ref.get_type() {
            Redirect => {
                unreachable!()
            }
            LanguageSpecific => {
                let class = self.resolve_python_value(database, self.value_or_ref.get_language_specific());
                vec![Box::new(WithValueName::new(database, class as &dyn Value))]
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
                unreachable!();
            }
        }
    }

    fn run_function(&self, callable: impl Fn(&dyn Value<'a>) -> Inferred<'a>) -> Inferred<'a> {
        todo!()
    }

    fn resolve_python_value(&self, database: &'a Database, value: ValueEnum) -> &'a Class {
        load_builtin_class_from_str(database, match value {
            ValueEnum::String => "str",
            ValueEnum::Integer => "int",
            ValueEnum::Float => "float",
            ValueEnum::Boolean => "bool",
            ValueEnum::Bytes => "bytes",
            ValueEnum::Complex => "complex",
            ValueEnum::Ellipsis => "ellipsis",  // TODO this should not even be public
            actual => todo!("{:?}", actual)
        })
    }
}

fn is_name_reference(name: PyNode) -> bool {
    debug_assert!(name.is_type(Terminal(TerminalType::Name)));
    !name.get_parent().unwrap().is_type(
        Nonterminal(NonterminalType::name_definition)
    )
}

enum Target<'a> {
    Tuple(TargetIterator<'a>),
    Name(PyNode<'a>),
    Expression(PyNode<'a>),
    Starred(PyNode<'a>),
}

impl<'a> Target<'a> {
    fn new(node: PyNode<'a>) -> Self {
        // star_targets: ",".star_target+ [","]
        let mut iterator = node.iter_children();
        let first = iterator.next().unwrap();
        if iterator.next().is_none() {
            if first.is_type(Nonterminal(NonterminalType::name_definition)) {
                Self::Name(first.get_nth_child(0))
            } else if first.is_type(Nonterminal(NonterminalType::t_primary)) {
                Self::Expression(first)
            } else if first.is_type(Nonterminal(NonterminalType::star_target_brackets)) {
                todo!("star_target_brackets")
            } else if first.is_type(Nonterminal(NonterminalType::star_target)) {
                Self::Starred(first.get_nth_child(1))
            } else {
                unreachable!();
            }
        } else {
            Self::Tuple(TargetIterator{siblings: node.iter_children()})
        }
    }
}

struct TargetIterator<'a> {
    siblings: SiblingIterator<'a>
}

impl<'a> Iterator for TargetIterator<'a> {
    type Item = Target<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        let current = self.siblings.next();
        if let Some(sibling) = current {
            self.siblings.next();
            Some(Target::new(sibling))
        } else {
            None
        }
    }
}
