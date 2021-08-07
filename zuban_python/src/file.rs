use std::fs;
use std::cell::{Cell, UnsafeCell};
use std::pin::Pin;
use std::fmt;
use std::any::Any;
use regex::Regex;
use parsa::{CodeIndex, NodeIndex, Node};
use parsa_python::{PythonTree, PythonTerminalType, PythonNonterminalType,
                   SiblingIterator, PythonNode, PythonNodeType, PYTHON_GRAMMAR};
use PythonNodeType::{Nonterminal, Terminal, ErrorNonterminal, ErrorTerminal};
use crate::utils::SymbolTable;
use crate::name::{Name, Names, TreeName, ValueNames};
use crate::database::{Database, FileIndex, Locality, ValueOrReference, PythonValueEnum,
                      ValueLink, LocalityLink, ValueOrReferenceType, ComplexValue};
use crate::name_binder::NameBinder;
use crate::value::Class;
use crate::debug;

lazy_static::lazy_static! {
    static ref NEWLINES: Regex = Regex::new(r"\n|\r\n|\r").unwrap();
}

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

pub trait FileState {
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
        fn calculate<'b>(file: &'b PythonFile, database: &'b Database, node: PythonNode<'b>, position: CodeIndex) -> Leaf<'b> {
            match node.get_type() {
                Terminal(t) | ErrorTerminal(t) => {
                    match t {
                        PythonTerminalType::Name => Leaf::Name(Box::new(
                            TreeName::new(database, file, node)
                        )),
                        PythonTerminalType::Newline => {
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
                PythonNodeType::ErrorKeyword | PythonNodeType::Keyword => {
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
    tree: PythonTree,
    symbol_table: SymbolTable,
    //all_names_bloom_filter: Option<BloomFilter<&str>>,
    values_or_references: Vec<Cell<ValueOrReference>>,
    complex_values: Vec<ComplexValue>,
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

impl PythonFile {
    fn new(code: String) -> Self {
        let tree = PYTHON_GRAMMAR.parse(code);
        let length = tree.get_length();
        Self {
            tree,
            file_index: Cell::new(None),
            symbol_table: Default::default(),
            values_or_references: vec![Default::default(); length],
            complex_values: vec![],
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
            &self.symbol_table,
            &self.values_or_references,
            self.file_index.get().unwrap(),
            true, // is_global_scope
            None,
        );
        name_binder.index_block(self.tree.get_root_node(), true);

        self.values_or_references[0].set(ValueOrReference::new_node_analysis(
            Locality::File
        ));
    }

    fn calculate_node_scope_definitions(&self, node: PythonNode) {
        self.calculate_global_definitions_and_references();
        todo!();
    }

    fn cache_stmt_name(&self, stmt: PythonNode, name: PythonNode) {
        let child = stmt.get_nth_child(0);
        if child.is_type(Nonterminal(PythonNonterminalType::simple_stmts)) {
            for node in child.iter_children() {
                if node.is_type(Nonterminal(PythonNonterminalType::simple_stmt)) {
                    let simple_child = node.get_nth_child(0);
                    if simple_child.is_type(Nonterminal(PythonNonterminalType::assignment)) {
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

    fn cache_assignment_nodes(&self, assignment_node: PythonNode) {
        // | (star_targets "=" )+ (yield_expr | star_expressions)
        // | single_target ":" expression ["=" (yield_expr | star_expressions)]
        // | single_target augassign (yield_expr | star_expressions)
        use PythonNonterminalType::*;
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
                            let val = &self.values_or_references[n.index];
                            if val.get().is_calculated() {
                                todo!("{:?}", val.get().get_type());
                            }
                            val.set(inferred.value_or_ref);
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

    fn cache_star_expressions(&self, node: PythonNode) -> Inferred {
        debug_assert!(node.is_type(Nonterminal(PythonNonterminalType::star_expressions)));

        let mut iter = node.iter_children();
        let expression = iter.next().unwrap();
        if iter.next().is_none() {
            if expression.is_type(Nonterminal(PythonNonterminalType::expression)) {
                self.cache_expression(expression)
            } else {
                debug_assert!(node.is_type(Nonterminal(PythonNonterminalType::star_expression)));
                todo!("Add error: can't use starred expression here");
            }
        } else {
            todo!("it's a tuple, cache that!")
        }
    }

    fn cache_expression(&self, node: PythonNode) -> Inferred {
        // disjunction ["if" disjunction "else" expression] | lambda
        debug_assert!(node.is_type(Nonterminal(PythonNonterminalType::expression)));
        if let Some(result) = self.check_node_cache(node) {
            return result.as_local_redirect(self.get_file_index(), node.index as NodeIndex)
        }

        let mut iter = node.iter_children();
        let first = iter.next().unwrap();
        let inferred = match first.is_type(Nonterminal(PythonNonterminalType::lambda)) {
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
        self.values_or_references[node.index].set(inferred.value_or_ref);
        inferred
    }

    fn infer_expression_part(&self, node: PythonNode) -> Inferred {
        // Responsible for all
        use PythonNonterminalType::*;
        match node.get_type() {
            Nonterminal(atom) => self.infer_atom(node),
            _ => todo!("Did not handle {:?}", node),
        }
    }

    fn infer_atom(&self, node: PythonNode) -> Inferred {
        use PythonNonterminalType::*;
        debug_assert!(node.is_type(Nonterminal(atom)));
        if let Some(result) = self.check_node_cache(node) {
            return result
        }

        let mut iter = node.iter_children();
        let first = iter.next().unwrap();
        let value_enum = match first.get_type() {
            Terminal(PythonTerminalType::Name) => {
                return self.infer_name_reference(first)
            }
            Terminal(PythonTerminalType::Number) => {
                let code = first.get_code();
                if code.contains('j') {
                    PythonValueEnum::Complex
                } else if code.contains('.') {
                    PythonValueEnum::Float
                } else {
                    PythonValueEnum::Integer
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
                    PythonValueEnum::Bytes
                } else {
                    PythonValueEnum::String
                }
            }
            PythonNodeType::Keyword => {
                match first.get_code() {
                    "None" => PythonValueEnum::None,
                    "True" | "False" => PythonValueEnum::Bool,
                    "..." => PythonValueEnum::Ellipsis,
                    "(" => {
                        let next_node = iter.next().unwrap();
                        match next_node.get_type() {
                            Nonterminal(tuple_content) => PythonValueEnum::Tuple,
                            Nonterminal(yield_expr) => {
                                todo!("yield_expr");
                            }
                            Nonterminal(named_expression) => {
                                todo!("named_expression");
                            }
                            Nonterminal(comprehension) => PythonValueEnum::ComprehensionGenerator,
                            PythonNodeType::Keyword => {
                                debug_assert_eq!(next_node.get_code(), ")");
                                PythonValueEnum::Tuple
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
        self.values_or_references[node.index].set(val);
        Inferred::new(val, self.get_file_index(), node.index as u32)
    }

    fn infer_name_reference(&self, node: PythonNode) -> Inferred {
        todo!("name reference {:?}", node)
    }

    pub fn infer_name(&self, database: &Database, name: PythonNode) -> ValueNames {
        self.calculate_global_definitions_and_references();
        self.infer_node(database, name)
    }

    #[inline]
    fn check_node_cache(&self, node: PythonNode) -> Option<Inferred> {
        let value = self.values_or_references[node.index].get();
        if value.is_calculated() {
            debug!("Infer {:?} from cache: {:?}", node.get_code(), value.get_type());
            match value.get_type() {
                ValueOrReferenceType::Redirect => {
                    todo!("FOOO");
                }
                ValueOrReferenceType::NodeAnalysis => {
                    panic!("Invalid state, should not happen {:?}", node);
                }
                _ => {
                    Some(Inferred::new(value, self.get_file_index(), node.index as u32))
                }
            }
        } else {
            if value.is_calculating() {
                todo!("Set recursion error and return that");
            }
            None
        }
    }

    fn infer_node(&self, database: &Database, node: PythonNode) -> ValueNames {
        use ValueOrReferenceType::*;
        let value = self.values_or_references[node.index as usize].get();
        if value.is_calculated() {
            match value.get_type() {
                Redirect => {
                    let file_index = value.get_file_index();
                    if self.file_index.get().unwrap() == file_index {
                        let next = self.tree.get_node_by_index(value.get_node_index());
                        self.infer_node(database, next)
                    } else {
                        todo!("External Module Redirect")
                    }
                }
                LanguageSpecific => {
                    self.resolve_python_value(database, value.get_language_specific());
                    todo!()
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
            let stmt = node.get_parent_until(&[
                Nonterminal(PythonNonterminalType::lambda),
                Nonterminal(PythonNonterminalType::comprehension),
                Nonterminal(PythonNonterminalType::dict_comprehension),
                Nonterminal(PythonNonterminalType::stmt),
            ]).expect("There should always be a stmt");

            if !self.values_or_references[stmt.index as usize].get().is_calculated() {
                if !stmt.is_type(Nonterminal(PythonNonterminalType::stmt)) {
                    todo!()
                }
                //self.calculate_node_scope_definitions(node);
                if is_name_reference(node) {
                    todo!("is extern");
                } else {
                    // Is a reference and should have been calculated.
                    self.cache_stmt_name(stmt, node);
                }
            }
            debug_assert!(self.values_or_references[node.index as usize].get().is_calculated());
            self.infer_node(database, node)
        }
    }

    fn resolve_python_value(&self, database: &Database, value: PythonValueEnum) {
        match value {
            PythonValueEnum::String => todo!(),
            actual => todo!("{:?}", actual)
        }
    }

    fn lookup_global(&self, name: &str) -> Option<LocalityLink> {
        self.calculate_global_definitions_and_references();
        self.symbol_table.lookup_symbol(name).map(|node_index| LocalityLink {
            file: self.get_file_index(),
            node_index,
            locality: Locality::DirectExtern,
        })
    }

    fn create_class(&self, node: NodeIndex) -> Class<'_> {
        Class::new(self)
    }
}

fn load_builtin_class_from_str<'a>(database: &'a Database, name: &'static str) -> Class<'a> {
    let builtins = database.python_state.get_builtins();
    builtins.create_class(builtins.lookup_global(name).unwrap().node_index)
}

struct Inferred {
    value_or_ref: ValueOrReference,
    definition: ValueLink,
}

impl Inferred {
    fn new(value_or_ref: ValueOrReference, file: FileIndex, node_index: NodeIndex) -> Self {
        Self {value_or_ref, definition: ValueLink {file, node_index}}
    }

    fn as_local_redirect(&self, file: FileIndex, node_index: NodeIndex) -> Self {
        let value_or_ref = ValueOrReference::new_redirect(
            file,
            node_index,
            Locality::Stmt,
            false,
            false,
        );
        Self {value_or_ref, definition: self.definition}
    }
}

fn is_name_reference(name: PythonNode) -> bool {
    debug_assert!(name.is_type(Terminal(PythonTerminalType::Name)));
    !name.get_parent().unwrap().is_type(
        Nonterminal(PythonNonterminalType::name_definition)
    )
}

enum Target<'a> {
    Tuple(TargetIterator<'a>),
    Name(PythonNode<'a>),
    Expression(PythonNode<'a>),
    Starred(PythonNode<'a>),
}

impl<'a> Target<'a> {
    fn new(node: PythonNode<'a>) -> Self {
        // star_targets: ",".star_target+ [","]
        let mut iterator = node.iter_children();
        let first = iterator.next().unwrap();
        if iterator.next().is_none() {
            if first.is_type(Nonterminal(PythonNonterminalType::name_definition)) {
                Self::Name(first.get_nth_child(0))
            } else if first.is_type(Nonterminal(PythonNonterminalType::t_primary)) {
                Self::Expression(first)
            } else if first.is_type(Nonterminal(PythonNonterminalType::star_target_brackets)) {
                todo!("star_target_brackets")
            } else if first.is_type(Nonterminal(PythonNonterminalType::star_target)) {
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
