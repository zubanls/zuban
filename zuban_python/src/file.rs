use crate::arguments::Arguments;
use crate::database::{
    ComplexPoint, Database, FileIndex, Locality, LocalityLink, Point, PointType, Specific,
};
use crate::debug;
use crate::file_state::{File, Issue, Leaf};
use crate::imports::global_import;
use crate::inferred::Inferred;
use crate::name::{Names, TreeName, ValueNames};
use crate::name_binder::{NameBinder, NameBinderType};
use crate::utils::{InsertOnlyVec, SymbolTable};
use parsa::{CodeIndex, Node, NodeIndex};
use parsa_python::{
    NonterminalType, PyNode, PyNodeType, PyTree, SiblingIterator, TerminalType, PYTHON_GRAMMAR,
};
use regex::Regex;
use std::cell::{Cell, UnsafeCell};
use std::fmt;
use PyNodeType::{ErrorNonterminal, ErrorTerminal, Nonterminal, Terminal};

lazy_static::lazy_static! {
    static ref NEWLINES: Regex = Regex::new(r"\n|\r\n|\r").unwrap();
}

#[derive(Default)]
pub struct ComplexValues(InsertOnlyVec<ComplexPoint>);

impl ComplexValues {
    pub fn get(&self, index: usize) -> &ComplexPoint {
        self.0.get(index).unwrap()
    }

    pub fn insert(&self, points: &[Cell<Point>], node_index: NodeIndex, complex: ComplexPoint) {
        let complex_index = self.0.len() as u32;
        self.0.push(Box::pin(complex));
        points[node_index as usize].set(Point::new_complex_point(complex_index, Locality::Stmt));
    }
}

impl File for PythonFile {
    fn get_implementation<'a>(&self, names: Names<'a>) -> Names<'a> {
        todo!()
    }

    fn get_leaf<'a>(&'a self, database: &'a Database, position: CodeIndex) -> Leaf<'a> {
        fn calculate<'b>(
            file: &'b PythonFile,
            database: &'b Database,
            node: PyNode<'b>,
            position: CodeIndex,
        ) -> Leaf<'b> {
            match node.get_type() {
                Terminal(t) | ErrorTerminal(t) => match t {
                    TerminalType::Name => Leaf::Name(Box::new(TreeName::new(database, file, node))),
                    _ => Leaf::None,
                },
                PyNodeType::ErrorKeyword | PyNodeType::Keyword => Leaf::Keyword(node),
                Nonterminal(n) | ErrorNonterminal(n) => unreachable!("{}", node.type_str()),
            }
        }
        // First check the token left and right of the cursor
        let mut left = self.tree.get_leaf_by_position(position);
        let mut right = left;
        if left.start() == position {
            if let Some(n) = left.get_previous_leaf() {
                if n.end() == position {
                    left = n;
                }
            }
        } else if left.end() == position {
            if let Some(n) = left.get_next_leaf() {
                if n.start() == position {
                    right = n;
                }
            }
        }
        // From now on left is the node we're passing.
        if left.index != right.index {
            use TerminalType::*;
            let order = [
                Name,
                Number,
                String,
                Bytes,
                FStringString,
                FStringStart,
                FStringEnd,
            ];
            match left.get_type() {
                PyNodeType::ErrorKeyword | PyNodeType::Keyword => {
                    match right.get_type() {
                        PyNodeType::ErrorKeyword | PyNodeType::Keyword => {
                            let is_alpha =
                                |n: PyNode| n.get_code().chars().all(|x| x.is_alphanumeric());
                            if is_alpha(right) && !is_alpha(left) {
                                // Prefer keywords to operators
                                left = right;
                            }
                        }
                        Terminal(t) | ErrorTerminal(t) => {
                            // If it is any of the wanted types, just use that instead.
                            if order.contains(&t) {
                                left = right;
                            }
                        }
                        _ => unreachable!(),
                    }
                }
                Terminal(left_terminal) | ErrorTerminal(left_terminal) => {
                    match right.get_type() {
                        Terminal(right_terminal) | ErrorTerminal(right_terminal) => {
                            let order_func =
                                |typ| order.iter().position(|&t| t == typ).unwrap_or(usize::MAX);
                            let left_index = order_func(left_terminal);
                            let right_index = order_func(right_terminal);
                            // Both are terminals, prefer the one that is higher in the order
                            if right_index < left_index {
                                left = right;
                            }
                        }
                        _ => (),
                    }
                }
                Nonterminal(n) | ErrorNonterminal(n) => unreachable!(),
            }
        }
        calculate(self, database, left, position)
    }
    fn infer_operator_leaf<'a>(
        &'a self,
        database: &'a Database,
        leaf: PyNode<'a>,
    ) -> ValueNames<'a> {
        if ["(", "[", "{", ")", "]", "}"]
            .iter()
            .any(|&x| x == leaf.get_code())
        {
            let parent = leaf.get_parent().unwrap();
            if parent.is_type(Nonterminal(NonterminalType::primary)) {
                self.calculate_global_definitions_and_references();
                return self
                    .get_inference(database)
                    .infer_expression_part(parent)
                    .to_value_names();
            }
        }
        vec![]
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
    pub tree: PyTree, // TODO should probably not be public
    pub symbol_table: SymbolTable,
    //all_names_bloom_filter: Option<BloomFilter<&str>>,
    pub points: Vec<Cell<Point>>,
    pub complex_points: ComplexValues,
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
    pub fn new(code: String) -> Self {
        let tree = PYTHON_GRAMMAR.parse(code);
        let length = tree.get_length();
        Self {
            tree,
            file_index: Cell::new(None),
            symbol_table: Default::default(),
            points: vec![Default::default(); length],
            complex_points: Default::default(),
            dependencies: vec![],
            issues: vec![],
            new_line_indices: UnsafeCell::new(None),
        }
    }

    fn get_lines(&self) -> &[u32] {
        let ptr = unsafe { &mut *self.new_line_indices.get() };
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

    pub fn calculate_global_definitions_and_references(&self) {
        if self.get_point(0).is_calculated() {
            // It was already done.
            return;
        }
        self.with_global_binder(|binder| binder.index_file(self.tree.get_root_node()));

        self.set_point(0, Point::new_node_analysis(Locality::File));
    }

    fn with_global_binder(&'db self, func: impl FnOnce(&mut NameBinder<'db, 'db>)) {
        NameBinder::with_global_binder(
            &self.symbol_table,
            &self.points,
            &self.complex_points,
            self.file_index.get().unwrap(),
            None,
            func,
        )
    }

    fn calculate_node_scope_definitions(&self, node: PyNode) {
        self.calculate_global_definitions_and_references();
        let symbol_table = SymbolTable::default();
        self.with_global_binder(|binder| {
            binder.with_nested(NameBinderType::Function, &symbol_table, |b| {
                b.index_function_body(node)
            })
        });
    }

    pub fn get_inference(&'db self, database: &'db Database) -> PythonInference<'db> {
        PythonInference {
            file: self,
            file_index: self.get_file_index(),
            database,
        }
    }

    pub fn infer_name(&'db self, database: &'db Database, name: PyNode<'db>) -> ValueNames<'db> {
        self.calculate_global_definitions_and_references();
        self.get_inference(database)
            .infer_name(name)
            .to_value_names()
    }

    pub fn infer_name_by_index(
        &'db self,
        database: &'db Database,
        node_index: NodeIndex,
    ) -> Inferred<'db> {
        let node = self.tree.get_node_by_index(node_index);
        self.get_inference(database).infer_name(node)
    }

    pub fn infer_expression(
        &'db self,
        database: &'db Database,
        node: PyNode<'db>,
    ) -> Inferred<'db> {
        self.get_inference(database).infer_expression(node)
    }

    pub fn infer_expression_part(
        &'db self,
        database: &'db Database,
        node: PyNode<'db>,
    ) -> Inferred<'db> {
        self.get_inference(database).infer_expression_part(node)
    }

    #[inline]
    pub fn get_point(&self, index: NodeIndex) -> Point {
        self.points[index as usize].get()
    }

    #[inline]
    pub fn set_point(&self, index: NodeIndex, point: Point) {
        self.points[index as usize].set(point);
    }

    pub fn lookup_global(&self, name: &str) -> Option<LocalityLink> {
        self.calculate_global_definitions_and_references();
        self.symbol_table
            .lookup_symbol(name)
            .map(|node_index| LocalityLink {
                file: self.get_file_index(),
                node_index,
                locality: Locality::DirectExtern,
            })
    }
}

pub struct PythonInference<'a> {
    file: &'a PythonFile,
    file_index: FileIndex,
    database: &'a Database,
}

impl<'a> PythonInference<'a> {
    fn cache_stmt_name(&self, stmt: PyNode<'a>, name: PyNode<'a>) {
        debug!(
            "Infer stmt ({}, {})",
            self.file.get_file_index(),
            stmt.index
        );
        let child = stmt.get_nth_child(0);
        if child.is_type(Nonterminal(NonterminalType::simple_stmts)) {
            for node in child.iter_children() {
                if node.is_type(Nonterminal(NonterminalType::simple_stmt)) {
                    let simple_child = node.get_nth_child(0);
                    if simple_child.is_type(Nonterminal(NonterminalType::assignment)) {
                        self.cache_assignment_nodes(simple_child);
                    } else if simple_child.is_type(Nonterminal(NonterminalType::import_from)) {
                        if self.file.get_point(name.index).is_calculated() {
                            todo!("Multi name");
                        }
                        self.cache_import_from(simple_child);
                    } else if simple_child.is_type(Nonterminal(NonterminalType::import_name)) {
                        todo!();
                    } else {
                        unreachable!("Found type {:?}", simple_child.get_type());
                    }
                }
            }
        } else {
            unreachable!("Found type {:?}", child.get_type());
        }
    }

    fn cache_import_from(&self, imp: PyNode<'a>) {
        // | "from" ("." | "...")* dotted_name "import" import_from_targets
        // | "from" ("." | "...")+ "import" import_from_targets
        use NonterminalType::*;
        let mut level = 0;
        let mut inferred = None;
        for node in imp.iter_children() {
            if node.is_type(Nonterminal(dotted_name)) {
                if level > 0 {
                    todo!()
                }
                inferred = Some(self.infer_import_dotted_name(node));
            } else if node.is_type(Nonterminal(import_from_targets)) {
                if level > 0 {
                    todo!()
                }
                // import_from_targets:
                //     "*" | "(" ",".import_from_as_name+ ","? ")" | ",".import_from_as_name+
                for child in node.iter_children() {
                    if child.is_type(Nonterminal(import_from_as_name)) {
                        // import_from_as_name: Name "as" name_definition | name_definition
                        let from_as_name = child.get_nth_child(0);
                        if from_as_name.is_type(Nonterminal(name_definition)) {
                            if self.file.get_point(from_as_name.index + 1).is_calculated() {
                                todo!()
                            }
                            let i = inferred.as_ref().unwrap().run_on_value(|value| {
                                value.lookup(self.database, from_as_name.get_code())
                            });
                            i.save_redirect(self.file, from_as_name.index + 1);
                        } else {
                            todo!("from import as")
                        }
                    }
                }
            } else if node.get_code() == "." {
                level += 1;
            } else if node.get_code() == "..." {
                level += 3;
            }
        }
    }

    fn infer_import_dotted_name(&self, dotted: PyNode<'a>) -> Inferred<'a> {
        debug_assert_eq!(dotted.get_type(), Nonterminal(NonterminalType::dotted_name));
        // dotted_name: [dotted_name "."] Name
        let first = dotted.get_nth_child(0);
        if first.is_type(Terminal(TerminalType::Name)) {
            let file_index = global_import(self.database, first.get_code());
            let point = if let Some(file_index) = file_index {
                Point::new_file_reference(file_index, Locality::DirectExtern)
            } else {
                Point::new_missing_file()
            };
            Inferred::new_and_save(self.database, self.file, first, point)
        } else {
            let base = self.infer_import_dotted_name(first);
            let name = dotted.get_nth_child(2);
            todo!()
        }
    }

    fn cache_assignment_nodes(&self, assignment_node: PyNode<'a>) {
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
                    self.infer_star_expressions(expression_node)
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
                            let point = self.file.get_point(n.index);
                            if point.is_calculated() {
                                todo!("{:?} {:?} {:?}", self.file, point, n);
                            }
                            inferred.clone().save_redirect(self.file, n.index);
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

    pub fn infer_star_expressions(&self, node: PyNode<'a>) -> Inferred<'a> {
        debug_assert_eq!(
            node.get_type(),
            Nonterminal(NonterminalType::star_expressions)
        );

        let mut iter = node.iter_children();
        let expression = iter.next().unwrap();
        if iter.next().is_none() {
            if expression.is_type(Nonterminal(NonterminalType::expression)) {
                self.infer_expression(expression)
            } else {
                debug_assert_eq!(
                    node.get_type(),
                    Nonterminal(NonterminalType::star_expression)
                );
                todo!("Add error: can't use starred expression here");
            }
        } else {
            todo!("it's a tuple, cache that!")
        }
    }

    pub fn infer_named_expression(&self, node: PyNode<'a>) -> Inferred<'a> {
        // named_expression: name_definition ":=" expression | expression
        debug_assert_eq!(
            node.get_type(),
            Nonterminal(NonterminalType::named_expression)
        );
        let mut expr = node.get_nth_child(0);
        if !expr.is_type(Nonterminal(NonterminalType::expression)) {
            expr = node.get_nth_child(2);
        }
        self.infer_expression(expr)
    }

    fn infer_expression(&self, node: PyNode<'a>) -> Inferred<'a> {
        // disjunction ["if" disjunction "else" expression] | lambda
        debug_assert_eq!(node.get_type(), Nonterminal(NonterminalType::expression));
        if let Some(result) = self.check_point_cache(node) {
            return result;
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
        inferred.save_redirect(self.file, node.index)
    }

    fn infer_expression_part(&self, node: PyNode<'a>) -> Inferred<'a> {
        // Responsible for all
        use NonterminalType::*;
        match node.get_type() {
            Nonterminal(atom) => self.infer_atom(node),
            Nonterminal(primary) => self.infer_primary(node),
            _ => todo!("Did not handle {:?}", node),
        }
    }

    fn infer_primary(&self, node: PyNode<'a>) -> Inferred<'a> {
        //   primary "." Name
        // | primary "(" [arguments | comprehension] ")"
        // | primary "[" slices "]"
        // | atom
        debug_assert_eq!(node.get_type(), Nonterminal(primary));
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
            "." => base.run_on_value(|value| value.lookup(self.database, second.get_code())),
            "(" => base.run_on_value(|value| {
                debug!("Execute {}", value.get_name(),);
                value.execute(self.database, &Arguments::new(self.file, node, second))
            }),
            "[" => {
                todo!()
            }
            _ => unreachable!(),
        }
    }

    fn infer_atom(&self, node: PyNode<'a>) -> Inferred<'a> {
        use NonterminalType::*;
        debug_assert_eq!(node.get_type(), Nonterminal(atom));
        if let Some(result) = self.check_point_cache(node) {
            return result;
        }

        let mut iter = node.iter_children();
        let first = iter.next().unwrap();
        let specific_enum = match first.get_type() {
            Terminal(TerminalType::Name) => return self.infer_name_reference(first),
            Terminal(TerminalType::Number) => {
                let code = first.get_code();
                if code.contains('j') {
                    Specific::Complex
                } else if code.contains('.') {
                    Specific::Float
                } else {
                    Specific::Integer
                }
            }
            Nonterminal(strings) => {
                let code = first.get_nth_child(0).get_code();
                let mut is_byte = false;
                for byte in code.bytes() {
                    if byte == b'"' || byte == b'\'' {
                        break;
                    } else if byte == b'b' || byte == b'B' {
                        is_byte = true;
                        break;
                    }
                }
                if is_byte {
                    Specific::Bytes
                } else {
                    Specific::String
                }
            }
            PyNodeType::Keyword => match first.get_code() {
                "None" => Specific::None,
                "True" | "False" => Specific::Boolean,
                "..." => Specific::Ellipsis,
                "(" => {
                    let next_node = iter.next().unwrap();
                    match next_node.get_type() {
                        Nonterminal(tuple_content) => Specific::Tuple,
                        Nonterminal(yield_expr) => {
                            todo!("yield_expr");
                        }
                        Nonterminal(named_expression) => {
                            todo!("named_expression");
                        }
                        Nonterminal(comprehension) => Specific::ComprehensionGenerator,
                        PyNodeType::Keyword => {
                            debug_assert_eq!(next_node.get_code(), ")");
                            Specific::Tuple
                        }
                        _ => unreachable!(),
                    }
                }
                "[" => {
                    todo!("List literal")
                }
                "{" => match iter.next().unwrap().get_type() {
                    Nonterminal(dict_content) | Nonterminal(dict_comprehension) => {
                        todo!("dict literal")
                    }
                    Nonterminal(star_named_expression) | Nonterminal(comprehension) => {
                        todo!("set literal")
                    }
                    _ => unreachable!(),
                },
                _ => unreachable!(),
            },
            _ => unreachable!(),
        };
        let point = Point::new_simple_language_specific(specific_enum, Locality::Stmt);
        Inferred::new_and_save(self.database, self.file, node, point)
    }

    fn infer_name_reference(&self, node: PyNode<'a>) -> Inferred<'a> {
        if let Some(result) = self.check_point_cache(node) {
            return result;
        }
        todo!("star import? {:?}", node)
    }

    #[inline]
    fn check_point_cache(&self, node: PyNode<'a>) -> Option<Inferred<'a>> {
        let point = self.file.get_point(node.index);
        if point.is_calculated() {
            debug!(
                "Infer {:?} ({}, {}) from cache: {}",
                get_node_debug_output(node),
                self.file.get_file_index(),
                node.index,
                if matches!(point.get_type(), PointType::LanguageSpecific) {
                    format!("{:?}", point.get_language_specific())
                } else {
                    format!("{:?}", point.get_type())
                },
            );
            match point.get_type() {
                PointType::Redirect => {
                    let file_index = point.get_file_index();
                    if file_index == self.file_index {
                        self.follow_redirects_in_point_cache(point.get_node_index())
                    } else {
                        self.database
                            .get_loaded_python_file(file_index)
                            .get_inference(self.database)
                            .follow_redirects_in_point_cache(point.get_node_index())
                    }
                }
                PointType::LanguageSpecific => match point.get_language_specific() {
                    Specific::LazyInferredFunction => {
                        let func = node.get_parent().unwrap().get_parent().unwrap();
                        debug_assert_eq!(
                            func.get_type(),
                            Nonterminal(NonterminalType::function_def)
                        );
                        self.file.calculate_node_scope_definitions(func);
                        debug_assert!(self.file.get_point(node.index).is_calculated());
                        self.check_point_cache(node)
                    }
                    _ => Some(Inferred::new_saved(self.database, self.file, node, point)),
                },
                PointType::Complex => {
                    Some(Inferred::new_saved(self.database, self.file, node, point))
                }
                PointType::NodeAnalysis => {
                    panic!("Invalid state, should not happen {:?}", node);
                }
                _ => {
                    todo!("{:?} {:?}", point.get_type(), node)
                }
            }
        } else {
            if point.is_calculating() {
                todo!("Set recursion error and return that");
            }
            None
        }
    }

    fn follow_redirects_in_point_cache(&self, node_index: NodeIndex) -> Option<Inferred<'a>> {
        let node = self.file.tree.get_node_by_index(node_index);
        self.check_point_cache(node).or_else(|| {
            if node.is_type(Terminal(TerminalType::Name)) {
                Some(self.infer_name(node))
            } else {
                todo!("{:?}, {:?}", self.file.get_file_index().0, node_index)
            }
        })
    }

    fn infer_name(&self, node: PyNode<'a>) -> Inferred<'a> {
        // TODO move this after debug_assert_eq???
        if let Some(result) = self.check_point_cache(node) {
            return result;
        }
        debug_assert_eq!(
            node.get_type(),
            Terminal(TerminalType::Name),
            "Node Id: {}",
            node.index
        );
        let stmt = node
            .get_parent_until(&[
                Nonterminal(NonterminalType::lambda),
                Nonterminal(NonterminalType::comprehension),
                Nonterminal(NonterminalType::dict_comprehension),
                Nonterminal(NonterminalType::stmt),
            ])
            .expect("There should always be a stmt");

        if !self.file.get_point(stmt.index).is_calculated() {
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
        debug_assert!(self.file.get_point(node.index).is_calculated());
        self.infer_name(node)
    }
}

fn is_name_reference(name: PyNode) -> bool {
    debug_assert_eq!(name.get_type(), Terminal(TerminalType::Name));
    !name
        .get_parent()
        .unwrap()
        .is_type(Nonterminal(NonterminalType::name_definition))
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
            Self::Tuple(TargetIterator {
                siblings: node.iter_children(),
            })
        }
    }
}

struct TargetIterator<'a> {
    siblings: SiblingIterator<'a>,
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

fn get_node_debug_output(node: PyNode) -> &str {
    node.get_code().get(..20).unwrap_or_else(|| node.get_code())
}
