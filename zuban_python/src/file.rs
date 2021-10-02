use crate::arguments::SimpleArguments;
use crate::database::{
    ComplexPoint, Database, FileIndex, Locality, LocalityLink, Point, PointType, Specific,
};
use crate::debug;
use crate::file_state::{File, Issue, Leaf};
use crate::getitem::SliceType;
use crate::imports::global_import;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::name::{Names, TreeName};
use crate::name_binder::{NameBinder, NameBinderType};
use crate::utils::{debug_indent, InsertOnlyVec, SymbolTable};
use parsa_python::{
    NonterminalType, PyNode, PyNodeType, PyTree, SiblingIterator, TerminalType, PYTHON_GRAMMAR,
};
use parsa_python_ast::*;
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
    fn get_implementation<'db>(&self, names: Names<'db>) -> Names<'db> {
        todo!()
    }

    fn get_leaf<'db>(&'db self, database: &'db Database, position: CodeIndex) -> Leaf<'db> {
        fn calculate<'a>(
            file: &'a PythonFile,
            database: &'a Database,
            node: PyNode<'a>,
            position: CodeIndex,
        ) -> Leaf<'a> {
            match node.get_type() {
                Terminal(t) | ErrorTerminal(t) => match t {
                    TerminalType::Name => {
                        Leaf::Name(Box::new(TreeName::new(database, file, Name(node))))
                    }
                    _ => Leaf::None,
                },
                PyNodeType::ErrorKeyword | PyNodeType::Keyword => Leaf::Keyword(Keyword(node)),
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
    fn infer_operator_leaf<'db>(
        &'db self,
        database: &'db Database,
        leaf: Keyword<'db>,
    ) -> Inferred<'db> {
        if ["(", "[", "{", ")", "]", "}"]
            .iter()
            .any(|&x| x == leaf.as_str())
        {
            if let Some(primary) = leaf.maybe_primary_parent() {
                let mut i_s = InferenceState::new(database);
                return self.get_inference(&mut i_s).infer_primary(primary);
            }
        }
        todo!()
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
            &self.tree,
            &self.symbol_table,
            &self.points,
            &self.complex_points,
            self.file_index.get().unwrap(),
            None,
            func,
        )
    }

    fn calculate_node_scope_definitions(&self, node: PyNode<'db>) {
        let symbol_table = SymbolTable::default();
        self.with_global_binder(|binder| {
            binder.with_nested(NameBinderType::Function, &symbol_table, |b| {
                b.index_function_body(node)
            })
        });
    }

    pub fn get_inference<'a, 'b>(
        &'db self,
        i_s: &'b mut InferenceState<'db, 'a>,
    ) -> PythonInference<'db, 'a, 'b> {
        self.calculate_global_definitions_and_references();
        PythonInference {
            file: self,
            file_index: self.get_file_index(),
            i_s,
        }
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

pub struct PythonInference<'db, 'a, 'b> {
    file: &'db PythonFile,
    file_index: FileIndex,
    i_s: &'b mut InferenceState<'db, 'a>,
}

macro_rules! check_point_cache_with {
    ($vis:vis $name:ident, $func:path, $ast:ident) => {
        $vis fn $name(&mut self, node: $ast<'db>) -> $crate::inferred::Inferred<'db> {
            debug_indent(|| {
                let point = self.file.get_point(node.index());
                self.check_point_cache(
                    $func as fn (self_: &mut Self, Node: parsa_python::PyNode<'db>) -> Inferred<'db>,
                    point,
                    node
                )
            })
        }
    }
}

impl<'db, 'a, 'b> PythonInference<'db, 'a, 'b> {
    fn cache_stmt_name(&mut self, stmt: PyNode<'db>, name: PyNode<'db>) {
        debug!(
            "Infer stmt ({}, {}): {}",
            self.file.get_file_index(),
            stmt.index,
            stmt.get_code().chars().take(10).collect::<String>().trim()
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

    fn cache_import_from(&mut self, imp: PyNode<'db>) {
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
                            let i = inferred
                                .as_ref()
                                .unwrap()
                                .run_on_value(self.i_s, &|i_s, value| {
                                    value.lookup(i_s, from_as_name.get_code())
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

    fn infer_import_dotted_name(&mut self, dotted: PyNode<'db>) -> Inferred<'db> {
        debug_assert_eq!(dotted.get_type(), Nonterminal(NonterminalType::dotted_name));
        // dotted_name: [dotted_name "."] Name
        let first = dotted.get_nth_child(0);
        if first.is_type(Terminal(TerminalType::Name)) {
            let file_index = global_import(self.i_s.database, first.get_code());
            let point = if let Some(file_index) = file_index {
                Point::new_file_reference(file_index, Locality::DirectExtern)
            } else {
                Point::new_missing_file()
            };
            Inferred::new_and_save(self.file, first.index, point)
        } else {
            let base = self.infer_import_dotted_name(first);
            let name = dotted.get_nth_child(2);
            todo!()
        }
    }

    fn cache_assignment_nodes(&mut self, assignment_node: PyNode<'db>) {
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
                    self.infer_star_expressions(StarExpressions::new(expression_node))
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
                                // Save on name_definition
                                debug_assert_eq!(point.get_type(), PointType::MultiDefinition);
                                debug_assert_eq!(
                                    n.get_parent().unwrap().get_type(),
                                    Nonterminal(name_definition)
                                );
                                inferred.clone().save_redirect(self.file, n.index - 1);
                            } else {
                                inferred.clone().save_redirect(self.file, n.index);
                            }
                        }
                        Target::NameExpression(_, name_node) => {
                            inferred.clone().save_redirect(self.file, name_node.index);
                        }
                        Target::IndexExpression(n) => {
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

    pub fn infer_star_expressions(&mut self, exprs: StarExpressions<'db>) -> Inferred<'db> {
        match exprs.unpack() {
            StarExpressionContent::Expression(expr) => self.infer_expression(expr),
            StarExpressionContent::StarExpression(expr) => {
                todo!("Add error: can't use starred expression here")
            }
            StarExpressionContent::Tuple(expr) => todo!("it's a tuple, cache that!"),
        }
    }

    pub fn infer_named_expression(&mut self, node: PyNode<'db>) -> Inferred<'db> {
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

    check_point_cache_with!(pub infer_expression, Self::_infer_expression, Expression);
    fn _infer_expression(&mut self, node: Expression<'db>) -> Inferred<'db> {
        let mut iter = node.0.iter_children();
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

    pub fn infer_expression_part(&mut self, node: PyNode<'db>) -> Inferred<'db> {
        // Responsible for all
        use NonterminalType::*;
        match node.get_type() {
            Nonterminal(atom) => self.infer_atom(node),
            Nonterminal(primary) => self.infer_primary(Primary(node)),
            _ => todo!("Did not handle {:?}", node),
        }
    }

    fn infer_primary(&mut self, primary: Primary<'db>) -> Inferred<'db> {
        let base = match primary.first() {
            PrimaryOrAtom::Atom(atom) => self.infer_atom(atom),
            PrimaryOrAtom::Primary(primary) => self.infer_primary(primary),
        };
        match primary.second() {
            PrimaryContent::Attribute(name) => base.run_on_value(self.i_s, &|i_s, value| {
                debug!("Lookup {}.{}", value.get_name(), name.as_str());
                value.lookup(i_s, name.as_str())
            }),
            PrimaryContent::Execution(details) => {
                let f = self.file;
                base.run_on_value(self.i_s, &|i_s, value| {
                    debug!("Execute {}", value.get_name());
                    let x = i_s.current_execution.map(|x| x.1.as_execution(x.0));
                    value.execute(i_s, &SimpleArguments::new(f, primary, details, x.as_ref()))
                })
            }
            PrimaryContent::GetItem(slice_type) => {
                let f = self.file;
                base.run_on_value(self.i_s, &|i_s, value| {
                    debug!("Get Item {}", value.get_name());
                    let x = i_s.current_execution.map(|x| x.1.as_execution(x.0));
                    value.get_item(i_s, &SliceType::new(f, slice_type))
                })
            }
        }
    }

    check_point_cache_with!(infer_atom, Self::_infer_atom, Atom);
    fn _infer_atom(&mut self, atom: Atom<'db>) -> Inferred<'db> {
        use AtomContent::*;
        let specific = match atom.unpack() {
            Name(n) => return self.infer_name_reference(n),
            Int(_) => Specific::Integer,
            Float(_) => Specific::Float,
            Complex(_) => Specific::Complex,
            StringsOrBytes(s_o_b) => {
                if s_o_b.starts_with_string() {
                    Specific::String
                } else {
                    Specific::Bytes
                }
            }
            None => Specific::None,
            Boolean(_) => Specific::Boolean,
            Ellipsis => Specific::Ellipsis,
            List(_) => Specific::List,
            ListComprehension(_) => Specific::List,
            Dict(_) => todo!(),
            DictComprehension(_) => todo!(),
            Set(_) => todo!(),
            SetComprehension(_) => todo!(),
            Tuple(_) => Specific::Tuple,
            GeneratorComprehension(_) => Specific::GeneratorComprehension,
            YieldExpr(_) => todo!(),
            NamedExpression(named_expression) => todo!(),
        };
        let point = Point::new_simple_language_specific(specific, Locality::Stmt);
        Inferred::new_and_save(self.file, atom.index(), point)
    }

    check_point_cache_with!(infer_name_reference, Self::_infer_name_reference);
    fn _infer_name_reference(&mut self, name: Name<'db>) -> Inferred<'db> {
        todo!("star import? {:?}", name)
    }

    #[inline]
    fn check_point_cache(
        &mut self,
        callable: fn(&mut Self, PyNode<'db>) -> Inferred<'db>,
        point: Point,
        node_index: NodeIndex,
    ) -> Inferred<'db> {
        let point = self.file.get_point(node_index);
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
                    self.follow_redirects_in_point_cache(file_index, point.get_node_index())
                }
                PointType::LanguageSpecific => match point.get_language_specific() {
                    Specific::LazyInferredFunction => {
                        let func = node.get_parent().unwrap().get_parent().unwrap();
                        debug_assert_eq!(
                            func.get_type(),
                            Nonterminal(NonterminalType::function_def)
                        );
                        self.file.calculate_node_scope_definitions(func);
                        let point = self.file.get_point(node.index);
                        debug_assert!(point.is_calculated());
                        self.check_point_cache(callable, point, node)
                    }
                    _ => Inferred::new_saved(self.file, node.index, point),
                },
                PointType::MultiDefinition => {
                    let previous_node = self.file.tree.get_node_by_index(point.get_node_index());
                    let inferred = self.infer_name(previous_node);
                    // Check for the cache of name_definition
                    inferred.union(self.infer_multi_definition(node.get_parent().unwrap()))
                }
                PointType::Complex | PointType::MissingOrUnknown | PointType::FileReference => {
                    Inferred::new_saved(self.file, node.index, point)
                }
                PointType::NodeAnalysis => {
                    panic!("Invalid state, should not happen {:?}", node);
                }
            }
        } else {
            if point.is_calculating() {
                todo!("Set recursion error and return that");
            }
            callable(self, node)
        }
    }

    check_point_cache_with!(
        infer_multi_definition,
        Self::_infer_multi_definition,
        NameDefinition
    );
    fn _infer_multi_definition(&mut self, name_def: NameDefinition<'db>) -> Inferred<'db> {
        self._infer_name(name_def.name())
    }

    fn follow_redirects_in_point_cache(
        &mut self,
        file_index: FileIndex,
        node_index: NodeIndex,
    ) -> Inferred<'db> {
        if file_index != self.file_index {
            return self
                .i_s
                .database
                .get_loaded_python_file(file_index)
                .get_inference(self.i_s)
                .follow_redirects_in_point_cache(file_index, node_index);
        }
        let point = self.file.get_point(node_index);
        if point.is_calculated() {
            // This is just a shortcut to avoid fetching the node.
            if let PointType::Redirect = point.get_type() {
                return self.follow_redirects_in_point_cache(
                    point.get_file_index(),
                    point.get_node_index(),
                );
            }
        }
        let node = self.file.tree.get_node_by_index(node_index);
        self.check_point_cache(Self::infer_arbitrary_node, point, node)
    }

    fn infer_arbitrary_node(&mut self, node: PyNode<'db>) -> Inferred<'db> {
        if node.is_type(Terminal(TerminalType::Name)) {
            self.infer_name(node)
        } else {
            todo!("{:?}, {:?}", self.file.get_file_index().0, node)
        }
    }

    pub fn infer_name_by_index(&mut self, node_index: NodeIndex) -> Inferred<'db> {
        self.infer_name(Name::by_index(&self.file.tree, node_index))
    }

    check_point_cache_with!(pub infer_name, Self::_infer_name, Name);
    fn _infer_name(&mut self, name: Name<'db>) -> Inferred<'db> {
        let stmt = name
            .0
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
            if name.is_reference() {
                // References are not calculated by the name binder for star imports and lookups.
                let parent = name.0.get_parent().unwrap();
                if parent.is_type(Nonterminal(NonterminalType::primary)) {
                    return self.infer_primary(Primary(parent));
                } else {
                    dbg!(parent);
                    todo!("star import {:?}", name);
                }
            } else {
                self.cache_stmt_name(stmt, name.0);
            }
        }
        debug_assert!(self.file.get_point(name.index()).is_calculated());
        if let PointType::MultiDefinition = self.file.get_point(name.index()).get_type() {
            // We are trying to infer the name here. We don't have to follow the multi definition,
            // because the cache handling takes care of that.
            self.infer_multi_definition(name.0.get_parent().unwrap())
        } else {
            self.infer_name(name)
        }
    }
}

enum Target<'db> {
    Tuple(TargetIterator<'db>),
    Name(PyNode<'db>),
    NameExpression(PyNode<'db>, PyNode<'db>),
    IndexExpression(PyNode<'db>),
    Starred(PyNode<'db>),
}

impl<'db> Target<'db> {
    fn new(node: PyNode<'db>) -> Self {
        // star_targets: ",".star_target+ [","]
        let mut iterator = node.iter_children();
        let first = iterator.next().unwrap();
        if iterator.next().is_none() {
            if first.is_type(Nonterminal(NonterminalType::name_definition)) {
                Self::Name(first.get_nth_child(0))
            } else if first.is_type(Nonterminal(NonterminalType::t_primary)) {
                first
                    .iter_children()
                    .find(|x| x.is_type(Nonterminal(NonterminalType::name_definition)))
                    .map(|name_def| Self::NameExpression(first, name_def.get_nth_child(0)))
                    .unwrap_or_else(|| Self::IndexExpression(first))
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

struct TargetIterator<'db> {
    siblings: SiblingIterator<'db>,
}

impl<'db> Iterator for TargetIterator<'db> {
    type Item = Target<'db>;

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
