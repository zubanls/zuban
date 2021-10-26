use crate::arguments::SimpleArguments;
use crate::database::{
    ComplexPoint, Database, FileIndex, Locality, LocalityLink, Point, PointType, Points, Specific,
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
use parsa_python_ast::*;
use regex::Regex;
use std::cell::{Cell, UnsafeCell};
use std::fmt;

lazy_static::lazy_static! {
    static ref NEWLINES: Regex = Regex::new(r"\n|\r\n|\r").unwrap();
}

#[derive(Default)]
pub struct ComplexValues(InsertOnlyVec<ComplexPoint>);

impl ComplexValues {
    pub fn get(&self, index: usize) -> &ComplexPoint {
        self.0.get(index).unwrap()
    }

    pub fn insert(&self, points: &Points, node_index: NodeIndex, complex: ComplexPoint) {
        let complex_index = self.0.len() as u32;
        self.0.push(Box::pin(complex));
        points.set(
            node_index,
            Point::new_complex_point(complex_index, Locality::Stmt),
        );
    }
}

impl File for PythonFile {
    fn get_implementation<'db>(&self, names: Names<'db>) -> Names<'db> {
        todo!()
    }

    fn get_leaf<'db>(&'db self, database: &'db Database, position: CodeIndex) -> Leaf<'db> {
        match NameOrKeywordLookup::from_position(&self.tree, position) {
            NameOrKeywordLookup::Name(name) => {
                Leaf::Name(Box::new(TreeName::new(database, self, name)))
            }
            NameOrKeywordLookup::Keyword(keyword) => Leaf::Keyword(keyword),
            NameOrKeywordLookup::None => Leaf::None,
        }
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
    pub tree: Tree, // TODO should probably not be public
    pub symbol_table: SymbolTable,
    //all_names_bloom_filter: Option<BloomFilter<&str>>,
    pub points: Points,
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
        let tree = Tree::parse(code);
        let length = tree.length();
        Self {
            tree,
            file_index: Cell::new(None),
            symbol_table: Default::default(),
            points: Points::new(length),
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
            for m in NEWLINES.find_iter(self.tree.code()) {
                v.push(m.end() as CodeIndex);
            }
            *ptr = Some(v);
        }
        ptr.as_ref().unwrap()
    }

    pub fn calculate_global_definitions_and_references(&self) {
        if self.points.get(0).is_calculated() {
            // It was already done.
            return;
        }
        self.with_global_binder(|binder| binder.index_file(self.tree.root()));

        self.points.set(0, Point::new_node_analysis(Locality::File));
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

    fn calculate_function_scope_definitions(&self, func: FunctionDef<'db>) {
        let symbol_table = SymbolTable::default();
        self.with_global_binder(|binder| {
            binder.with_nested(NameBinderType::Function, &symbol_table, |b| {
                b.index_function_body(func)
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
                if let Some(inferred) = self.check_point_cache(node.index()) {
                    debug!(
                        "Infer {:?} ({}, {}) from cache: {}",
                        node.short_debug(),
                        self.file.get_file_index(),
                        node.index(),
                        {
                            let point = self.file.points.get(node.index());
                            if matches!(point.get_type(), PointType::LanguageSpecific) {
                                format!("{:?}", point.get_language_specific())
                            } else {
                                format!("{:?}", point.get_type())
                            }
                        },
                    );
                    inferred
                } else {
                    $func(self, node)
                }
            })
        }
    }
}

impl<'db, 'a, 'b> PythonInference<'db, 'a, 'b> {
    fn cache_stmt_name(&mut self, stmt: Stmt<'db>) {
        debug!(
            "Infer stmt ({}, {}): {}",
            self.file.get_file_index(),
            stmt.index(),
            stmt.short_debug().trim()
        );
        if let Some(simple_stmts) = stmt.as_simple_stmts() {
            for simple_stmt in simple_stmts.iter() {
                match simple_stmt.unpack() {
                    SimpleStmtContent::Assignment(assignment) => {
                        self.cache_assignment_nodes(assignment);
                    }
                    SimpleStmtContent::ImportFrom(import_from) => {
                        self.cache_import_from(import_from);
                    }
                    SimpleStmtContent::ImportName(import_from) => {
                        todo!()
                    }
                    _ => unreachable!("Found {:?}", simple_stmt),
                }
            }
        } else {
            unreachable!("Found type {:?}", stmt.short_debug());
        }
    }

    fn cache_import_from(&mut self, imp: ImportFrom<'db>) {
        let (level, dotted_name) = imp.level_with_dotted_name();
        let inferred = if level > 0 {
            todo!()
        } else {
            Some(self.infer_import_dotted_name(dotted_name.unwrap()))
        };

        match imp.unpack_targets() {
            ImportFromTargets::Star => (), // Nothing to do here, was calculated earlier
            ImportFromTargets::Iterator(targets) => {
                // as names should have been calculated earlier
                let import_file = self
                    .i_s
                    .database
                    .get_loaded_python_file(inferred.unwrap().as_file_index().unwrap());
                for target in targets {
                    let name = target.import_name();
                    let point = if let Some(link) = import_file.lookup_global(name.as_str()) {
                        debug_assert!(
                            link.file != self.file_index || link.node_index != name.index()
                        );
                        link.into_point_redirect()
                    } else {
                        // TODO star imports
                        Point::new_unknown(import_file.get_file_index(), Locality::DirectExtern)
                    };
                    self.file.points.set_on_name(&name, point);
                }
            }
        }
    }

    fn infer_import_dotted_name(&mut self, dotted: DottedName<'db>) -> Inferred<'db> {
        match dotted.unpack() {
            DottedNameContent::Name(name) => {
                let file_index = global_import(self.i_s.database, name.as_str());
                let point = if let Some(file_index) = file_index {
                    Point::new_file_reference(file_index, Locality::DirectExtern)
                } else {
                    Point::new_missing_file()
                };
                Inferred::new_and_save(self.file, name.index(), point)
            }
            DottedNameContent::DottedName(dotted_name, name) => {
                let base = self.infer_import_dotted_name(dotted_name);
                todo!()
            }
        }
    }

    fn cache_assignment_nodes(&mut self, assignment: Assignment<'db>) {
        match assignment.unpack() {
            AssignmentContent::Normal(targets, right_side) => {
                let right = self.infer_assignment_right_side(right_side);
                for target in targets {
                    self.assign_targets(target, &right)
                }
            }
            AssignmentContent::WithAnnotation(target, annotation, _) => {
                let right = self.infer_annotation_expression(annotation.expression());
                self.assign_targets(target, &right)
            }
            AssignmentContent::AugAssign(target, aug_assign, right_side) => {
                let right = self.infer_assignment_right_side(right_side);
                todo!()
            }
        }
    }

    fn infer_assignment_right_side(&mut self, right: AssignmentRightSide<'db>) -> Inferred<'db> {
        match right {
            AssignmentRightSide::StarExpressions(star_exprs) => {
                self.infer_star_expressions(star_exprs)
            }
            AssignmentRightSide::YieldExpr(yield_expr) => todo!(),
        }
    }

    fn assign_targets(&mut self, target: Target<'db>, value: &Inferred<'db>) {
        match target {
            Target::Tuple(target_iterator) => {
                todo!("Tuple unpack");
            }
            Target::Name(n) => {
                let point = self.file.points.get(n.index());
                if point.is_calculated() {
                    // Save on name_definition
                    debug_assert_eq!(point.get_type(), PointType::MultiDefinition);
                    value.clone().save_redirect(self.file, n.index() - 1);
                } else {
                    value.clone().save_redirect(self.file, n.index());
                }
            }
            Target::NameExpression(_, name_node) => {
                value.clone().save_redirect(self.file, name_node.index());
            }
            Target::IndexExpression(n) => {
                todo!("{:?}", n);
            }
            Target::Starred(n) => {
                todo!("Star tuple unpack");
            }
        };
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

    pub fn infer_named_expression(&mut self, named_expr: NamedExpression<'db>) -> Inferred<'db> {
        match named_expr.unpack() {
            NamedExpressionContent::Expression(expr)
            | NamedExpressionContent::Definition(_, expr) => self.infer_expression(expr),
        }
    }

    check_point_cache_with!(pub infer_expression, Self::_infer_expression, Expression);
    fn _infer_expression(&mut self, expr: Expression<'db>) -> Inferred<'db> {
        let inferred = self.infer_expression_no_save(expr);
        inferred.save_redirect(self.file, expr.index())
    }

    pub fn infer_expression_no_save(&mut self, expr: Expression<'db>) -> Inferred<'db> {
        match expr.unpack() {
            ExpressionContent::ExpressionPart(n) => self.infer_expression_part(n),
            ExpressionContent::Lambda(_) => todo!(),
            ExpressionContent::Ternary(_) => todo!(),
        }
    }

    pub fn infer_annotation_expression(&mut self, expr: Expression<'db>) -> Inferred<'db> {
        // Make sure that we're not working "inside" of a function/closure. Annotations are always
        // considered global and should not use params or local state.
        dbg!(&expr);
        let mut inf_state = self.i_s.with_annotation_instance();
        let mut inference = self.file.get_inference(&mut inf_state);
        let inferred = inference.infer_expression_no_save(expr);
        // TODO locality is wrong!!!!!1
        let point = if inferred.is_class(inference.i_s) {
            dbg!("X", expr);
            Point::new_simple_language_specific(Specific::AnnotationInstance, Locality::Stmt)
        } else {
            Point::new_unknown(self.file.get_file_index(), Locality::Stmt)
        };
        Inferred::new_and_save(self.file, expr.index(), point)
    }

    fn infer_expression_part(&mut self, node: ExpressionPart<'db>) -> Inferred<'db> {
        match node {
            ExpressionPart::Atom(atom) => self.infer_atom(atom),
            ExpressionPart::Primary(primary) => self.infer_primary(primary),
            _ => todo!("Not handled yet {:?}", node),
        }
    }

    pub fn infer_primary(&mut self, primary: Primary<'db>) -> Inferred<'db> {
        let base = self.infer_primary_or_atom(primary.first());
        match primary.second() {
            PrimaryContent::Attribute(name) => base.run_on_value(self.i_s, &mut |i_s, value| {
                debug!("Lookup {}.{}", value.get_name(), name.as_str());
                value.lookup(i_s, name.as_str())
            }),
            PrimaryContent::Execution(details) => {
                let f = self.file;
                base.run_on_value(self.i_s, &mut |i_s, value| {
                    debug!("Execute {}", value.get_name());
                    let x = i_s.current_execution.map(|x| x.1.as_execution(x.0));
                    value.execute(i_s, &SimpleArguments::new(f, primary, details, x.as_ref()))
                })
            }
            PrimaryContent::GetItem(slice_type) => {
                let f = self.file;
                base.run_on_value(self.i_s, &mut |i_s, value| {
                    debug!("Get Item {}", value.get_name());
                    let x = i_s.current_execution.map(|x| x.1.as_execution(x.0));
                    value.get_item(i_s, &SliceType::new(f, primary.index(), slice_type))
                })
            }
        }
    }

    pub fn infer_primary_or_atom(&mut self, p: PrimaryOrAtom<'db>) -> Inferred<'db> {
        match p {
            PrimaryOrAtom::Primary(primary) => self.infer_primary(primary),
            PrimaryOrAtom::Atom(atom) => self.infer_atom(atom),
        }
    }

    check_point_cache_with!(pub infer_atom, Self::_infer_atom, Atom);
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

    check_point_cache_with!(infer_name_reference, Self::_infer_name_reference, Name);
    fn _infer_name_reference(&mut self, name: Name<'db>) -> Inferred<'db> {
        // If it's not inferred already through the name binder, it's either a star import, a
        // builtin or really missing.
        let point = if let Some(link) = self
            .i_s
            .database
            .python_state
            .get_builtins()
            .lookup_global(name.as_str())
        {
            debug_assert!(link.file != self.file_index || link.node_index != name.index());
            link.into_point_redirect()
        } else {
            // TODO star imports
            Point::new_unknown(self.file_index, Locality::File)
        };
        self.file.points.set_on_name(&name, point);
        debug_assert!(self.file.points.get(name.index()).is_calculated());
        self.infer_name_reference(name)
    }

    fn check_point_cache(&mut self, node_index: NodeIndex) -> Option<Inferred<'db>> {
        let point = self.file.points.get(node_index);
        point
            .is_calculated()
            .then(|| match point.get_type() {
                PointType::Redirect => {
                    let file_index = point.get_file_index();
                    let node_index = point.get_node_index();
                    let infer = |inference: &mut PythonInference<'db, '_, '_>| {
                        let point = inference.file.points.get(point.get_node_index());
                        inference.check_point_cache(node_index).unwrap_or_else(|| {
                            let name = Name::maybe_by_index(&inference.file.tree, node_index);
                            if let Some(name) = name {
                                inference._infer_name(name)
                            } else {
                                todo!("{:?}, {:?}", inference.file.get_file_index().0, node_index)
                            }
                        })
                    };
                    if file_index == self.file_index {
                        infer(self)
                    } else {
                        infer(
                            &mut self
                                .i_s
                                .database
                                .get_loaded_python_file(file_index)
                                .get_inference(self.i_s),
                        )
                    }
                }
                PointType::LanguageSpecific => match point.get_language_specific() {
                    Specific::LazyInferredFunction => {
                        // TODO this does not analyze decorators
                        let name = Name::by_index(&self.file.tree, node_index);
                        let func = name.expect_function_def();
                        self.file.calculate_function_scope_definitions(func);
                        let point = self.file.points.get(node_index);
                        debug_assert!(point.is_calculated());
                        self.check_point_cache(node_index).unwrap()
                    }
                    Specific::LazyInferredClass => {
                        // TODO this does not analyze decorators
                        let name = Name::by_index(&self.file.tree, node_index);
                        let class = name.expect_class_def();
                        // Avoid overwriting multi definitions
                        let mut name_index = name.index();
                        if self.file.points.get(name_index).get_type() == PointType::MultiDefinition
                        {
                            name_index = name.name_definition().unwrap().index();
                        }
                        self.file.points.set(
                            name_index,
                            Point::new_redirect(self.file_index, class.index(), Locality::Stmt),
                        );
                        debug_assert!(self.file.points.get(node_index).is_calculated());
                        self.check_point_cache(node_index).unwrap()
                    }
                    _ => Inferred::new_saved(self.file, node_index, point),
                },
                PointType::MultiDefinition => {
                    let inferred =
                        self.infer_name(Name::by_index(&self.file.tree, point.get_node_index()));
                    // Check for the cache of name_definition
                    let name_def = NameDefinition::by_index(&self.file.tree, node_index - 1);
                    inferred.union(self.infer_multi_definition(name_def))
                }
                PointType::Complex | PointType::Unknown | PointType::FileReference => {
                    Inferred::new_saved(self.file, node_index, point)
                }
                PointType::NodeAnalysis => {
                    panic!("Invalid state, should not happen {:?}", node_index);
                }
            })
            .or_else(|| {
                if point.is_calculating() {
                    todo!("Set recursion error and return that");
                }
                None
            })
    }

    check_point_cache_with!(
        infer_multi_definition,
        Self::_infer_multi_definition,
        NameDefinition
    );
    fn _infer_multi_definition(&mut self, name_def: NameDefinition<'db>) -> Inferred<'db> {
        self._infer_name(name_def.name())
    }

    pub fn infer_name_by_index(&mut self, node_index: NodeIndex) -> Inferred<'db> {
        self.infer_name(Name::by_index(&self.file.tree, node_index))
    }

    check_point_cache_with!(pub infer_name, Self::_infer_name, Name);
    fn _infer_name(&mut self, name: Name<'db>) -> Inferred<'db> {
        let stmt_like = name.expect_stmt_like_ancestor();

        if !self.file.points.get(stmt_like.index()).is_calculated() {
            match stmt_like {
                StmtLike::Stmt(stmt) => {
                    if name.is_reference() {
                        // References are not calculated by the name binder for star imports and
                        // lookups.
                        if let Some(primary) = name.maybe_primary_parent() {
                            return self.infer_primary(primary);
                        } else {
                            todo!("star import {:?}", name);
                        }
                    } else {
                        self.cache_stmt_name(stmt);
                    }
                }
                _ => todo!("{:?}", stmt_like),
            }
        }
        debug_assert!(
            self.file.points.get(name.index()).is_calculated(),
            "{:?}",
            name
        );
        if let PointType::MultiDefinition = self.file.points.get(name.index()).get_type() {
            // We are trying to infer the name here. We don't have to follow the multi definition,
            // because the cache handling takes care of that.
            self.infer_multi_definition(name.name_definition().unwrap())
        } else {
            self.infer_name(name)
        }
    }

    pub fn infer_by_node_index(&mut self, node_index: NodeIndex) -> Inferred<'db> {
        self.check_point_cache(node_index)
            .unwrap_or_else(|| todo!())
    }
}
