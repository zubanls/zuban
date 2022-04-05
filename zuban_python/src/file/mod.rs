mod annotation;
mod diagnostics;
mod utils;

use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::fmt;
use std::rc::Rc;

use parsa_python_ast::*;

use crate::arguments::SimpleArguments;
use crate::database::{
    ComplexPoint, Database, DbType, FileIndex, FormatStyle, GenericsList, Locality, LocalityLink,
    Point, PointType, Points, Specific, TupleContent, TypeAlias, TypeVar, TypeVarUsage,
};
use crate::debug;
use crate::diagnostics::{Diagnostic, DiagnosticConfig, Issue, IssueType};
pub use crate::file::annotation::TypeComputation;
use crate::file_state::{File, Leaf};
use crate::getitem::SliceType;
use crate::imports::global_import;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::lines::NewlineIndices;
use crate::name::{Names, TreeName, TreePosition};
use crate::name_binder::{NameBinder, NameBinderType};
use crate::node_ref::NodeRef;
use crate::utils::{debug_indent, InsertOnlyVec, SymbolTable};
use crate::value::{Function, Module, Value};
use crate::workspaces::DirContent;

#[derive(Default, Debug)]
pub struct ComplexValues(InsertOnlyVec<ComplexPoint>);

impl ComplexValues {
    pub fn get(&self, index: usize) -> &ComplexPoint {
        &self.0[index]
    }

    pub fn get_by_node_index(&self, points: &Points, node_index: NodeIndex) -> &ComplexPoint {
        &self.0[points.get(node_index).complex_index()]
    }

    pub fn insert(
        &self,
        points: &Points,
        node_index: NodeIndex,
        complex: ComplexPoint,
        locality: Locality,
    ) {
        let complex_index = self.0.len() as u32;
        self.0.push(Box::pin(complex));
        points.set(
            node_index,
            Point::new_complex_point(complex_index, locality),
        );
    }
}

impl File for PythonFile {
    fn ensure_initialized(&self) {
        if self.points.get(0).calculated() {
            // It was already done.
            return;
        }
        self.with_global_binder(|binder| binder.index_file(self.tree.root()));

        self.points.set(0, Point::new_node_analysis(Locality::File));
    }

    fn implementation<'db>(&self, names: Names<'db>) -> Names<'db> {
        todo!()
    }

    fn leaf<'db>(&'db self, database: &'db Database, position: CodeIndex) -> Leaf<'db> {
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
                return self.inference(&mut i_s).infer_primary(primary);
            }
        }
        todo!()
    }

    fn file_index(&self) -> FileIndex {
        self.file_index.get().unwrap()
    }

    fn set_file_index(&self, index: FileIndex) {
        self.file_index.set(Some(index));
    }

    fn node_start_position(&self, n: NodeIndex) -> TreePosition {
        TreePosition::new(self, self.tree.node_start_position(n))
    }

    fn node_end_position(&self, n: NodeIndex) -> TreePosition {
        TreePosition::new(self, self.tree.node_end_position(n))
    }

    fn line_column_to_byte(&self, line: usize, column: usize) -> CodeIndex {
        self.newline_indices
            .line_column_to_byte(self.tree.code(), line, column)
    }

    fn byte_to_line_column(&self, byte: CodeIndex) -> (usize, usize) {
        self.newline_indices
            .byte_to_line_column(self.tree.code(), byte)
    }

    fn diagnostics<'db>(
        &'db self,
        db: &'db Database,
        config: &DiagnosticConfig,
    ) -> Box<[Diagnostic<'db>]> {
        let mut i_s = InferenceState::new(db);
        self.inference(&mut i_s).calculate_diagnostics();
        let mut vec: Vec<_> = unsafe {
            self.issues
                .iter()
                .filter(|i| config.should_be_reported(&i.type_))
                .map(|i| Diagnostic::new(db, self, i))
                .collect()
        };
        vec.sort_by_key(|diag| diag.issue.node_index);
        vec.into_boxed_slice()
    }

    fn invalidate_references_to(&mut self, file_index: FileIndex) {
        self.points.invalidate_references_to(file_index);
        self.issues.as_vec_mut().clear();
    }
}

pub struct PythonFile {
    pub tree: Tree, // TODO should probably not be public
    pub symbol_table: SymbolTable,
    //all_names_bloom_filter: Option<BloomFilter<&str>>,
    pub points: Points,
    pub complex_points: ComplexValues,
    file_index: Cell<Option<FileIndex>>,
    pub issues: InsertOnlyVec<Issue>,
    pub star_imports: Vec<FileIndex>,
    pub package_dir: Option<Rc<DirContent>>,
    sub_files: RefCell<HashMap<CodeIndex, FileIndex>>,

    newline_indices: NewlineIndices,
}

impl fmt::Debug for PythonFile {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("PythonFile")
            .field("file_index", &self.file_index.get())
            .finish()
    }
}

impl<'db> PythonFile {
    pub fn new(package_dir: Option<Rc<DirContent>>, code: String) -> Self {
        let tree = Tree::parse(code);
        let length = tree.length();
        Self {
            tree,
            file_index: Cell::new(None),
            symbol_table: Default::default(),
            points: Points::new(length),
            complex_points: Default::default(),
            star_imports: Default::default(),
            issues: Default::default(),
            newline_indices: NewlineIndices::new(),
            sub_files: Default::default(),
            package_dir,
        }
    }

    fn with_global_binder(&'db self, func: impl FnOnce(&mut NameBinder<'db, 'db>)) {
        NameBinder::with_global_binder(
            &self.tree,
            &self.symbol_table,
            &self.points,
            &self.complex_points,
            &self.issues,
            self.file_index.get().unwrap(),
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
        todo!("This function is currently unused, but might be useful again later")
    }

    pub fn inference<'a, 'b>(
        &'db self,
        i_s: &'b mut InferenceState<'db, 'a>,
    ) -> PythonInference<'db, 'a, 'b> {
        PythonInference {
            file: self,
            file_index: self.file_index(),
            i_s,
        }
    }

    pub fn lookup_global(&self, name: &str) -> Option<LocalityLink> {
        self.symbol_table
            .lookup_symbol(name)
            .map(|node_index| LocalityLink {
                file: self.file_index(),
                node_index,
                locality: Locality::Todo,
            })
    }

    fn new_annotation_file(
        &'db self,
        db: &'db Database,
        start: CodeIndex,
        code: String,
    ) -> &'db Self {
        // TODO should probably not need a newline
        let mut file = PythonFile::new(None, code + "\n");
        file.star_imports.push(self.file_index());
        // TODO just saving this in the cache and forgetting about it is a bad idea
        let f = db.load_sub_file(file);
        self.sub_files.borrow_mut().insert(start, f.file_index());
        f
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
                        "{} {:?} (#{}, {}, {}) from cache: {}",
                        stringify!($name),
                        node.short_debug(),
                        self.file.byte_to_line_column(node.start()).0,
                        self.file.file_index(),
                        node.index(),
                        {
                            let point = self.file.points.get(node.index());
                            if matches!(point.type_(), PointType::Specific) {
                                format!("{:?}", point.specific())
                            } else {
                                format!("{:?}", point.type_())
                            }
                        },
                    );
                    inferred
                } else {
                    debug!(
                        "{} {:?} (#{}, {}, {})",
                        stringify!($name),
                        node.short_debug(),
                        self.file.byte_to_line_column(node.start()).0,
                        self.file.file_index(),
                        node.index(),
                    );
                    $func(self, node)
                }
            })
        }
    }
}

impl<'db, 'a, 'b> PythonInference<'db, 'a, 'b> {
    fn cache_stmt_name(&mut self, stmt: Stmt<'db>) {
        debug!(
            "Infer stmt (#{}: {}, {}): {:?}",
            self.file.byte_to_line_column(stmt.start()).0,
            self.file.file_index(),
            stmt.index(),
            stmt.short_debug().trim()
        );
        match stmt.unpack() {
            StmtContent::SimpleStmts(simple_stmts) => {
                for simple_stmt in simple_stmts.iter() {
                    match simple_stmt.unpack() {
                        SimpleStmtContent::Assignment(assignment) => {
                            self.cache_assignment_nodes(assignment);
                        }
                        SimpleStmtContent::ImportFrom(import_from) => {
                            self.cache_import_from(import_from);
                        }
                        SimpleStmtContent::ImportName(import_name) => {
                            self.cache_import_name(import_name);
                        }
                        _ => unreachable!("Found {:?}", simple_stmt),
                    }
                }
            }
            StmtContent::ForStmt(for_stmt) => {
                let (star_targets, star_exprs, _, _) = for_stmt.unpack();
                let element = self
                    .infer_star_expressions(star_exprs)
                    .iter(self.i_s, NodeRef::new(self.file, star_exprs.index()))
                    .infer_all(self.i_s);
                debug!("For loop input: {}", element.description(self.i_s));
                self.assign_targets(
                    star_targets.as_target(),
                    &element,
                    NodeRef::new(self.file, star_exprs.index()),
                )
            }
            _ => unreachable!("Found type {:?}", stmt.short_debug()),
        }
    }

    fn cache_import_name(&mut self, imp: ImportName<'db>) {
        if self.file.points.get(imp.index()).calculated() {
            return;
        }

        for dotted_as_name in imp.iter_dotted_as_names() {
            match dotted_as_name.unpack() {
                DottedAsNameContent::Simple(name_def, _) => {
                    let name = name_def.name();
                    self.global_import(name);
                }
                DottedAsNameContent::WithAs(dotted_name, as_name_def) => {
                    let inferred = self.infer_import_dotted_name(dotted_name);
                    debug_assert!(!self
                        .file
                        .points
                        .get(as_name_def.name().index())
                        .calculated());
                    inferred.save_redirect(self.file, as_name_def.name().index());
                }
            }
        }

        self.file
            .points
            .set(imp.index(), Point::new_node_analysis(Locality::Todo));
    }

    fn cache_import_from(&mut self, imp: ImportFrom<'db>) {
        if self.file.points.get(imp.index()).calculated() {
            return;
        }

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
                let import_file = inferred
                    .unwrap()
                    .as_file_index()
                    .map(|f| self.i_s.database.loaded_python_file(f));
                for target in targets {
                    let (import_name, name_def) = target.unpack();
                    let name = import_name.unwrap_or_else(|| name_def.name());

                    let point = if let Some(import_file) = import_file {
                        let module = Module::new(self.i_s.database, import_file);

                        if let Some(link) = import_file.lookup_global(name.as_str()) {
                            debug_assert!(
                                link.file != self.file_index || link.node_index != name.index()
                            );
                            link.into_point_redirect()
                        } else if let Some(Some(file_index)) = import_file
                            .package_dir
                            .as_ref()
                            .map(|dir| module.sub_module(self.i_s.database, name.as_str()))
                        {
                            self.i_s
                                .database
                                .add_invalidates(file_index, self.file.file_index());
                            Point::new_file_reference(file_index, Locality::Todo)
                        } else {
                            NodeRef::new(self.file, name.index()).add_typing_issue(
                                self.i_s.database,
                                IssueType::AttributeError(
                                    format!("Module {:?}", module.name()),
                                    name.as_str().to_owned(),
                                ),
                            );
                            Point::new_unknown(import_file.file_index(), Locality::Todo)
                        }
                    } else {
                        Point::new_unknown(self.file.file_index(), Locality::Todo)
                    };
                    if let Some(import_name) = import_name {
                        self.file.points.set_on_name(&import_name, point);
                    }
                    self.file.points.set_on_name(&name_def.name(), point);
                }
            }
        }
        self.file
            .points
            .set(imp.index(), Point::new_node_analysis(Locality::Todo));
    }

    fn global_import(&self, name: Name<'db>) -> Inferred<'db> {
        let file_index = global_import(self.i_s.database, self.file.file_index(), name.as_str());
        let point = if let Some(file_index) = file_index {
            self.i_s
                .database
                .add_invalidates(file_index, self.file.file_index());
            debug!(
                "Global import {:?}: {:?}",
                name.as_str(),
                self.i_s.database.file_path(file_index)
            );
            Point::new_file_reference(file_index, Locality::DirectExtern)
        } else {
            let node_ref = NodeRef::new(self.file, name.index());
            node_ref.add_typing_issue(
                self.i_s.database,
                IssueType::ModuleNotFound(name.as_str().to_owned()),
            );
            Point::new_unknown(self.file.file_index(), Locality::Todo)
        };
        Inferred::new_and_save(self.file, name.index(), point)
    }

    fn infer_import_dotted_name(&mut self, dotted: DottedName<'db>) -> Inferred<'db> {
        match dotted.unpack() {
            DottedNameContent::Name(name) => self.global_import(name),
            DottedNameContent::DottedName(dotted_name, name) => {
                let base = self.infer_import_dotted_name(dotted_name);
                base.run_on_value(self.i_s, &mut |i_s, value| match value.as_module() {
                    Some(module) => module
                        .sub_module(i_s.database, name.as_str())
                        .map(Inferred::new_file_reference)
                        .unwrap_or_else(Inferred::new_unknown),
                    None => unreachable!(),
                })
            }
        }
    }

    fn cache_assignment_nodes(&mut self, assignment: Assignment<'db>) {
        if self.file.points.get(assignment.index()).calculated() {
            return;
        }
        match assignment.unpack() {
            AssignmentContent::Normal(targets, right_side) => {
                let suffix = assignment.suffix();
                let right = if let Some(start) = suffix.find("# type: ") {
                    let s = &suffix[start + "# type: ".len()..];
                    if s == "ignore" {
                        self.infer_assignment_right_side(right_side)
                    } else {
                        let g = self.compute_type_comment(
                            assignment.end() + "# type: ".len() as CodeIndex,
                            s.to_owned(),
                        );
                        Inferred::execute_db_type(self.i_s, g)
                    }
                } else {
                    self.infer_assignment_right_side(right_side)
                };
                for target in targets {
                    self.assign_targets(target, &right, NodeRef::new(self.file, assignment.index()))
                }
            }
            AssignmentContent::WithAnnotation(target, annotation, right_side) => {
                if let Some(right_side) = right_side {
                    let right = self.infer_assignment_right_side(right_side);
                    self.annotation_type(annotation).error_if_not_matches(
                        self.i_s,
                        &right,
                        |t1, t2| {
                            NodeRef::new(self.file, annotation.index()).add_typing_issue(
                                self.i_s.database,
                                IssueType::IncompatibleAssignment(t1, t2),
                            );
                        },
                    )
                }
                let inf_annot = self.compute_annotation(annotation);
                self.assign_single_target(target, &inf_annot, |index| {
                    self.file.points.set(
                        index,
                        Point::new_redirect(
                            self.file.file_index(),
                            annotation.index(),
                            Locality::Todo,
                        ),
                    );
                })
            }
            AssignmentContent::AugAssign(target, aug_assign, right_side) => {
                let right = self.infer_assignment_right_side(right_side);
                todo!()
            }
        }
        self.file
            .points
            .set(assignment.index(), Point::new_node_analysis(Locality::Todo));
    }

    fn infer_assignment_right_side(&mut self, right: AssignmentRightSide<'db>) -> Inferred<'db> {
        match right {
            AssignmentRightSide::StarExpressions(star_exprs) => {
                self.infer_star_expressions(star_exprs)
            }
            AssignmentRightSide::YieldExpr(yield_expr) => match yield_expr.unpack() {
                YieldExprContent::StarExpressions(s) => todo!(),
                YieldExprContent::YieldFrom(y) => todo!(),
            },
        }
    }

    fn assign_single_target(
        &mut self,
        target: Target<'db>,
        value: &Inferred<'db>,
        save: impl Fn(NodeIndex),
    ) {
        match target {
            Target::Name(n) => {
                let point = self.file.points.get(n.index());
                if point.calculated() {
                    // Save on name_definition
                    debug_assert_eq!(point.type_(), PointType::MultiDefinition);
                    let mut first_definition = point.node_index();
                    loop {
                        let point = self.file.points.get(first_definition);
                        if point.type_() == PointType::MultiDefinition {
                            first_definition = point.node_index();
                        } else {
                            break;
                        }
                    }
                    if let Some(inferred) = self.check_point_cache(first_definition) {
                        inferred.class_as_type(self.i_s).error_if_not_matches(
                            self.i_s,
                            value,
                            |t1, t2| {
                                NodeRef::new(self.file, n.index()).add_typing_issue(
                                    self.i_s.database,
                                    IssueType::IncompatibleAssignment(t1, t2),
                                );
                            },
                        );
                    }
                    save(n.index() - 1);
                } else {
                    save(n.index());
                }
            }
            Target::NameExpression(primary_target, name_node) => {
                if primary_target.as_code().contains("self") {
                    // TODO here we should do something as well.
                } else {
                    self.infer_primary_target(primary_target)
                        .class_as_type(self.i_s)
                        .error_if_not_matches(self.i_s, value, |t1, t2| {
                            NodeRef::new(self.file, primary_target.index()).add_typing_issue(
                                self.i_s.database,
                                IssueType::IncompatibleAssignment(t1, t2),
                            );
                        });
                }
                save(name_node.index()); // TODO why is this needed? document!
            }
            Target::IndexExpression(n) => {
                todo!("{:?}", n);
            }
            Target::Tuple(_) | Target::Starred(_) => unreachable!(),
        }
    }

    fn assign_targets(
        &mut self,
        target: Target<'db>,
        value: &Inferred<'db>,
        value_node_ref: NodeRef<'db>,
    ) {
        match target {
            Target::Tuple(mut targets) => {
                let mut value_iterator = value.iter(self.i_s, value_node_ref);
                while let Some(target) = targets.next() {
                    if let Target::Starred(star_target) = target {
                        let (stars, normal) = targets.clone().remaining_stars_and_normal_count();
                        if stars > 0 {
                            todo!()
                        } else if let Some(len) = value_iterator.len() {
                            let fetch = len - normal;
                            let union = Inferred::gather_union(|callable| {
                                for _ in 0..(len - normal) {
                                    callable(value_iterator.next(self.i_s).unwrap());
                                }
                            });

                            let generic = union.class_as_type(self.i_s).into_db_type(self.i_s);
                            let list = Inferred::new_unsaved_complex(ComplexPoint::Instance(
                                self.i_s.database.python_state.list().as_link(),
                                Some(GenericsList::new(Box::new([generic]))),
                            ));
                            self.assign_targets(star_target.as_target(), &list, value_node_ref);
                        } else {
                            todo!()
                        }
                    } else if let Some(value) = value_iterator.next(self.i_s) {
                        self.assign_targets(target, &value, value_node_ref)
                    } else {
                        todo!()
                    }
                }
            }
            Target::Starred(n) => {
                todo!("Star tuple unpack");
            }
            _ => self.assign_single_target(target, value, |index| {
                value.clone().save_redirect(self.file, index);
            }),
        };
    }

    pub fn infer_star_expressions(&mut self, exprs: StarExpressions<'db>) -> Inferred<'db> {
        match exprs.unpack() {
            StarExpressionContent::Expression(expr) => {
                if true {
                    self.infer_expression(expr)
                } else {
                    // TODO use this somewhere
                    /*
                    debug!("Found {} type vars in {}", type_vars.len(), expr.as_code());
                    Inferred::new_unsaved_complex(ComplexPoint::TypeAlias(Box::new(TypeAlias {
                        type_vars: type_vars.into_boxed_slice(),
                        db_type: self.infer_expression(expr).as_db_type(self.i_s),
                    })))
                    */
                    todo!()
                }
            }
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
        let inferred = match expr.unpack() {
            ExpressionContent::ExpressionPart(n) => self.infer_expression_part(n),
            ExpressionContent::Lambda(_) => todo!(),
            ExpressionContent::Ternary(t) => {
                let (if_, condition, else_) = t.unpack();
                self.infer_expression_part(if_)
                    .union(self.infer_expression(else_))
            }
        };
        inferred.save_redirect(self.file, expr.index())
    }

    pub fn infer_expression_part(&mut self, node: ExpressionPart<'db>) -> Inferred<'db> {
        match node {
            ExpressionPart::Atom(atom) => self.infer_atom(atom),
            ExpressionPart::Primary(primary) => self.infer_primary(primary),
            ExpressionPart::BitwiseOr(bitwise_or) => {
                let (a, b) = bitwise_or.unpack();
                // TODO this should only merge in annotation contexts
                self.infer_expression_part(a)
                    .union(self.infer_expression_part(b))
            }
            _ => todo!("Not handled yet {:?}", node),
        }
    }

    check_point_cache_with!(pub infer_primary, Self::_infer_primary, Primary);
    fn _infer_primary(&mut self, primary: Primary<'db>) -> Inferred<'db> {
        let base = self.infer_primary_or_atom(primary.first());
        self.infer_primary_content(base, primary.index(), primary.second())
            .save_redirect(self.file, primary.index())
    }

    pub fn infer_primary_content(
        &mut self,
        base: Inferred<'db>,
        primary_index: NodeIndex,
        second: PrimaryContent<'db>,
    ) -> Inferred<'db> {
        match second {
            PrimaryContent::Attribute(name) => base.run_on_value(self.i_s, &mut |i_s, value| {
                debug!("Lookup {}.{}", value.name(), name.as_str());
                value.lookup(i_s, name.as_str(), NodeRef::new(self.file, primary_index))
            }),
            PrimaryContent::Execution(details) => {
                let f = self.file;
                base.run_on_value(self.i_s, &mut |i_s, value| {
                    debug!("Execute {}", value.name());
                    let x = i_s.current_execution.and_then(|x| x.1.as_execution(x.0));
                    value.execute(
                        i_s,
                        &SimpleArguments::new(
                            f,
                            primary_index,
                            details,
                            x.as_ref(),
                            value.as_class().cloned(),
                        ),
                    )
                })
            }
            PrimaryContent::GetItem(slice_type) => {
                let f = self.file;
                base.run_on_value(self.i_s, &mut |i_s, value| {
                    debug!("Get Item on {}", value.name());
                    let x = i_s.current_execution.and_then(|x| x.1.as_execution(x.0));
                    value.get_item(i_s, &SliceType::new(f, primary_index, slice_type))
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
                let mut iterator = s_o_b.iter().peekable();
                let specific = match iterator.peek().unwrap() {
                    StringOrByte::String(_) => Specific::String,
                    StringOrByte::Bytes(_) => Specific::Bytes,
                    StringOrByte::FString(f) => Specific::String,
                };
                for string_or_byte in iterator {
                    if let StringOrByte::FString(f) = string_or_byte {
                        self.calc_fstring_diagnostics(f)
                    }
                }
                specific
            }
            NoneLiteral => Specific::None,
            Boolean(_) => Specific::Boolean,
            Ellipsis => Specific::Ellipsis,
            List(_) => Specific::List,
            ListComprehension(_) => Specific::List,
            Dict(_) => Specific::Dict,
            DictComprehension(_) => todo!(),
            Set(set) => {
                if let Some(elements) = set.unpack() {
                    return Inferred::new_unsaved_complex(ComplexPoint::Instance(
                        self.i_s.database.python_state.builtins_point_link("set"),
                        Some(GenericsList::new(Box::new([
                            self.create_list_or_set_generics(elements)
                        ]))),
                    ))
                    .save_redirect(self.file, atom.index());
                } else {
                    todo!()
                }
            }
            SetComprehension(_) => todo!(),
            Tuple(tuple) => {
                let mut generics = vec![];
                for e in tuple.iter() {
                    match e {
                        StarLikeExpression::NamedExpression(e) => {
                            generics.push(self.infer_named_expression(e).class_as_db_type(self.i_s))
                        }
                        StarLikeExpression::StarNamedExpression(e) => {
                            let inferred = self.infer_expression_part(e.expression_part());
                            let mut iterator =
                                inferred.iter(self.i_s, NodeRef::new(self.file, e.index()));
                            if iterator.len().is_some() {
                                while let Some(inf) = iterator.next(self.i_s) {
                                    generics.push(inf.class_as_db_type(self.i_s))
                                }
                            } else {
                                todo!()
                            }
                        }
                    }
                }
                let content = TupleContent {
                    generics: (generics.len() != 0).then(|| GenericsList::from_vec(generics)),
                    arbitrary_length: false,
                };
                debug!(
                    "Inferred literal: Tuple{}",
                    content.as_string(self.i_s.database, FormatStyle::Short)
                );
                return Inferred::new_unsaved_complex(ComplexPoint::TypeInstance(Box::new(
                    DbType::Tuple(content),
                )))
                .save_redirect(self.file, atom.index());
            }
            GeneratorComprehension(_) => Specific::GeneratorComprehension,
            YieldExpr(_) => todo!(),
            NamedExpression(named_expression) => todo!(),
        };
        let point = Point::new_simple_specific(specific, Locality::Todo);
        Inferred::new_and_save(self.file, atom.index(), point)
    }

    fn infer_primary_target(&mut self, primary_target: PrimaryTarget<'db>) -> Inferred<'db> {
        let first = match primary_target.first() {
            PrimaryTargetOrAtom::Atom(atom) => self.infer_atom(atom),
            PrimaryTargetOrAtom::PrimaryTarget(p) => self.infer_primary_target(p),
        };
        self.infer_primary_content(first, primary_target.index(), primary_target.second())
    }

    check_point_cache_with!(pub infer_name_reference, Self::_infer_name_reference, Name);
    fn _infer_name_reference(&mut self, name: Name<'db>) -> Inferred<'db> {
        // If it's not inferred already through the name binder, it's either a star import, a
        // builtin or really missing.
        let point = if let Some(link) = self
            .i_s
            .database
            .python_state
            .builtins()
            .lookup_global(name.as_str())
        {
            debug_assert!(link.file != self.file_index || link.node_index != name.index());
            link.into_point_redirect()
        } else {
            let name_str = name.as_str();
            for index in &self.file.star_imports {
                let other_file = self.i_s.database.loaded_python_file(*index);

                if let Some(symbol) = other_file.symbol_table.lookup_symbol(name_str) {
                    self.file.points.set(
                        name.index(),
                        Point::new_redirect(other_file.file_index(), symbol, Locality::Todo),
                    );
                    return self.infer_name_reference(name);
                }
            }
            if let Some(symbol) = self.file.symbol_table.lookup_symbol(name_str) {
                // TODO mypy this is a issue AFAIK and this code should not be needed
                Point::new_redirect(self.file_index, symbol, Locality::Todo)
            } else if name_str == "reveal_type" {
                Point::new_simple_specific(Specific::RevealTypeFunction, Locality::Stmt)
            } else {
                // TODO check star imports
                NodeRef::new(self.file, name.index()).add_typing_issue(
                    self.i_s.database,
                    IssueType::NameError(name.as_str().to_owned()),
                );
                Point::new_unknown(self.file_index, Locality::Todo)
            }
        };
        self.file.points.set_on_name(&name, point);
        debug_assert!(self.file.points.get(name.index()).calculated());
        self.infer_name_reference(name)
    }

    fn check_point_cache(&mut self, node_index: NodeIndex) -> Option<Inferred<'db>> {
        let point = self.file.points.get(node_index);
        let result = point
            .calculated()
            .then(|| match point.type_() {
                PointType::Redirect => {
                    let file_index = point.file_index();
                    let node_index = point.node_index();
                    let infer = |inference: &mut PythonInference<'db, '_, '_>| {
                        let point = inference.file.points.get(point.node_index());
                        inference.check_point_cache(node_index).unwrap_or_else(|| {
                            let name = Name::maybe_by_index(&inference.file.tree, node_index);
                            if let Some(name) = name {
                                inference._infer_name(name)
                            } else if let Some(expr) =
                                Expression::maybe_by_index(&inference.file.tree, node_index)
                            {
                                inference._infer_expression(expr)
                            } else if let Some(annotation) =
                                Annotation::maybe_by_index(&inference.file.tree, node_index)
                            {
                                inference.compute_annotation(annotation)
                            } else {
                                todo!(
                                    "{}",
                                    NodeRef::new(inference.file, node_index)
                                        .debug_info(self.i_s.database)
                                )
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
                                .loaded_python_file(file_index)
                                .inference(self.i_s),
                        )
                    }
                }
                PointType::Specific => match point.specific() {
                    Specific::Param => {
                        let name = Name::by_index(&self.file.tree, node_index);
                        // Performance: This could be improved by not needing to lookup all the
                        // parents all the time.
                        if let FunctionOrLambda::Function(func) =
                            name.function_or_lambda_ancestor().unwrap()
                        {
                            let func = Function::new(
                                NodeRef::new(self.file, func.index()),
                                self.i_s.current_class,
                            );
                            func.calculated_type_vars(self.i_s);
                        }
                        if let Some(inferred) = self.use_cached_param_annotation(name) {
                            return inferred;
                        }
                        if let Some((function, args)) = self.i_s.current_execution {
                            function
                                .infer_param(self.i_s, node_index, args)
                                .resolve_function_return(self.i_s)
                        } else {
                            todo!()
                        }
                    }
                    Specific::LazyInferredFunction | Specific::LazyInferredClosure => {
                        todo!("Resolve decorators")
                    }
                    Specific::LazyInferredClass => {
                        // TODO this does not analyze decorators
                        let name = Name::by_index(&self.file.tree, node_index);
                        let class = name.expect_class_def();
                        // Avoid overwriting multi definitions
                        let mut name_index = name.index();
                        if self.file.points.get(name_index).type_() == PointType::MultiDefinition {
                            name_index = name.name_definition().unwrap().index();
                        }
                        self.file.points.set(
                            name_index,
                            Point::new_redirect(self.file_index, class.index(), Locality::Todo),
                        );
                        debug_assert!(self.file.points.get(node_index).calculated());
                        self.check_point_cache(node_index).unwrap()
                    }
                    _ => Inferred::new_saved(self.file, node_index, point),
                },
                PointType::MultiDefinition => {
                    let inferred =
                        self.infer_name(Name::by_index(&self.file.tree, point.node_index()));
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
                if point.calculating() {
                    todo!("Set recursion error and return that");
                }
                None
            });
        if cfg!(feature = "zuban_debug") {
            if let Some(inferred) = result.as_ref() {
                if inferred.is_unknown() {
                    debug!("Found unknown cache result: {}", node_index);
                }
            }
        }
        result
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

        if !self.file.points.get(stmt_like.index()).calculated() {
            match stmt_like {
                StmtLike::Stmt(stmt) => {
                    if name.is_reference() {
                        // References are not calculated by the name binder for star imports and
                        // lookups.
                        if let Some(primary) = name.maybe_primary_parent() {
                            return self.infer_primary(primary);
                        } else {
                            todo!(
                                "star import {} {:?} {:?}",
                                self.file.file_path(self.i_s.database),
                                name,
                                self.file.byte_to_line_column(name.start())
                            )
                        }
                    } else {
                        self.cache_stmt_name(stmt);
                    }
                }
                _ => todo!("{:?}", stmt_like),
            }
        }
        debug_assert!(
            self.file.points.get(name.index()).calculated(),
            "{:?}",
            name
        );
        if let PointType::MultiDefinition = self.file.points.get(name.index()).type_() {
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

    pub fn infer_module_name(&mut self, name: &str) -> Option<Inferred<'db>> {
        self.file
            .symbol_table
            .lookup_symbol(name)
            .map(|i| self.infer_name_by_index(i))
    }
}
