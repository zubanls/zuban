mod class_type_var_finder;
mod diagnostics;
mod name_binder;
mod type_computation;
mod utils;

use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::fmt;
use std::rc::Rc;

use parsa_python_ast::*;

use crate::arguments::{Arguments, CombinedArguments, KnownArguments, SimpleArguments};
use crate::database::{
    ComplexPoint, Database, DbType, FileIndex, GenericItem, GenericsList, Locality, LocalityLink,
    Point, PointLink, PointType, Points, Specific, TupleContent, TypeVarLike,
};
use crate::debug;
use crate::diagnostics::{Diagnostic, DiagnosticConfig, Issue, IssueType};
use crate::file_state::{File, Leaf};
use crate::getitem::SliceType;
use crate::imports::{find_ancestor, global_import};
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::lines::NewlineIndices;
use crate::matching::{FormatData, ResultContext};
use crate::name::{Names, TreeName, TreePosition};
use crate::node_ref::NodeRef;
use crate::utils::{debug_indent, InsertOnlyVec, SymbolTable};
use crate::value::{Class, Function, LookupResult, Module, OnTypeError, ParamWithArgument, Value};
use crate::workspaces::DirContent;
pub use class_type_var_finder::ClassTypeVarFinder;
use name_binder::NameBinder;
use type_computation::type_computation_for_variable_annotation;
pub use type_computation::{
    BaseClass, TypeComputation, TypeComputationOrigin, TypeVarCallbackReturn,
};

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

    fn leaf<'db>(&'db self, db: &'db Database, position: CodeIndex) -> Leaf<'db> {
        match NameOrKeywordLookup::from_position(&self.tree, position) {
            NameOrKeywordLookup::Name(name) => Leaf::Name(Box::new(TreeName::new(db, self, name))),
            NameOrKeywordLookup::Keyword(keyword) => Leaf::Keyword(keyword),
            NameOrKeywordLookup::None => Leaf::None,
        }
    }

    fn infer_operator_leaf(&self, db: &Database, leaf: Keyword) -> Inferred {
        if ["(", "[", "{", ")", "]", "}"]
            .iter()
            .any(|&x| x == leaf.as_str())
        {
            if let Some(primary) = leaf.maybe_primary_parent() {
                let mut i_s = InferenceState::new(db);
                return self
                    .inference(&mut i_s)
                    .infer_primary(primary, &mut ResultContext::Unknown);
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
        if self.super_file.is_none() {
            // The main file is responsible for calculating diagnostics of type comments,
            // annotation strings, etc.
            self.inference(&mut i_s).calculate_diagnostics();
        }
        let mut vec: Vec<_> = unsafe {
            self.issues
                .iter()
                .filter(|i| config.should_be_reported(&i.type_))
                .map(|i| Diagnostic::new(db, self, i))
                .collect()
        };
        for (code_index, file_index) in self.sub_files.borrow().iter() {
            let file = db.loaded_python_file(*file_index);
            vec.extend(
                file.diagnostics(db, config)
                    .into_vec()
                    .into_iter()
                    .map(|d| d.wrap_subfile(self, *code_index)),
            );
        }
        vec.sort_by_key(|diag| diag.issue.node_index);
        vec.into_boxed_slice()
    }

    fn invalidate_references_to(&mut self, file_index: FileIndex) {
        self.points.invalidate_references_to(file_index);
        self.issues.as_vec_mut().clear();
    }
}

pub struct StarImport {
    scope: NodeIndex,
    import_from_node: NodeIndex,
    star_node: NodeIndex,
}

impl StarImport {
    #[inline]
    fn to_file<'db>(&self, inf: &mut PythonInference<'db, '_, '_, '_>) -> Option<&'db PythonFile> {
        let point = inf.file.points.get(self.star_node);
        if point.calculated() {
            return if point.type_() == PointType::Unknown {
                None
            } else {
                Some(inf.i_s.db.loaded_python_file(point.file_index()))
            };
        }
        let import_from = NodeRef::new(inf.file, self.import_from_node).expect_import_from();
        inf.cache_import_from(import_from);
        debug_assert!(inf.file.points.get(self.star_node).calculated());
        self.to_file(inf)
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
    pub star_imports: RefCell<Vec<StarImport>>,
    pub package_dir: Option<Rc<DirContent>>,
    sub_files: RefCell<HashMap<CodeIndex, FileIndex>>,
    pub(crate) super_file: Option<FileIndex>,

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
            super_file: None,
            package_dir,
        }
    }

    fn with_global_binder(&'db self, func: impl FnOnce(&mut NameBinder<'db, 'db>)) {
        NameBinder::with_global_binder(
            true,
            &self.tree,
            &self.symbol_table,
            &self.points,
            &self.complex_points,
            &self.issues,
            &self.star_imports,
            self.file_index.get().unwrap(),
            func,
        )
    }

    pub fn inference<'file, 'i_s, 'b>(
        &'file self,
        i_s: &'i_s mut InferenceState<'db, 'b>,
    ) -> PythonInference<'db, 'file, 'i_s, 'b> {
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
        &self,
        db: &'db Database,
        start: CodeIndex,
        code: String, // TODO this should not be a string, but probably cow
    ) -> &'db Self {
        // TODO should probably not need a newline
        let mut file = PythonFile::new(None, code + "\n");
        file.super_file = Some(self.file_index());
        // TODO just saving this in the cache and forgetting about it is a bad idea
        let f = db.load_sub_file(file);
        self.sub_files.borrow_mut().insert(start, f.file_index());
        f
    }

    pub fn is_stub(&self, db: &Database) -> bool {
        db.file_path(self.file_index()).ends_with(".pyi")
    }
}

pub struct PythonInference<'db: 'file, 'file, 'a, 'b> {
    file: &'file PythonFile,
    file_index: FileIndex,
    i_s: &'a mut InferenceState<'db, 'b>,
}

macro_rules! check_point_cache_with {
    ($vis:vis $name:ident, $func:path, $ast:ident $(, $result_context:ident )?) => {
        $vis fn $name(&mut self, node: $ast $(, $result_context : &mut ResultContext)?) -> $crate::inferred::Inferred {
            debug_indent(|| {
                if let Some(inferred) = self.check_point_cache(node.index()) {
                    debug!(
                        "{} {:?} (#{}, {}:{}) from cache: {}",
                        stringify!($name),
                        node.short_debug(),
                        self.file.byte_to_line_column(node.start()).0,
                        self.file.file_index(),
                        node.index(),
                        {
                            let point = self.file.points.get(node.index());
                            match point.type_() {
                                PointType::Specific => format!("{:?}", point.specific()),
                                PointType::Redirect => format!("Redirect {}:{}", point.file_index(), point.node_index()),
                                _ => format!("{:?}", point.type_()),
                            }
                        },
                    );
                    inferred
                } else {
                    debug!(
                        "{} {:?} (#{}, {}:{})",
                        stringify!($name),
                        node.short_debug(),
                        self.file.byte_to_line_column(node.start()).0,
                        self.file.file_index(),
                        node.index(),
                    );
                    $func(self, node $(, $result_context)?)
                }
            })
        }
    }
}

impl<'db, 'file, 'i_s, 'b> PythonInference<'db, 'file, 'i_s, 'b> {
    fn cache_simple_stmts_name(&mut self, simple_stmts: SimpleStmts, name_def: NodeRef) {
        debug!(
            "Infer stmt (#{}, {}:{}): {:?}",
            self.file.byte_to_line_column(simple_stmts.start()).0,
            self.file.file_index(),
            simple_stmts.index(),
            simple_stmts.short_debug().trim()
        );
        name_def.set_point(Point::new_calculating());
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
                _ => unreachable!("Found {simple_stmt:?}"),
            }
        }
    }

    fn cache_stmt_name(&mut self, stmt: Stmt, name_def: NodeRef) {
        debug!(
            "Infer stmt (#{}, {}:{}): {:?}",
            self.file.byte_to_line_column(stmt.start()).0,
            self.file.file_index(),
            stmt.index(),
            stmt.short_debug().trim()
        );
        name_def.set_point(Point::new_calculating());
        match stmt.unpack() {
            StmtContent::ForStmt(for_stmt) => {
                let (star_targets, star_exprs, _, _) = for_stmt.unpack();
                // Performance: We probably do not need to calculate diagnostics just for
                // calculating the names.
                self.cache_for_stmt_names(star_targets, star_exprs);
            }
            _ => unreachable!("Found type {:?}", stmt.short_debug()),
        }
    }

    fn cache_import_name(&mut self, imp: ImportName) {
        if self.file.points.get(imp.index()).calculated() {
            return;
        }

        for dotted_as_name in imp.iter_dotted_as_names() {
            match dotted_as_name.unpack() {
                DottedAsNameContent::Simple(name_def, _) => {
                    self.global_import(
                        name_def.as_code(),
                        name_def.index(),
                        Some(name_def.name_index()),
                    );
                }
                DottedAsNameContent::WithAs(dotted_name, as_name_def) => {
                    let file_index = self.infer_import_dotted_name(dotted_name, None);
                    debug_assert!(!self.file.points.get(as_name_def.index()).calculated());
                    let point = if let Some(file_index) = file_index {
                        Point::new_file_reference(file_index, Locality::Todo)
                    } else {
                        Point::new_unknown(self.file.file_index(), Locality::Todo)
                    };
                    self.file.points.set(as_name_def.index(), point);
                    self.file.points.set(as_name_def.name().index(), point);
                }
            }
        }

        self.file
            .points
            .set(imp.index(), Point::new_node_analysis(Locality::Todo));
    }

    fn cache_import_from(&mut self, imp: ImportFrom) {
        if self.file.points.get(imp.index()).calculated() {
            return;
        }

        let (level, dotted_name) = imp.level_with_dotted_name();
        let maybe_level_file = (level > 0)
            .then(|| {
                find_ancestor(self.i_s.db, self.file, level).or_else(|| {
                    NodeRef::new(self.file, imp.index())
                        .add_typing_issue(self.i_s.db, IssueType::NoParentModule);
                    None
                })
            })
            .flatten();
        let from_part_file_index = match dotted_name {
            Some(dotted_name) => self.infer_import_dotted_name(dotted_name, maybe_level_file),
            None => maybe_level_file,
        };

        match imp.unpack_targets() {
            ImportFromTargets::Star(keyword) => {
                // Nothing to do here, was calculated earlier
                let point = match from_part_file_index {
                    Some(file_index) => Point::new_file_reference(file_index, Locality::Todo),
                    None => Point::new_unknown(self.file.file_index(), Locality::Todo),
                };
                self.file.points.set(keyword.index(), point);
            }
            ImportFromTargets::Iterator(targets) => {
                // as names should have been calculated earlier
                let import_file = from_part_file_index.map(|f| self.i_s.db.loaded_python_file(f));
                for target in targets {
                    let (import_name, name_def) = target.unpack();

                    let point = if let Some(import_file) = import_file {
                        let module = Module::new(self.i_s.db, import_file);

                        if let Some(link) = import_file.lookup_global(import_name.as_str()) {
                            link.into_point_redirect()
                        } else if let Some(Some(file_index)) = import_file
                            .package_dir
                            .as_ref()
                            // TODO this dir is unused???
                            .map(|dir| module.sub_module(self.i_s.db, import_name.as_str()))
                        {
                            self.i_s
                                .db
                                .add_invalidates(file_index, self.file.file_index());
                            Point::new_file_reference(file_index, Locality::Todo)
                        } else if let Some(link) = import_file
                            .inference(self.i_s)
                            .lookup_from_star_import(import_name.as_str(), false)
                        {
                            Point::new_redirect(link.file, link.node_index, Locality::Todo)
                        } else {
                            NodeRef::new(self.file, import_name.index()).add_typing_issue(
                                self.i_s.db,
                                IssueType::ImportAttributeError {
                                    module_name: Box::from(module.name()),
                                    name: Box::from(import_name.as_str()),
                                },
                            );
                            Point::new_unknown(import_file.file_index(), Locality::Todo)
                        }
                    } else {
                        Point::new_unknown(self.file.file_index(), Locality::Todo)
                    };
                    self.file.points.set(import_name.index(), point);
                    self.file.points.set(name_def.index(), point);
                    self.file.points.set(name_def.name().index(), point);
                }
            }
        }
        self.file
            .points
            .set(imp.index(), Point::new_node_analysis(Locality::Todo));
    }

    fn global_import(
        &self,
        name: &str,
        index: NodeIndex,
        second_index: Option<NodeIndex>,
    ) -> Option<FileIndex> {
        let file_index = global_import(self.i_s.db, self.file.file_index(), name);
        let point = if let Some(file_index) = file_index {
            self.i_s
                .db
                .add_invalidates(file_index, self.file.file_index());
            debug!(
                "Global import {name:?}: {:?}",
                self.i_s.db.file_path(file_index)
            );
            Point::new_file_reference(file_index, Locality::DirectExtern)
        } else {
            let node_ref = NodeRef::new(self.file, index);
            node_ref.add_typing_issue(
                self.i_s.db,
                IssueType::ModuleNotFound {
                    module_name: Box::from(name),
                },
            );
            Point::new_unknown(self.file.file_index(), Locality::Todo)
        };
        self.file.points.set(index, point);
        if let Some(second_index) = second_index {
            self.file.points.set(second_index, point);
        }
        file_index
    }

    fn infer_import_dotted_name(
        &mut self,
        dotted: DottedName,
        base: Option<FileIndex>,
    ) -> Option<FileIndex> {
        let infer_name = |file_index, name: Name| {
            let file = self.i_s.db.loaded_python_file(file_index);
            let module = Module::new(self.i_s.db, file);
            let result = module.sub_module(self.i_s.db, name.as_str());
            if let Some(imported) = result {
                debug!(
                    "Imported {:?} for {:?}",
                    self.i_s
                        .db
                        .loaded_python_file(imported)
                        .file_path(self.i_s.db),
                    dotted.as_code(),
                );
            } else {
                let node_ref = NodeRef::new(self.file, name.index());
                node_ref.add_typing_issue(
                    self.i_s.db,
                    IssueType::ModuleNotFound {
                        module_name: format!("{}.{}", module.name().to_owned(), name.as_str())
                            .into(),
                    },
                );
            }
            result
        };
        match dotted.unpack() {
            DottedNameContent::Name(name) => {
                if let Some(base) = base {
                    infer_name(base, name)
                } else {
                    self.global_import(name.as_str(), name.index(), None)
                }
            }
            DottedNameContent::DottedName(dotted_name, name) => self
                .infer_import_dotted_name(dotted_name, base)
                .and_then(|file_index| infer_name(file_index, name)),
        }
    }

    fn original_definition(&mut self, assignment: Assignment) -> Option<Inferred> {
        // TODO shouldn't this be merged/using infer_single_target

        // TODO it's weird that we unpack assignments here again.
        if let AssignmentContent::Normal(targets, _) = assignment.unpack() {
            for target in targets {
                match target {
                    Target::Name(name_def) => {
                        let point = self.file.points.get(name_def.name_index());
                        if point.calculated() {
                            debug_assert_eq!(
                                point.type_(),
                                PointType::MultiDefinition,
                                "{target:?}"
                            );
                            let mut first_definition = point.node_index();
                            loop {
                                let point = self.file.points.get(first_definition);
                                if point.calculated() && point.type_() == PointType::MultiDefinition
                                {
                                    first_definition = point.node_index();
                                } else {
                                    break;
                                }
                            }
                            let inferred = self.infer_name_by_index(first_definition);
                            return Some(inferred);
                        }
                    }
                    Target::NameExpression(primary_target, name_def_node) => {
                        if let PrimaryTargetOrAtom::Atom(atom) = primary_target.first() {
                            // TODO this is completely wrong!!!
                            if atom.as_code() == "self" {
                                continue;
                            }
                        }
                        return Some(self.infer_primary_target(primary_target));
                    }
                    _ => (),
                }
            }
        }
        None
    }

    fn set_calculating_on_target(&mut self, target: Target) {
        match target {
            Target::Name(name_def) => {
                self.file
                    .points
                    .set(name_def.index(), Point::new_calculating());
            }
            Target::NameExpression(primary_target, name_def_node) => (),
            Target::IndexExpression(t) => (),
            Target::Tuple(targets) => {
                for target in targets {
                    self.set_calculating_on_target(target);
                }
            }
            Target::Starred(s) => self.set_calculating_on_target(s.as_target()),
        }
    }

    fn cache_assignment_nodes(&mut self, assignment: Assignment) {
        let node_ref = NodeRef::new(self.file, assignment.index());
        if node_ref.point().calculated() {
            return;
        }
        match assignment.unpack() {
            AssignmentContent::Normal(targets, right_side) => {
                for target in targets {
                    self.set_calculating_on_target(target);
                }
            }
            AssignmentContent::WithAnnotation(target, _, _) => {
                self.set_calculating_on_target(target)
            }
            AssignmentContent::AugAssign(target, aug_assign, right_side) => (),
        };
        match assignment.unpack() {
            AssignmentContent::Normal(targets, right_side) => {
                let suffix = assignment.suffix();
                const TYPE: &str = "# type: ";
                let mut type_comment_result = None;
                if let Some(start) = suffix.find(TYPE) {
                    let start = start + TYPE.len();
                    let s = &suffix[start..];
                    debug!("Infer type comment {s:?} on {:?}", assignment.as_code());
                    if s != "ignore" {
                        type_comment_result = Some(self.compute_type_comment(
                            assignment.end() + start as CodeIndex,
                            s,
                            node_ref,
                        ));
                    }
                }
                let is_definition = type_comment_result.is_some();
                let right = if let Some((r, type_)) = type_comment_result {
                    let right = self
                        .infer_assignment_right_side(right_side, &mut ResultContext::Known(&type_));
                    type_.error_if_not_matches(self.i_s, &right, |i_s, got, expected| {
                        node_ref.add_typing_issue(
                            i_s.db,
                            IssueType::IncompatibleAssignment { got, expected },
                        );
                    });
                    r
                } else {
                    let original_def = self.original_definition(assignment);
                    let result_type = original_def.as_ref().map(|inf| inf.class_as_type(self.i_s));
                    let mut result_context = match &result_type {
                        Some(t) => ResultContext::Known(t),
                        None => ResultContext::Unknown,
                    };
                    self.infer_assignment_right_side(right_side, &mut result_context)
                };
                for target in targets {
                    self.assign_targets(target, right.clone(), node_ref, is_definition)
                }
            }
            AssignmentContent::WithAnnotation(target, annotation, right_side) => {
                let mut x = type_computation_for_variable_annotation;
                let mut comp = TypeComputation::new(
                    self,
                    node_ref.as_link(),
                    Some(&mut x),
                    TypeComputationOrigin::TypeCommentOrAnnotation,
                );
                comp.compute_annotation(annotation);
                comp.into_type_vars(|inf, recalculate_type_vars| {
                    inf.recalculate_annotation_type_vars(annotation.index(), recalculate_type_vars);
                });
                if let Some(right_side) = right_side {
                    let t = self.use_cached_annotation_type(annotation);
                    let right =
                        self.infer_assignment_right_side(right_side, &mut ResultContext::Known(&t));
                    t.error_if_not_matches(self.i_s, &right, |i_s, got, expected| {
                        node_ref.add_typing_issue(
                            i_s.db,
                            IssueType::IncompatibleAssignment { got, expected },
                        );
                    });
                }
                let inf_annot = self.use_cached_annotation(annotation);
                self.assign_single_target(target, &inf_annot, true, |index| {
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
                let (inplace, normal, reverse) = aug_assign.magic_methods();
                let right =
                    self.infer_assignment_right_side(right_side, &mut ResultContext::Unknown);
                let left = self.infer_single_target(target);
                let result = left.run_on_value(self.i_s, &mut |i_s, value| {
                    value
                        .lookup_implicit(i_s, normal, &|i_s| todo!())
                        .run_on_value(i_s, &mut |i_s, v| {
                            v.execute(
                                i_s,
                                &KnownArguments::new(&right, Some(node_ref)),
                                &mut ResultContext::Unknown,
                                OnTypeError::new(
                                    &|i_s, node_ref, class, function, p, right, wanted| {
                                        node_ref.add_typing_issue(
                                            i_s.db,
                                            IssueType::UnsupportedOperand {
                                                operand: Box::from(aug_assign.operand()),
                                                left: class
                                                    .unwrap()
                                                    .format(&FormatData::new_short(i_s.db)),
                                                right,
                                            },
                                        )
                                    },
                                ),
                            )
                        })
                });
                if let AssignmentContent::AugAssign(target, _, _) = assignment.unpack() {
                    self.assign_single_target(target, &result, false, |index| {
                        // There is no need to save this, because it's never used
                    })
                } else {
                    unreachable!()
                }
            }
        }
        self.file
            .points
            .set(assignment.index(), Point::new_node_analysis(Locality::Todo));
    }

    fn infer_assignment_right_side(
        &mut self,
        right: AssignmentRightSide,
        result_context: &mut ResultContext,
    ) -> Inferred {
        match right {
            AssignmentRightSide::StarExpressions(star_exprs) => {
                self.infer_star_expressions(star_exprs, result_context)
            }
            AssignmentRightSide::YieldExpr(yield_expr) => match yield_expr.unpack() {
                YieldExprContent::StarExpressions(s) => todo!(),
                YieldExprContent::YieldFrom(y) => todo!(),
            },
        }
    }

    fn infer_single_target(&mut self, target: Target) -> Inferred {
        match target {
            Target::Name(name_def) => {
                todo!()
            }
            Target::NameExpression(primary_target, name_def_node) => {
                todo!()
            }
            Target::IndexExpression(t) => self.infer_primary_target(t),
            Target::Tuple(_) | Target::Starred(_) => unreachable!(),
        }
    }

    fn assign_single_target(
        &mut self,
        target: Target,
        value: &Inferred,
        is_definition: bool,
        save: impl Fn(NodeIndex),
    ) {
        match target {
            Target::Name(name_def) => {
                let point = self.file.points.get(name_def.name_index());
                if point.calculated() {
                    debug_assert_eq!(point.type_(), PointType::MultiDefinition, "{target:?}");
                    let mut first_definition = point.node_index();
                    loop {
                        let point = self.file.points.get(first_definition);
                        if point.calculated() && point.type_() == PointType::MultiDefinition {
                            first_definition = point.node_index();
                        } else {
                            break;
                        }
                    }
                    let inferred = self.infer_name_by_index(first_definition);
                    inferred.class_as_type(self.i_s).error_if_not_matches(
                        self.i_s,
                        value,
                        |i_s, got, expected| {
                            NodeRef::new(self.file, name_def.index()).add_typing_issue(
                                i_s.db,
                                IssueType::IncompatibleAssignment { got, expected },
                            );
                        },
                    );
                }
                save(name_def.index());
            }
            Target::NameExpression(primary_target, name_def_node) => {
                if primary_target.as_code().contains("self") {
                    // TODO here we should do something as well.
                } else {
                    if is_definition {
                        NodeRef::new(self.file, primary_target.index())
                            .add_typing_issue(self.i_s.db, IssueType::InvalidTypeDeclaration);
                    }
                    self.infer_primary_target(primary_target)
                        .class_as_type(self.i_s)
                        .error_if_not_matches(self.i_s, value, |i_s, got, expected| {
                            NodeRef::new(self.file, primary_target.index()).add_typing_issue(
                                self.i_s.db,
                                IssueType::IncompatibleAssignment { got, expected },
                            );
                        });
                }
                // This mostly needs to be saved for self names
                save(name_def_node.index());
            }
            Target::IndexExpression(primary_target) => {
                let base = match primary_target.first() {
                    PrimaryTargetOrAtom::Atom(atom) => {
                        self.infer_atom(atom, &mut ResultContext::Unknown)
                    }
                    PrimaryTargetOrAtom::PrimaryTarget(p) => self.infer_primary_target(p),
                };
                if is_definition {
                    NodeRef::new(self.file, primary_target.index())
                        .add_typing_issue(self.i_s.db, IssueType::UnexpectedTypeDeclaration);
                }
                if let PrimaryContent::GetItem(slice_type) = primary_target.second() {
                    let node_ref = NodeRef::new(self.file, primary_target.index());
                    let slice = SliceType::new(self.file, primary_target.index(), slice_type);
                    let args = slice.as_args(self.i_s.context);
                    base.run_on_value(self.i_s, &mut |i_s, v| {
                        debug!("Set Item on {}", v.name());
                        v.lookup_implicit(i_s, "__setitem__", &|i_s| {
                            debug!("TODO __setitem__ not found");
                        })
                        .run_on_value(i_s, &mut |i_s, v| {
                            v.execute(
                                i_s,
                                &CombinedArguments::new(&args, &KnownArguments::new(value, None)),
                                &mut ResultContext::Unknown,
                                OnTypeError::new(
                                    &|i_s, node_ref, class, function, p, actual, expected| {
                                        node_ref.add_typing_issue(
                                            i_s.db,
                                            IssueType::InvalidGetItem {
                                                actual,
                                                type_: class
                                                    .unwrap()
                                                    .format(&FormatData::new_short(i_s.db)),
                                                expected,
                                            },
                                        )
                                    },
                                ),
                            )
                        })
                    });
                } else {
                    unreachable!();
                }
            }
            Target::Tuple(_) | Target::Starred(_) => unreachable!(),
        }
    }

    fn assign_targets(
        &mut self,
        target: Target,
        value: Inferred,
        value_node_ref: NodeRef,
        is_definition: bool,
    ) {
        match target {
            Target::Tuple(mut targets) => {
                let mut value_iterator = value.save_and_iter(self.i_s, value_node_ref);
                let mut counter = 0;
                while let Some(target) = targets.next() {
                    counter += 1;
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

                            let generic = union.class_as_db_type(self.i_s);
                            let list = Inferred::new_unsaved_complex(ComplexPoint::Instance(
                                self.i_s.db.python_state.list().as_link(),
                                Some(GenericsList::new_generics(Box::new([
                                    GenericItem::TypeArgument(generic),
                                ]))),
                            ));
                            self.assign_targets(
                                star_target.as_target(),
                                list,
                                value_node_ref,
                                is_definition,
                            );
                        } else if value_iterator.len().is_none() {
                            let value = value_iterator.next(self.i_s).unwrap();
                            let list = Inferred::new_unsaved_complex(ComplexPoint::Instance(
                                self.i_s.db.python_state.list().as_link(),
                                Some(GenericsList::new_generics(Box::new([
                                    GenericItem::TypeArgument(value.class_as_db_type(self.i_s)),
                                ]))),
                            ));
                            self.assign_targets(
                                star_target.as_target(),
                                list,
                                value_node_ref,
                                is_definition,
                            );
                        } else {
                            todo!()
                        }
                    } else if let Some(value) = value_iterator.next(self.i_s) {
                        self.assign_targets(target, value, value_node_ref, is_definition)
                    } else {
                        let original_counter = counter;
                        self.assign_targets(
                            target,
                            Inferred::new_any(),
                            value_node_ref,
                            is_definition,
                        );
                        for target in targets {
                            counter += 1;
                            self.assign_targets(
                                target,
                                Inferred::new_any(),
                                value_node_ref,
                                is_definition,
                            );
                        }
                        value_node_ref.add_typing_issue(
                            self.i_s.db,
                            IssueType::TooFewValuesToUnpack {
                                actual: original_counter - 1,
                                expected: counter,
                            },
                        );
                        break;
                    }
                }
            }
            Target::Starred(n) => {
                todo!("Star tuple unpack");
            }
            _ => self.assign_single_target(target, &value, is_definition, |index| {
                value.clone().save_redirect(self.i_s.db, self.file, index);
            }),
        };
    }

    pub fn infer_star_expressions(
        &mut self,
        exprs: StarExpressions,
        result_context: &mut ResultContext,
    ) -> Inferred {
        match exprs.unpack() {
            StarExpressionContent::Expression(expr) => {
                if true {
                    self.infer_expression_with_context(expr, result_context)
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
            StarExpressionContent::Tuple(tuple) => self
                .infer_tuple_iterator(tuple.iter())
                .save_redirect(self.i_s.db, self.file, tuple.index()),
        }
    }

    pub fn infer_named_expression(&mut self, named_expr: NamedExpression) -> Inferred {
        self.infer_named_expression_with_context(named_expr, &mut ResultContext::Unknown)
    }

    pub fn infer_named_expression_with_context(
        &mut self,
        named_expr: NamedExpression,
        result_context: &mut ResultContext,
    ) -> Inferred {
        match named_expr.unpack() {
            NamedExpressionContent::Expression(expr)
            | NamedExpressionContent::Definition(_, expr) => {
                self.infer_expression_with_context(expr, result_context)
            }
        }
    }

    pub fn infer_expression(&mut self, expr: Expression) -> Inferred {
        self.infer_expression_with_context(expr, &mut ResultContext::Unknown)
    }

    check_point_cache_with!(
        pub infer_expression_with_context,
        Self::infer_expression_without_cache,
        Expression,
        result_context
    );
    fn infer_expression_without_cache(
        &mut self,
        expr: Expression,
        result_context: &mut ResultContext,
    ) -> Inferred {
        let inferred = match expr.unpack() {
            ExpressionContent::ExpressionPart(n) => self.infer_expression_part(n, result_context),
            ExpressionContent::Lambda(_) => todo!(),
            ExpressionContent::Ternary(t) => {
                let (if_, condition, else_) = t.unpack();
                self.infer_expression_part(if_, &mut ResultContext::Unknown)
                    .union(self.infer_expression(else_))
            }
        };
        inferred.save_redirect(self.i_s.db, self.file, expr.index())
    }

    pub fn infer_expression_part(
        &mut self,
        node: ExpressionPart,
        result_context: &mut ResultContext,
    ) -> Inferred {
        match node {
            ExpressionPart::Atom(atom) => self.infer_atom(atom, result_context),
            ExpressionPart::Primary(primary) => self.infer_primary(primary, result_context),
            ExpressionPart::Sum(sum) => self.infer_operation(sum.as_operation()),
            ExpressionPart::Term(term) => self.infer_operation(term.as_operation()),
            ExpressionPart::Inversion(inv) => Inferred::new_unsaved_complex(
                ComplexPoint::Instance(self.i_s.db.python_state.builtins_point_link("bool"), None),
            ),
            ExpressionPart::Disjunction(or) => {
                let (first, second) = or.unpack();
                let first = self.infer_expression_part(first, &mut ResultContext::Unknown);
                let second = self.infer_expression_part(second, &mut ResultContext::Unknown);
                Inferred::new_unsaved_complex(ComplexPoint::Instance(
                    self.i_s.db.python_state.builtins_point_link("bool"),
                    None,
                ))
            }
            ExpressionPart::Comparison(cmp) => {
                match cmp.unpack() {
                    ComparisonContent::Equals(first, _, second)
                    | ComparisonContent::NotEquals(first, _, second)
                    | ComparisonContent::Is(first, _, second)
                    | ComparisonContent::IsNot(first, _, second)
                    | ComparisonContent::In(first, _, second)
                    | ComparisonContent::NotIn(first, _, second) => {
                        let first = self.infer_expression_part(first, &mut ResultContext::Unknown);
                        let second =
                            self.infer_expression_part(second, &mut ResultContext::Unknown);
                    }
                    ComparisonContent::Operation(op) => return self.infer_operation(op),
                }
                Inferred::new_unsaved_complex(ComplexPoint::Instance(
                    self.i_s.db.python_state.builtins_point_link("bool"),
                    None,
                ))
            }
            _ => todo!("Not handled yet {node:?}"),
        }
    }

    fn infer_operation(&mut self, op: Operation) -> Inferred {
        let left = self.infer_expression_part(op.left, &mut ResultContext::Unknown);
        let right = self.infer_expression_part(op.right, &mut ResultContext::Unknown);
        let node_ref = NodeRef::new(self.file, op.index);
        let added_note = Cell::new(false);
        let on_error = |i_s: &mut InferenceState, class: Option<&Class>| {
            node_ref.add_typing_issue(
                i_s.db,
                IssueType::UnsupportedOperand {
                    operand: Box::from(op.operand),
                    left: class.unwrap().format(&FormatData::new_short(i_s.db)),
                    right: right.format(i_s, &FormatData::new_short(i_s.db)),
                },
            );
            if left.is_union(i_s.db) && !added_note.get() {
                added_note.set(true);
                node_ref.add_typing_issue(
                    i_s.db,
                    IssueType::Note(
                        format!(
                            "Left operand is of type {:?}",
                            left.format(i_s, &FormatData::new_short(i_s.db)),
                        )
                        .into(),
                    ),
                );
            }
        };
        left.run_on_value(self.i_s, &mut |i_s, value| {
            value.lookup_implicit(i_s, op.magic_method, &|i_s| {
                node_ref.add_typing_issue(
                    i_s.db,
                    IssueType::UnsupportedLeftOperand {
                        operand: Box::from(op.operand),
                        left: value.as_type(i_s).format(&FormatData::new_short(i_s.db)),
                        note: None, // TODO check for unions and stuff
                    },
                )
            })
        })
        .run_on_value(self.i_s, &mut |i_s, value| {
            value.execute(
                i_s,
                &KnownArguments::new(&right, Some(node_ref)),
                &mut ResultContext::Unknown,
                OnTypeError {
                    on_overload_mismatch: Some(&on_error),
                    callback: &|i_s, _, class, _, _, _, _| on_error(i_s, class),
                },
            )
        })
    }

    check_point_cache_with!(pub infer_primary, Self::_infer_primary, Primary, result_context);
    fn _infer_primary(&mut self, primary: Primary, result_context: &mut ResultContext) -> Inferred {
        let base = self.infer_primary_or_atom(primary.first());
        let result = self
            .infer_primary_or_primary_t_content(
                base,
                primary.index(),
                primary.second(),
                false,
                result_context,
            )
            .save_redirect(self.i_s.db, self.file, primary.index());
        debug!(
            "Infer primary {} as {}",
            primary.short_debug(),
            result.description(self.i_s)
        );
        result
    }

    fn infer_primary_or_primary_t_content(
        &mut self,
        base: Inferred,
        node_index: NodeIndex,
        second: PrimaryContent,
        is_target: bool,
        result_context: &mut ResultContext,
    ) -> Inferred {
        match second {
            PrimaryContent::Attribute(name) => base.run_on_value(self.i_s, &mut |i_s, value| {
                debug!("Lookup {}.{}", value.name(), name.as_str());
                match value.lookup(i_s, name.as_str(), &|i_s| {
                    let object = if value.as_module().is_some() {
                        Box::from("Module")
                    } else {
                        format!("{:?}", value.name()).into()
                    };
                    NodeRef::new(self.file, node_index).add_typing_issue(
                        i_s.db,
                        IssueType::AttributeError {
                            object,
                            name: Box::from(name.as_str()),
                        },
                    );
                }) {
                    LookupResult::GotoName(link, inferred) => {
                        // TODO this is not correct, because there can be multiple runs, so setting
                        // it here can be overwritten.
                        self.file.points.set(
                            name.index(),
                            Point::new_redirect(link.file, link.node_index, Locality::Todo),
                        );
                        inferred
                    }
                    LookupResult::FileReference(file_index) => {
                        self.file.points.set(
                            name.index(),
                            Point::new_file_reference(file_index, Locality::Todo),
                        );
                        Inferred::new_file_reference(file_index)
                    }
                    LookupResult::UnknownName(inferred) => inferred,
                    LookupResult::None => Inferred::new_unknown(),
                }
            }),
            PrimaryContent::Execution(details) => {
                let f = self.file;
                let on_type_error = |i_s: &mut InferenceState<'db, '_>,
                                     node_ref: NodeRef,
                                     class: Option<&Class>,
                                     function: Option<&Function>,
                                     p: &dyn ParamWithArgument,
                                     t1,
                                     t2| {
                    node_ref.add_typing_issue(
                        i_s.db,
                        IssueType::ArgumentIssue(
                            format!(
                                "Argument {} has incompatible type {t1:?}; expected {t2:?}",
                                match function {
                                    Some(function) => format!(
                                        "{} to {}",
                                        p.human_readable_argument_index(),
                                        function.diagnostic_string(class),
                                    ),
                                    None => p.human_readable_argument_index(),
                                },
                            )
                            .into(),
                        ),
                    )
                };
                let x = self
                    .i_s
                    .current_execution()
                    .and_then(|x| x.1.as_execution(x.0));
                let args =
                    SimpleArguments::new(self.i_s.clone(), f, node_index, details, x.as_ref());
                if x.is_none() && !is_target && false {
                    if let Some(class) = base.maybe_class(self.i_s) {
                        if class.type_vars(self.i_s).is_none()
                            && class.has_non_overloaded_init_func(self.i_s)
                        {
                            class.type_check_init_func(
                                self.i_s,
                                &args,
                                result_context,
                                OnTypeError::new(&on_type_error),
                            );
                            return Inferred::new_unsaved_specific(Specific::InstanceWithArguments);
                        }
                    }
                }
                base.internal_run(
                    self.i_s,
                    &mut |i_s, value| {
                        debug!("Execute {}", value.name());
                        value.execute(i_s, &args, result_context, OnTypeError::new(&on_type_error))
                    },
                    &|i_s, i1, i2| i1.union(i2),
                    &mut |i_s| {
                        // Still need to calculate diagnostics for all the arguments
                        args.iter_arguments().calculate_diagnostics(i_s);
                        Inferred::new_unknown()
                    },
                )
            }
            PrimaryContent::GetItem(slice_type) => {
                let f = self.file;
                base.run_on_value(self.i_s, &mut |i_s, value| {
                    debug!("Get Item on {}", value.name());
                    value.get_item(i_s, &SliceType::new(f, node_index, slice_type))
                })
            }
        }
    }

    pub fn infer_primary_or_atom(&mut self, p: PrimaryOrAtom) -> Inferred {
        match p {
            PrimaryOrAtom::Primary(primary) => {
                self.infer_primary(primary, &mut ResultContext::Unknown)
            }
            PrimaryOrAtom::Atom(atom) => self.infer_atom(atom, &mut ResultContext::Unknown),
        }
    }

    check_point_cache_with!(pub infer_atom, Self::_infer_atom, Atom, result_context);
    fn _infer_atom(&mut self, atom: Atom, result_context: &mut ResultContext) -> Inferred {
        use AtomContent::*;
        let specific = match atom.unpack() {
            Name(n) => return self.infer_name_reference(n),
            Int(_) => Specific::Integer,
            Float(_) => Specific::Float,
            Complex(_) => Specific::Complex,
            Strings(s_o_b) => {
                for string in s_o_b.iter() {
                    if let StringType::FString(f) = string {
                        self.calc_fstring_diagnostics(f)
                    }
                }
                Specific::String
            }
            Bytes(_) => Specific::Bytes,
            NoneLiteral => Specific::None,
            Boolean(_) => Specific::Boolean,
            Ellipsis => Specific::Ellipsis,
            List(list) => {
                if let Some(result) = self.infer_list_literal_from_context(list, result_context) {
                    return result.save_redirect(self.i_s.db, self.file, atom.index());
                } else if self.i_s.db.python_state.mypy_compatible {
                    let result = match list.unpack() {
                        Some(elements) => self
                            .file
                            .inference(self.i_s)
                            .create_list_or_set_generics(elements),
                        None => GenericItem::TypeArgument(DbType::Any), // TODO shouldn't this be Never?
                    };
                    return Inferred::new_unsaved_complex(ComplexPoint::TypeInstance(Box::new(
                        DbType::Class(
                            self.i_s.db.python_state.builtins_point_link("list"),
                            Some(GenericsList::new_generics(Box::new([result]))),
                        ),
                    )));
                } else {
                    todo!();
                    //Specific::List
                }
            }
            ListComprehension(_) => Specific::List,
            Dict(_) => Specific::Dict,
            DictComprehension(_) => todo!(),
            Set(set) => {
                if let Some(elements) = set.unpack() {
                    return Inferred::new_unsaved_complex(ComplexPoint::Instance(
                        self.i_s.db.python_state.builtins_point_link("set"),
                        Some(GenericsList::new_generics(Box::new([
                            self.create_list_or_set_generics(elements)
                        ]))),
                    ))
                    .save_redirect(self.i_s.db, self.file, atom.index());
                } else {
                    todo!()
                }
            }
            SetComprehension(_) => todo!(),
            Tuple(tuple) => {
                return self.infer_tuple_iterator(tuple.iter()).save_redirect(
                    self.i_s.db,
                    self.file,
                    atom.index(),
                )
            }
            GeneratorComprehension(_) => Specific::GeneratorComprehension,
            YieldExpr(_) => todo!(),
            NamedExpression(named_expression) => {
                return self.infer_named_expression_with_context(named_expression, result_context)
            }
        };
        let point = Point::new_simple_specific(specific, Locality::Todo);
        Inferred::new_and_save(self.file, atom.index(), point)
    }

    fn infer_tuple_iterator<'x>(
        &mut self,
        iterator: impl Iterator<Item = StarLikeExpression<'x>>,
    ) -> Inferred {
        let mut generics = vec![];
        for e in iterator {
            match e {
                StarLikeExpression::NamedExpression(e) => {
                    generics.push(self.infer_named_expression(e).class_as_db_type(self.i_s))
                }
                StarLikeExpression::Expression(e) => {
                    generics.push(self.infer_expression(e).class_as_db_type(self.i_s))
                }
                StarLikeExpression::StarNamedExpression(e) => {
                    let inferred = self
                        .infer_expression_part(e.expression_part(), &mut ResultContext::Unknown);
                    let mut iterator =
                        inferred.save_and_iter(self.i_s, NodeRef::new(self.file, e.index()));
                    if iterator.len().is_some() {
                        while let Some(inf) = iterator.next(self.i_s) {
                            generics.push(inf.class_as_db_type(self.i_s))
                        }
                    } else {
                        todo!()
                    }
                }
                StarLikeExpression::StarExpression(e) => {
                    todo!()
                }
            }
        }
        let content = TupleContent::new_fixed_length(generics.into_boxed_slice());
        debug!(
            "Inferred: {}",
            content.format(&FormatData::new_short(self.i_s.db))
        );
        Inferred::new_unsaved_complex(ComplexPoint::TypeInstance(Box::new(DbType::Tuple(content))))
    }

    check_point_cache_with!(pub infer_primary_target, Self::_infer_primary_target, PrimaryTarget);
    fn _infer_primary_target(&mut self, primary_target: PrimaryTarget) -> Inferred {
        let first = match primary_target.first() {
            PrimaryTargetOrAtom::Atom(atom) => self.infer_atom(atom, &mut ResultContext::Unknown),
            PrimaryTargetOrAtom::PrimaryTarget(p) => self.infer_primary_target(p),
        };
        self.infer_primary_or_primary_t_content(
            first,
            primary_target.index(),
            primary_target.second(),
            true,
            &mut ResultContext::Unknown,
        )
        .save_redirect(self.i_s.db, self.file, primary_target.index())
    }

    check_point_cache_with!(pub infer_name_reference, Self::_infer_name_reference, Name);
    fn _infer_name_reference(&mut self, name: Name) -> Inferred {
        // If it's not inferred already through the name binder, it's either a star import, a
        // builtin or really missing.
        let name_str = name.as_str();
        if let Some(point_link) = self.lookup_from_star_import(name_str, true) {
            self.file.points.set(
                name.index(),
                Point::new_redirect(point_link.file, point_link.node_index, Locality::Todo),
            );
            return self.infer_name_reference(name);
        }
        let point = if name_str == "reveal_type" {
            Point::new_simple_specific(Specific::RevealTypeFunction, Locality::Stmt)
        } else if let Some(link) = self
            .i_s
            .db
            .python_state
            .builtins()
            .lookup_global(name.as_str())
        {
            debug_assert!(link.file != self.file_index || link.node_index != name.index());
            link.into_point_redirect()
        } else {
            // The builtin module should really not have any issues.
            debug_assert!(
                self.file_index != self.i_s.db.python_state.builtins().file_index(),
                "{:?}",
                name
            );
            // TODO check star imports
            NodeRef::new(self.file, name.index()).add_typing_issue(
                self.i_s.db,
                IssueType::NameError {
                    name: Box::from(name.as_str()),
                },
            );
            if self
                .i_s
                .db
                .python_state
                .typing()
                .lookup_global(name_str)
                .is_some()
            {
                // TODO what about underscore or other vars?
                NodeRef::new(self.file, name.index()).add_typing_issue(
                    self.i_s.db,
                    IssueType::Note(
                        format!(
                            "Did you forget to import it from \"typing\"? \
                         (Suggestion: \"from typing import {name_str}\")",
                        )
                        .into(),
                    ),
                );
            }
            Point::new_unknown(self.file_index, Locality::Todo)
        };
        self.file.points.set(name.index(), point);
        debug_assert!(self.file.points.get(name.index()).calculated());
        self.infer_name_reference(name)
    }

    fn lookup_from_star_import(&mut self, name: &str, check_local: bool) -> Option<PointLink> {
        if !name.starts_with('_') {
            for star_import in self.file.star_imports.borrow().iter() {
                // TODO these feel a bit weird and do not include parent functions (when in a
                // closure)
                if !(star_import.scope == 0
                    || check_local
                        && self
                            .i_s
                            .current_function()
                            .map(|f| f.node_ref.node_index == star_import.scope)
                            .or_else(|| {
                                self.i_s
                                    .current_class()
                                    .map(|c| c.node_ref.node_index == star_import.scope)
                            })
                            .unwrap_or(false))
                {
                    continue;
                }
                if let Some(other_file) = star_import.to_file(self) {
                    if let Some(symbol) = other_file.symbol_table.lookup_symbol(name) {
                        return Some(PointLink::new(other_file.file_index(), symbol));
                    }
                    if let Some(l) = other_file
                        .inference(self.i_s)
                        .lookup_from_star_import(name, false)
                    {
                        return Some(l);
                    }
                }
            }
        }
        if let Some(super_file) = self.file.super_file {
            let super_file = self.i_s.db.loaded_python_file(super_file);
            if let Some(symbol) = super_file.symbol_table.lookup_symbol(name) {
                return Some(PointLink::new(super_file.file_index(), symbol));
            }
            super_file
                .inference(self.i_s)
                .lookup_from_star_import(name, false)
        } else {
            None
        }
    }

    pub fn check_point_cache(&mut self, node_index: NodeIndex) -> Option<Inferred> {
        let point = self.file.points.get(node_index);
        let result = point
            .calculated()
            .then(|| match point.type_() {
                PointType::Redirect => {
                    let file_index = point.file_index();
                    let next_node_index = point.node_index();
                    debug_assert!(
                        file_index != self.file.file_index() || next_node_index != node_index
                    );
                    let infer = |inference: &mut PythonInference| {
                        let point = inference.file.points.get(next_node_index);
                        inference
                            .check_point_cache(next_node_index)
                            .unwrap_or_else(|| {
                                let name =
                                    Name::maybe_by_index(&inference.file.tree, next_node_index);
                                if let Some(name) = name {
                                    inference.infer_name(name)
                                } else if let Some(expr) = Expression::maybe_by_index(
                                    &inference.file.tree,
                                    next_node_index,
                                ) {
                                    inference.infer_expression_without_cache(
                                        expr,
                                        &mut ResultContext::Unknown,
                                    )
                                } else if let Some(annotation) = Annotation::maybe_by_index(
                                    &inference.file.tree,
                                    next_node_index,
                                ) {
                                    todo!()
                                    // inference.compute_annotation(annotation)
                                } else {
                                    todo!(
                                        "{}",
                                        NodeRef::new(inference.file, next_node_index)
                                            .debug_info(self.i_s.db)
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
                                .db
                                .loaded_python_file(file_index)
                                .inference(self.i_s),
                        )
                    }
                }
                PointType::Specific => match point.specific() {
                    Specific::Param => {
                        let name_def = NameDefinition::by_index(&self.file.tree, node_index);
                        // Performance: This could be improved by not needing to lookup all the
                        // parents all the time.
                        if let FunctionOrLambda::Function(func) =
                            name_def.function_or_lambda_ancestor().unwrap()
                        {
                            let func = Function::new(
                                NodeRef::new(self.file, func.index()),
                                self.i_s.current_class().copied(),
                            );
                            func.type_vars(self.i_s);
                        }

                        if let Some(annotation) = name_def.maybe_param_annotation() {
                            match name_def.name().simple_param_kind() {
                                SimpleParamKind::Normal => self.use_cached_annotation(annotation),
                                SimpleParamKind::Starred => {
                                    let p = self
                                        .use_cached_annotation_type(annotation)
                                        .into_db_type(self.i_s);
                                    Inferred::new_unsaved_complex(ComplexPoint::TypeInstance(
                                        Box::new(DbType::Tuple(
                                            TupleContent::new_arbitrary_length(p),
                                        )),
                                    ))
                                }
                                SimpleParamKind::DoubleStarred => {
                                    let p = self
                                        .use_cached_annotation_type(annotation)
                                        .into_db_type(self.i_s);
                                    Inferred::create_instance(
                                        self.i_s.db.python_state.builtins_point_link("dict"),
                                        Some(&[
                                            GenericItem::TypeArgument(DbType::Class(
                                                self.i_s.db.python_state.builtins_point_link("str"),
                                                None,
                                            )),
                                            GenericItem::TypeArgument(p),
                                        ]),
                                    )
                                }
                            }
                        } else if let Some((function, args)) = self.i_s.current_execution() {
                            function
                                .infer_param(self.i_s, node_index, args)
                                .resolve_function_return(self.i_s)
                        } else {
                            todo!("{:?}", self.i_s.context)
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
                        todo!();
                        //self.check_point_cache(node_index).unwrap()
                    }
                    Specific::AnnotationWithTypeVars => {
                        // For variable annotations like a: int
                        // TODO is this really the right place?
                        if self.i_s.is_diagnostic() {
                            return Inferred::new_saved(self.file, node_index, point);
                        }
                        let d = self
                            .use_db_type_of_annotation(node_index)
                            .replace_type_vars(&mut |t| {
                                if let Some(class) = self.i_s.current_class() {
                                    if class.node_ref.as_link() == t.in_definition {
                                        return dbg!(class
                                            .generics()
                                            .nth_usage(self.i_s, t)
                                            .into_generic_item(self.i_s));
                                    }
                                }
                                match t.type_var_like.as_ref() {
                                    TypeVarLike::TypeVar(_) => {
                                        GenericItem::TypeArgument(DbType::TypeVar(t.clone()))
                                    }
                                    TypeVarLike::TypeVarTuple(_) => todo!(), //GenericItem::TypeArguments(
                                    //TypeArguments::new_fixed_length(Box::new([DbType::TypeVarLike(t.clone())]))
                                    //),
                                    TypeVarLike::ParamSpec(_) => todo!(),
                                }
                            });
                        Inferred::new_unsaved_complex(ComplexPoint::TypeInstance(Box::new(d)))
                    }
                    _ => Inferred::new_saved(self.file, node_index, point),
                },
                PointType::MultiDefinition => {
                    // TODO for now we use Mypy's way of resolving multiple names, which means that
                    // it always uses the first name.
                    /*
                    let inferred = self.infer_name(Name::by_index(&self.file.tree, point.node_index()));
                    // Check for the cache of name_definition
                    let name_def = NameDefinition::by_index(&self.file.tree, node_index - 1);
                    inferred.union(self.infer_multi_definition(name_def))
                    */
                    self.check_point_cache(point.node_index())
                        .unwrap_or_else(|| {
                            self.infer_name(Name::by_index(&self.file.tree, point.node_index()))
                        })
                }
                PointType::Complex | PointType::Unknown | PointType::FileReference => {
                    Inferred::new_saved(self.file, node_index, point)
                }
                PointType::NodeAnalysis => {
                    panic!("Invalid state, should not happen {node_index:?}");
                }
            })
            .or_else(|| {
                if point.calculating() {
                    let node_ref = NodeRef::new(self.file, node_index);
                    node_ref.set_point(Point::new_simple_specific(Specific::Cycle, Locality::Todo));
                    Some(Inferred::new_unsaved_specific(Specific::Cycle))
                } else {
                    None
                }
            });
        if cfg!(feature = "zuban_debug") {
            if let Some(inferred) = result.as_ref() {
                if inferred.is_unknown() {
                    debug!("Found unknown cache result: {node_index}");
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
    fn _infer_multi_definition(&mut self, name_def: NameDefinition) -> Inferred {
        self.infer_name_definition(name_def)
    }

    pub fn infer_name_by_index(&mut self, node_index: NodeIndex) -> Inferred {
        self.infer_name(Name::by_index(&self.file.tree, node_index))
    }

    pub fn infer_name(&mut self, name: Name) -> Inferred {
        let point = self.file.points.get(name.index());
        if point.calculated() && point.type_() == PointType::MultiDefinition {
            // We are trying to infer the name here. We don't have to follow the multi definition,
            // because the cache handling takes care of that.
            println!("TODO Is this branch still needed???");
            //self.infer_multi_definition(name.name_definition().unwrap())
        }
        match name.name_definition() {
            Some(name_def) => self.infer_name_definition(name_def),
            None => {
                todo!()
                /* TODO maybe use this???
                if name_def.is_reference() {
                    // References are not calculated by the name binder for star imports and
                    // lookups.
                    if let Some(primary) = name_def.maybe_primary_parent() {
                        return self.infer_primary(primary);
                    } else {
                        todo!(
                            "star import {} {name_def:?} {:?}",
                            self.file.file_path(self.i_s.db),
                            self.file.byte_to_line_column(name_def.start())
                        )
                    }
                } else {
                }
                */
            }
        }
    }

    check_point_cache_with!(pub infer_name_definition, Self::_infer_name_definition, NameDefinition);
    fn _infer_name_definition(&mut self, name_def: NameDefinition) -> Inferred {
        let stmt_like = name_def.expect_stmt_like_ancestor();

        if !self.file.points.get(stmt_like.index()).calculated() {
            match stmt_like {
                StmtLike::SimpleStmts(s) => {
                    self.cache_simple_stmts_name(s, NodeRef::new(self.file, name_def.index()));
                }
                StmtLike::Stmt(stmt) => {
                    self.cache_stmt_name(stmt, NodeRef::new(self.file, name_def.index()));
                }
                _ => todo!("{stmt_like:?}"),
            }
        }
        debug_assert!(
            self.file.points.get(name_def.index()).calculated(),
            "{name_def:?}",
        );
        self.infer_name_definition(name_def)
    }

    pub fn infer_by_node_index(&mut self, node_index: NodeIndex) -> Inferred {
        self.check_point_cache(node_index)
            .unwrap_or_else(|| todo!())
    }
}
