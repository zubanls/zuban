use std::{
    cell::{Cell, OnceCell, RefCell},
    collections::HashMap,
    fmt,
    rc::Rc,
};

use parsa_python_cst::*;

use super::{
    file_state::{File, Leaf},
    inference::Inference,
    name_binder::NameBinder,
};
use crate::{
    config::{set_flag, to_bool},
    database::{
        ComplexPoint, Database, FileIndex, Locality, LocalityLink, Point, PointKind, Points,
        PythonProject, Specific,
    },
    debug,
    diagnostics::{Diagnostic, DiagnosticConfig, Diagnostics, Issue, IssueKind},
    inference_state::InferenceState,
    inferred::Inferred,
    lines::NewlineIndices,
    matching::ResultContext,
    name::{Names, TreeName, TreePosition},
    node_ref::NodeRef,
    type_::DbString,
    utils::{InsertOnlyVec, SymbolTable},
    workspaces::FileEntry,
    TypeCheckerFlags,
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

    pub unsafe fn iter(&self) -> impl Iterator<Item = &ComplexPoint> {
        self.0.iter()
    }
}

pub struct PythonFile {
    pub tree: Tree, // TODO should probably not be public
    pub symbol_table: OnceCell<SymbolTable>,
    maybe_dunder_all: OnceCell<Option<Box<[DbString]>>>, // For __all__
    //all_names_bloom_filter: Option<BloomFilter<&str>>,
    pub points: Points,
    pub complex_points: ComplexValues,
    file_index: Cell<Option<FileIndex>>,
    pub issues: Diagnostics,
    pub star_imports: RefCell<Vec<StarImport>>,
    sub_files: RefCell<HashMap<CodeIndex, FileIndex>>,
    pub(crate) super_file: Option<FileIndex>,
    pub is_stub: bool,
    pub ignore_type_errors: bool,
    flags: Option<TypeCheckerFlags>,

    newline_indices: NewlineIndices,
}

impl File for PythonFile {
    fn ensure_initialized(&self, project: &PythonProject) {
        if self.symbol_table.get().is_some() {
            // It was already done.
            return;
        }
        self.with_global_binder(project, |binder| binder.index_file(self.tree.root()));

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
                let i_s = InferenceState::new(db);
                return self
                    .inference(&i_s)
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
        let i_s = InferenceState::new(db);
        if self.super_file.is_none() {
            // The main file is responsible for calculating diagnostics of type comments,
            // annotation strings, etc.
            self.inference(&i_s).calculate_diagnostics();
        }
        let flags = self.flags(&db.project);
        let mut vec: Vec<_> = unsafe {
            self.issues
                .iter()
                .filter(|i| config.should_be_reported(flags, &i.kind))
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
        vec.sort_by_key(|diag| diag.issue.start_position);
        vec.into_boxed_slice()
    }

    fn invalidate_references_to(&mut self, file_index: FileIndex) {
        self.points.invalidate_references_to(file_index);
        self.issues.clear();
    }
}

#[derive(Debug)]
pub struct StarImport {
    pub(super) scope: NodeIndex,
    pub(super) import_from_node: NodeIndex,
    pub(super) star_node: NodeIndex,
}

impl StarImport {
    #[inline]
    pub(super) fn to_file<'db>(
        &self,
        inference: &Inference<'db, '_, '_>,
    ) -> Option<&'db PythonFile> {
        let point = inference.file.points.get(self.star_node);
        if point.calculated() {
            return if point.maybe_specific() == Some(Specific::ModuleNotFound) {
                None
            } else {
                Some(inference.i_s.db.loaded_python_file(point.file_index()))
            };
        }
        let import_from = NodeRef::new(inference.file, self.import_from_node).expect_import_from();
        inference.cache_import_from(import_from);
        debug_assert!(inference.file.points.get(self.star_node).calculated());
        self.to_file(inference)
    }
}

impl fmt::Debug for PythonFile {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("PythonFile")
            .field("file_index", &self.file_index.get())
            .finish()
    }
}

impl<'db> PythonFile {
    pub fn new(project_options: &PythonProject, code: Box<str>, is_stub: bool) -> Self {
        let issues = Diagnostics::default();
        let tree = Tree::parse(code);
        let mut ignore_type_errors =
            tree.has_type_ignore_at_start()
                .unwrap_or_else(|ignore_code| {
                    issues
                        .add_if_not_ignored(
                            Issue::from_start_stop(
                                1,
                                1,
                                IssueKind::TypeIgnoreWithErrorCodeNotSupportedForModules {
                                    ignore_code: ignore_code.into(),
                                },
                            ),
                            None,
                        )
                        .ok();
                    true
                });
        let directives_info = info_from_directives(
            project_options,
            &issues,
            tree.mypy_inline_config_directives(),
        );
        ignore_type_errors |= directives_info.ignore_errors;
        let length = tree.length();
        Self {
            tree,
            file_index: Cell::new(None),
            symbol_table: Default::default(),
            maybe_dunder_all: OnceCell::default(),
            points: Points::new(length),
            complex_points: Default::default(),
            star_imports: Default::default(),
            issues,
            newline_indices: NewlineIndices::new(),
            sub_files: Default::default(),
            super_file: None,
            is_stub,
            ignore_type_errors,
            flags: directives_info.flags,
        }
    }

    fn with_global_binder(
        &'db self,
        project: &PythonProject,
        func: impl FnOnce(&mut NameBinder<'_, 'db>),
    ) {
        self.symbol_table
            .set(NameBinder::with_global_binder(
                self.flags(project),
                &self.tree,
                &self.points,
                &self.complex_points,
                &self.issues,
                &self.star_imports,
                self.file_index.get().unwrap(),
                self.is_stub,
                func,
            ))
            .unwrap()
    }

    pub fn inference<'file, 'i_s>(
        &'file self,
        i_s: &'i_s InferenceState<'db, 'i_s>,
    ) -> Inference<'db, 'file, 'i_s> {
        Inference {
            file: self,
            file_index: self.file_index(),
            i_s,
        }
    }

    pub fn lookup_global(&self, name: &str) -> Option<LocalityLink> {
        self.symbol_table
            .get()
            .unwrap()
            .lookup_symbol(name)
            .map(|node_index| LocalityLink {
                file: self.file_index(),
                node_index,
                locality: Locality::Todo,
            })
    }

    pub fn import_global_name(&self, db: &Database, name: &str) -> Option<LocalityLink> {
        if let Some(dunder) = self.maybe_dunder_all(db) {
            if !dunder.iter().any(|x| x.as_str(db) == name) {
                return None;
            }
        } else if name.starts_with('_') {
            return None;
        }
        self.lookup_global(name)
    }

    pub(super) fn new_annotation_file(
        &self,
        db: &'db Database,
        start: CodeIndex,
        code: Box<str>, // TODO this should not be a string, but probably cow
    ) -> &'db Self {
        // TODO should probably not need a newline
        let mut file = PythonFile::new(
            &db.project,
            Box::from(code.into_string() + "\n"),
            self.is_stub,
        );
        file.super_file = Some(self.file_index());
        // TODO just saving this in the cache and forgetting about it is a bad idea
        let f = db.load_sub_file(self, file);
        self.sub_files.borrow_mut().insert(start, f.file_index());
        f
    }

    pub fn is_stub_or_in_protocol(&self, i_s: &InferenceState) -> bool {
        if let Some(current_class) = i_s.current_class() {
            if current_class.is_protocol(i_s.db) {
                return true;
            }
        }
        self.is_stub
    }

    pub fn maybe_dunder_all(&self, db: &Database) -> Option<&[DbString]> {
        self.maybe_dunder_all
            .get_or_init(|| {
                self.symbol_table
                    .get()
                    .unwrap()
                    .lookup_symbol("__all__")
                    .and_then(|dunder_all_index| {
                        let name_def = NodeRef::new(self, dunder_all_index)
                            .maybe_name()
                            .unwrap()
                            .name_definition()
                            .unwrap();
                        if let Some((_, _, expr)) =
                            name_def
                                .maybe_assignment_definition()
                                .and_then(|assignment| {
                                    assignment.maybe_simple_type_expression_assignment()
                                })
                        {
                            let base = maybe_dunder_all_names(vec![], self.file_index(), expr)?;
                            self.gather_dunder_all_modifications(db, dunder_all_index, base)
                        } else if let Some(import) = name_def.maybe_import() {
                            if let NameImportParent::ImportFromAsName(as_name) = import {
                                let i_s = InferenceState::new(db);
                                let inference = self.inference(&i_s);
                                inference.infer_name_definition(name_def);
                                // Just take the __all__ from the now calculated file. The exact
                                // position doesn't matter anymore, because that is calculated by
                                // exactly this method.
                                let name_def_point =
                                    NodeRef::new(self, as_name.name_definition().index()).point();
                                let base = name_def_point
                                    .as_redirected_node_ref(db)
                                    .file
                                    .maybe_dunder_all(db)?;
                                self.gather_dunder_all_modifications(
                                    db,
                                    dunder_all_index,
                                    base.into(),
                                )
                            } else {
                                None
                            }
                        } else {
                            None
                        }
                    })
            })
            .as_deref()
    }

    fn gather_dunder_all_modifications(
        &self,
        db: &Database,
        dunder_all_index: NodeIndex,
        mut dunder_all: Vec<DbString>,
    ) -> Option<Box<[DbString]>> {
        let file_index = self.file_index();
        let check_multi_def = |dunder_all: Vec<DbString>, name: Name| -> Option<Vec<DbString>> {
            let name_def = name.name_definition().unwrap();
            let assignment = name_def.maybe_assignment_definition()?;
            if let AssignmentContent::AugAssign(_, _, right_side) = assignment.unpack() {
                maybe_dunder_all_names(
                    dunder_all,
                    file_index,
                    right_side.maybe_simple_expression()?,
                )
            } else {
                None
            }
        };

        let check_ref = |mut dunder_all: Vec<DbString>, name: Name| -> Option<Vec<DbString>> {
            if let Some(primary) = name.maybe_atom_of_primary() {
                if let PrimaryParent::Primary(maybe_call) = primary.parent() {
                    if let PrimaryContent::Execution(arg_details) = maybe_call.second() {
                        if let PrimaryContent::Attribute(attr) = primary.second() {
                            let maybe_single = arg_details.maybe_single_named_expr();
                            match attr.as_code() {
                                "append" => dunder_all.push(DbString::from_python_string(
                                    file_index,
                                    maybe_single?
                                        .expression()
                                        .maybe_single_string_literal()?
                                        .as_python_string(),
                                )?),
                                "extend" => {
                                    return maybe_dunder_all_names(
                                        dunder_all,
                                        file_index,
                                        maybe_single?.expression(),
                                    )
                                }
                                "remove" => {
                                    let s = maybe_single?
                                        .expression()
                                        .maybe_single_string_literal()?
                                        .as_python_string();
                                    let to_remove = s.as_str()?;
                                    dunder_all.retain(|x| x.as_str(db) != to_remove)
                                }
                                _ => (),
                            }
                        }
                    }
                }
            }
            Some(dunder_all)
        };
        let p = self.points.get(dunder_all_index);
        if p.calculated() && p.kind() == PointKind::MultiDefinition {
            for index in MultiDefinitionIterator::new(&self.points, dunder_all_index) {
                let name = NodeRef::new(self, index as NodeIndex).maybe_name().unwrap();
                dunder_all = check_multi_def(dunder_all, name)?
            }
        }
        for (index, point) in self.points.iter().enumerate() {
            if point.maybe_redirect_to(file_index, dunder_all_index) {
                if let Some(name) = NodeRef::new(self, index as NodeIndex).maybe_name() {
                    dunder_all = check_ref(dunder_all, name)?
                }
            }
        }
        Some(dunder_all.into())
    }

    pub fn file_entry(&self, db: &Database) -> Rc<FileEntry> {
        db.file_state(self.file_index()).file_entry()
    }

    pub fn add_issue(&self, i_s: &InferenceState, issue: Issue) {
        if !i_s.should_add_issue() || self.ignore_type_errors {
            return;
        }
        let maybe_ignored = self
            .tree
            .type_ignore_comment_for(issue.start_position, issue.end_position);
        let config = DiagnosticConfig {
            show_column_numbers: true,
            ..Default::default()
        };
        match self.issues.add_if_not_ignored(issue, maybe_ignored) {
            Ok(issue) => debug!(
                "NEW ISSUE: {}",
                Diagnostic::new(i_s.db, self, issue).as_string(&config)
            ),
            Err(issue) => debug!(
                "New ignored issue: {}",
                Diagnostic::new(i_s.db, self, &issue).as_string(&config)
            ),
        }
    }

    pub fn flags<'x>(&'x self, project: &'x PythonProject) -> &TypeCheckerFlags {
        self.flags.as_ref().unwrap_or(&project.flags)
    }
}

fn info_from_directives<'x>(
    project: &PythonProject,
    issues: &Diagnostics,
    directives: impl Iterator<Item = (CodeIndex, &'x str)>,
) -> DirectivesInfos {
    // Directives like `# mypy: disallow-any-generics`
    let mut ignore_errors = false;
    let mut flags = None;
    for (start_position, rest) in directives {
        let splitter = DirectiveSplitter {
            issues,
            rest,
            start_position,
        };
        for (name, value) in splitter {
            let name = name.replace('-', "_");
            if flags.is_none() {
                flags = Some(project.flags.clone());
            }
            let mut check = || {
                if name == "ignore_errors" {
                    ignore_errors = to_bool(value, false)?;
                    Ok(())
                } else {
                    set_flag(flags.as_mut().unwrap(), &name, value)
                }
            };
            if let Err(err) = check() {
                issues
                    .add_if_not_ignored(
                        Issue {
                            kind: IssueKind::DirectiveSyntaxError(err),
                            start_position,
                            end_position: start_position + rest.len() as CodeIndex,
                        },
                        None,
                    )
                    .ok();
            }
        }
    }
    DirectivesInfos {
        flags,
        ignore_errors,
    }
}

struct DirectivesInfos {
    flags: Option<TypeCheckerFlags>,
    ignore_errors: bool,
}

struct DirectiveSplitter<'db, 'code> {
    issues: &'db Diagnostics,
    rest: &'code str,
    start_position: CodeIndex,
}

impl<'code> Iterator for DirectiveSplitter<'_, 'code> {
    type Item = (&'code str, Option<&'code str>);
    fn next(&mut self) -> Option<Self::Item> {
        let split_name_value = |directive: &'code str, had_quotation_marks: bool| {
            let (name, value) = if let Some((first, second)) = directive.split_once('=') {
                let mut second = second.trim();
                if had_quotation_marks {
                    if second.chars().next().is_some_and(|first| first == '"')
                        && second.chars().last().is_some_and(|last| last == '"')
                    {
                        second = &second[1..second.len() - 1];
                    } else {
                        todo!("weird quotes")
                    }
                }
                (first.trim(), Some(second))
            } else {
                (directive.trim(), None)
            };
            if name.contains('"') {
                todo!("weird quotes")
            }
            Some((name, value))
        };
        let mut opened_quotation_mark = false;
        let mut had_quotation_marks = false;
        for (i, n) in self.rest.chars().enumerate() {
            if opened_quotation_mark {
                if n == '"' {
                    opened_quotation_mark = false;
                }
            } else if n == '"' {
                opened_quotation_mark = true;
                had_quotation_marks = true;
            } else if n == ',' {
                self.start_position += i as CodeIndex;
                let result = &self.rest[..i];
                self.rest = &self.rest[i + 1..];
                return split_name_value(result, had_quotation_marks);
            }
        }
        if opened_quotation_mark {
            self.issues
                .add_if_not_ignored(
                    Issue {
                        kind: IssueKind::DirectiveSyntaxError(
                            "Unterminated quote in configuration comment".into(),
                        ),
                        start_position: self.start_position,
                        end_position: self.start_position + self.rest.len() as CodeIndex,
                    },
                    None,
                )
                .ok();
        } else {
            let rest = self.rest.trim();
            if !rest.is_empty() {
                self.rest = "";
                return split_name_value(rest, had_quotation_marks);
            }
        }
        self.rest = "";
        None
    }
}

fn maybe_dunder_all_names(
    mut result: Vec<DbString>,
    file_index: FileIndex,
    expr: Expression,
) -> Option<Vec<DbString>> {
    let elements = match expr.maybe_unpacked_atom()? {
        AtomContent::List(list) => list.unpack(),
        AtomContent::Tuple(tup) => tup.iter(),
        _ => return None,
    };

    for star_like in elements {
        match star_like {
            StarLikeExpression::NamedExpression(named_expr) => {
                result.push(DbString::from_python_string(
                    file_index,
                    named_expr
                        .expression()
                        .maybe_single_string_literal()?
                        .as_python_string(),
                )?)
            }
            StarLikeExpression::StarNamedExpression(_) => return None,
            _ => unreachable!(),
        }
    }
    Some(result)
}

struct MultiDefinitionIterator<'a> {
    points: &'a Points,
    start: NodeIndex,
    current: NodeIndex,
}

impl<'a> MultiDefinitionIterator<'a> {
    fn new(points: &'a Points, start: NodeIndex) -> Self {
        debug_assert_eq!(points.get(start).kind(), PointKind::MultiDefinition);
        Self {
            points,
            start,
            current: start,
        }
    }
}

impl Iterator for MultiDefinitionIterator<'_> {
    type Item = NodeIndex;

    fn next(&mut self) -> Option<Self::Item> {
        let p = self.points.get(self.current);
        debug_assert_eq!(p.kind(), PointKind::MultiDefinition);
        let next = p.node_index();
        if next == self.start {
            None
        } else {
            self.current = next;
            Some(next)
        }
    }
}
