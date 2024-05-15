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
    config::set_flag,
    database::{
        ComplexPoint, Database, FileIndex, Locality, LocalityLink, Point, Points, PythonProject,
        Specific,
    },
    debug,
    diagnostics::{Diagnostic, DiagnosticConfig, Diagnostics, Issue, IssueKind},
    inference_state::InferenceState,
    inferred::Inferred,
    lines::NewlineIndices,
    matching::ResultContext,
    name::{Names, TreeName, TreePosition},
    node_ref::NodeRef,
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
        let mut vec: Vec<_> = unsafe {
            self.issues
                .iter()
                .filter(|i| config.should_be_reported(&db.project, &i.kind))
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
        let ignore_type_errors = tree
            .has_type_ignore_at_start()
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
        let flags = directives_to_flags(
            project_options,
            &issues,
            tree.mypy_inline_config_directives(),
        );
        let length = tree.length();
        Self {
            tree,
            file_index: Cell::new(None),
            symbol_table: Default::default(),
            points: Points::new(length),
            complex_points: Default::default(),
            star_imports: Default::default(),
            issues,
            newline_indices: NewlineIndices::new(),
            sub_files: Default::default(),
            super_file: None,
            is_stub,
            ignore_type_errors,
            flags,
        }
    }

    fn with_global_binder(
        &'db self,
        project: &PythonProject,
        func: impl FnOnce(&mut NameBinder<'_, 'db>),
    ) {
        self.symbol_table
            .set(NameBinder::with_global_binder(
                &self.flags(project),
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

fn directives_to_flags<'x>(
    project: &PythonProject,
    issues: &Diagnostics,
    directives: impl Iterator<Item = (CodeIndex, &'x str)>,
) -> Option<TypeCheckerFlags> {
    // Directives like `# mypy: disallow-any-generics`
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
            if let Err(err) = set_flag(flags.as_mut().unwrap(), &name, value) {
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
    flags
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
            } else {
                if n == '"' {
                    opened_quotation_mark = true;
                    had_quotation_marks = true;
                } else if n == ',' {
                    self.start_position += i as CodeIndex;
                    let result = &self.rest[..i];
                    self.rest = &self.rest[i + 1..];
                    return split_name_value(result, had_quotation_marks);
                }
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
