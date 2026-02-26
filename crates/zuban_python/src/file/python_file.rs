use std::{
    borrow::Cow,
    cell::RefCell,
    collections::{HashMap, VecDeque},
    fmt,
    ops::Range,
    sync::{Arc, OnceLock, RwLock},
};

use config::{
    DiagnosticConfig, FinalizedTypeCheckerFlags, IniOrTomlValue, TypeCheckerFlags, set_flag,
};
use parsa_python_cst::*;
use utils::InsertOnlyVec;
use vfs::{Directory, DirectoryEntry, FileEntry, FileIndex, PathWithScheme, WorkspaceKind};

use super::{
    FLOW_ANALYSIS,
    file_state::File,
    flow_analysis::DelayedDiagnostic,
    imports::is_package_name,
    inference::Inference,
    name_binder::{DbInfos, NameBinder},
    name_resolution::{ModuleAccessDetail, NameResolution},
};
use crate::{
    InputPosition,
    database::{
        ComplexPoint, Database, Locality, Point, PointLink, Points, PythonProject, Specific,
    },
    debug,
    diagnostics::{Diagnostic, Diagnostics, Issue, IssueKind},
    imports::{ImportResult, STUBS_SUFFIX},
    inference_state::InferenceState,
    lines::{BytePositionInfos, NewlineIndices, PositionInfos},
    node_ref::NodeRef,
    type_::{DbString, LookupResult},
    utils::SymbolTable,
};

#[derive(Default, Debug, Clone)]
pub(crate) struct ComplexValues(InsertOnlyVec<ComplexPoint>);

impl ComplexValues {
    pub fn get(&self, index: usize) -> &ComplexPoint {
        &self.0[index]
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
        unsafe { self.0.iter() }
    }

    #[expect(dead_code)]
    pub fn clear(&mut self) {
        self.0.clear()
    }
}

#[derive(Copy, Clone, Debug)]
pub(crate) struct SuperFile {
    pub file: FileIndex,
    // This is is the offset where the sub file starts if it's in the same file
    // It might also be part of a notebook and therefore be different files with different URIs.
    pub offset: Option<CodeIndex>,
}

impl SuperFile {
    pub fn file<'db>(&self, db: &'db Database) -> &'db PythonFile {
        db.loaded_python_file(self.file)
    }

    pub fn is_part_of_parent(&self) -> bool {
        self.offset.is_some()
    }
}

#[derive(Copy, Clone, Debug)]
pub(crate) struct FileImport {
    pub node_index: NodeIndex,
    pub in_global_scope: bool,
}

pub(crate) struct PythonFile {
    pub tree: Tree, // TODO should probably not be public
    pub symbol_table: SymbolTable,
    maybe_dunder_all: OnceLock<Option<Box<[DbString]>>>, // For __all__
    pub points: Points,
    pub complex_points: ComplexValues,
    pub file_index: FileIndex,
    pub issues: Diagnostics,
    pub star_imports: Box<[StarImport]>,
    pub all_imports: Box<[FileImport]>,
    pub sub_files: SubFiles,
    pub(crate) super_file: Option<SuperFile>,
    stub_cache: Option<StubCache>,
    pub ignore_type_errors: bool,
    flags: Option<FinalizedTypeCheckerFlags>,
    pub(super) delayed_diagnostics: RwLock<VecDeque<DelayedDiagnostic>>,

    pub newline_indices: NewlineIndices,
}

#[derive(Default)]
pub(crate) struct SubFiles {
    in_same_file: RwLock<HashMap<CodeIndex, FileIndex>>,
    separate_files: Vec<FileIndex>,
}

impl SubFiles {
    fn lookup_sub_file_at_position(&self, start: CodeIndex) -> Option<FileIndex> {
        self.in_same_file.read().unwrap().get(&start).copied()
    }

    fn save_sub_file_at_position(&self, start: CodeIndex, file_index: FileIndex) {
        self.in_same_file.write().unwrap().insert(start, file_index);
    }

    pub fn add_separate_file(&mut self, sub_file: FileIndex) {
        self.separate_files.push(sub_file);
    }

    pub fn take_separate_files(&mut self) -> Vec<FileIndex> {
        std::mem::take(&mut self.separate_files)
    }
}

impl Clone for SubFiles {
    fn clone(&self) -> Self {
        Self {
            in_same_file: RwLock::new(self.in_same_file.read().unwrap().clone()),
            separate_files: self.separate_files.clone(),
        }
    }
}

impl Clone for PythonFile {
    fn clone(&self) -> Self {
        Self {
            tree: self.tree.clone(),
            symbol_table: self.symbol_table.clone(),
            maybe_dunder_all: self.maybe_dunder_all.clone(),
            points: self.points.clone(),
            complex_points: self.complex_points.clone(),
            file_index: self.file_index,
            issues: self.issues.clone(),
            star_imports: self.star_imports.clone(),
            all_imports: self.all_imports.clone(),
            sub_files: self.sub_files.clone(),
            super_file: self.super_file,
            stub_cache: self.stub_cache.clone(),
            ignore_type_errors: self.ignore_type_errors,
            flags: self.flags.clone(),
            delayed_diagnostics: RwLock::new(self.delayed_diagnostics.read().unwrap().clone()),
            newline_indices: self.newline_indices.clone(),
        }
    }
}

impl File for PythonFile {
    fn file_index(&self) -> FileIndex {
        self.file_index
    }

    fn code(&self) -> &str {
        self.tree.code()
    }

    fn line_column_to_byte(&self, input: InputPosition) -> anyhow::Result<BytePositionInfos> {
        self.newline_indices
            .line_column_to_byte(self.tree.code(), input)
    }

    fn byte_to_position_infos<'db>(
        &'db self,
        db: &'db Database,
        byte: CodeIndex,
    ) -> PositionInfos<'db> {
        if let Some(super_file) = self.super_file
            && let Some(offset) = super_file.offset
        {
            super_file
                .file(db)
                .byte_to_position_infos(db, offset + byte)
        } else {
            self.newline_indices.position_infos(self.tree.code(), byte)
        }
    }

    fn diagnostics<'db>(&'db self, db: &'db Database) -> Box<[Diagnostic<'db>]> {
        if self
            .super_file
            .is_none_or(|super_file| !super_file.is_part_of_parent())
        {
            // The main file is responsible for calculating diagnostics of type comments,
            // annotation strings, etc.
            let result = self.ensure_calculated_diagnostics(db);
            debug_assert!(result.is_ok());
        }
        let mut vec: Vec<_> = unsafe {
            self.issues
                .iter()
                .map(|i| Diagnostic::new(db, self, i))
                .collect()
        };
        for (_, file_index) in self.sub_files.in_same_file.read().unwrap().iter() {
            let file = db.loaded_python_file(*file_index);
            vec.extend(file.diagnostics(db).into_vec().into_iter());
        }
        vec.sort_by_key(|diag| diag.issue.start_position);
        vec.into_boxed_slice()
    }

    fn invalidate_full_db(&mut self, project: &PythonProject) {
        debug_assert!(self.super_file.is_none());
        let mut points = std::mem::take(&mut self.points);
        points.invalidate_full_db();
        let is_stub = self.is_stub();
        let tree = std::mem::replace(&mut self.tree, Tree::invalid_empty());
        *self = Self::new_internal(
            self.file_index,
            tree,
            points,
            Diagnostics::default(),
            is_stub,
            self.flags.take().map(|flags| flags.into_unfinalized()),
            project,
            self.ignore_type_errors,
        );
    }

    fn has_super_file(&self) -> bool {
        self.super_file.is_some()
    }
}

impl vfs::VfsFile for PythonFile {
    type Artifacts = Tree;

    fn code(&self) -> &str {
        self.tree.code()
    }

    fn into_recoverable_artifacts(self) -> Tree {
        self.tree
    }

    fn invalidate_references_to(&mut self, file_index: Option<FileIndex>) {
        self.points.invalidate_references_to(file_index);
        self.issues.invalidate_non_name_binder_issues();
        if let Some(cache) = self.stub_cache.as_mut() {
            *cache = StubCache::default();
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) struct StarImport {
    pub scope: NodeIndex,
    pub(super) import_from_node: NodeIndex,
    pub(super) star_node: NodeIndex,
}

impl StarImport {
    pub fn in_module_scope(&self) -> bool {
        self.scope == 0
    }
}

impl fmt::Debug for PythonFile {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("PythonFile")
            .field("file_index", &self.file_index)
            .finish()
    }
}

impl<'db> PythonFile {
    pub fn from_file_entry_and_code(
        project: &PythonProject,
        file_index: FileIndex,
        file_entry: &FileEntry,
        code: Box<str>,
    ) -> Self {
        debug!("Initialize {} ({file_index})", file_entry.name);
        let tree = Tree::parse(code);
        PythonFile::new(project, file_index, file_entry, tree)
    }

    pub fn new(
        project_options: &PythonProject,
        file_index: FileIndex,
        file_entry: &FileEntry,
        tree: Tree,
    ) -> Self {
        let is_stub = file_entry.name.ends_with(".pyi");
        let issues = Diagnostics::default();
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
            file_entry,
            &issues,
            tree.mypy_inline_config_directives(),
        );
        ignore_type_errors |= match &directives_info.flags {
            Some(flags) => flags.ignore_errors,
            None => project_options.flags.ignore_errors,
        };

        if !ignore_type_errors && let Some(issue) = add_error_if_typeshed_is_overwritten(file_entry)
        {
            let result =
                issues.add_if_not_ignored(Issue::from_node_index(&tree, 0, issue, false), None);
            debug_assert!(result.is_ok());
        }
        let points = Points::new(tree.length());
        Self::new_internal(
            file_index,
            tree,
            points,
            issues,
            is_stub,
            directives_info.flags,
            project_options,
            ignore_type_errors,
        )
    }

    fn new_internal(
        file_index: FileIndex,
        tree: Tree,
        points: Points,
        issues: Diagnostics,
        is_stub: bool,
        flags: Option<TypeCheckerFlags>,
        project: &PythonProject,
        ignore_type_errors: bool,
    ) -> Self {
        let flags = flags.map(|flags| flags.finalize());
        let complex_points = Default::default();
        let star_imports: RefCell<Vec<StarImport>> = Default::default();
        let all_imports: RefCell<Vec<FileImport>> = Default::default();
        let symbol_table = NameBinder::with_global_binder(
            DbInfos {
                // TODO this does not use flags of the super file. Is this an issue?
                settings: &project.settings,
                flags: flags.as_ref().unwrap_or(&project.flags),
                tree: &tree,
                points: &points,
                complex_points: &complex_points,
                issues: &issues,
                star_imports: &star_imports,
                all_imports: &all_imports,
                file_index,
                is_stub,
            },
            |binder| binder.index_file(tree.root()),
        );
        Self {
            tree,
            file_index,
            symbol_table,
            maybe_dunder_all: OnceLock::default(),
            points,
            complex_points,
            star_imports: star_imports.into_inner().into_boxed_slice(),
            all_imports: all_imports.into_inner().into_boxed_slice(),
            issues,
            newline_indices: NewlineIndices::new(),
            sub_files: Default::default(),
            super_file: None,
            stub_cache: is_stub.then(StubCache::default),
            ignore_type_errors,
            flags,
            delayed_diagnostics: Default::default(),
        }
    }

    pub fn inference<'file, 'i_s>(
        &'file self,
        i_s: &'i_s InferenceState<'db, 'i_s>,
    ) -> Inference<'db, 'file, 'i_s> {
        Inference(self.name_resolution_for_inference(i_s))
    }

    pub fn name_resolution_for_inference<'file, 'i_s>(
        &'file self,
        i_s: &'i_s InferenceState<'db, 'i_s>,
    ) -> NameResolution<'db, 'file, 'i_s> {
        NameResolution {
            file: self,
            i_s,
            stop_on_assignments: false,
        }
    }

    pub fn name_resolution_for_types<'file, 'i_s>(
        &'file self,
        i_s: &'i_s InferenceState<'db, 'i_s>,
    ) -> NameResolution<'db, 'file, 'i_s> {
        NameResolution {
            file: self,
            i_s,
            stop_on_assignments: true,
        }
    }

    pub fn lookup_symbol(&self, name: &str) -> Option<NodeRef<'_>> {
        self.symbol_table
            .lookup_symbol(name)
            .map(|node_index| NodeRef::new(self, node_index))
    }

    pub fn lookup(
        &self,
        db: &Database,
        add_issue: impl Fn(IssueKind) -> bool,
        name: &str,
    ) -> LookupResult {
        let i_s = &InferenceState::new(db, self);
        let inference = self.inference(i_s);
        if let Some((pr, redirect_to)) = inference.resolve_module_access(name, &add_issue) {
            let inf = inference.infer_module_point_resolution(pr, add_issue);
            match redirect_to {
                Some(ModuleAccessDetail::OnName(name)) => LookupResult::GotoName { inf, name },
                Some(ModuleAccessDetail::OnFile(file_index)) => {
                    LookupResult::FileReference(file_index)
                }
                None => LookupResult::UnknownName(inf),
            }
        } else {
            LookupResult::None
        }
    }

    pub fn file_entry_and_is_package(&self, db: &'db Database) -> (&'db Arc<FileEntry>, bool) {
        let entry = self.file_entry(db);
        (entry, is_package_name(entry))
    }

    pub fn ensure_calculated_diagnostics(&self, db: &Database) -> Result<(), ()> {
        self.inference(&InferenceState::new(db, self))
            .calculate_module_diagnostics()
    }

    pub fn ensure_module_symbols_flow_analysis(&self, db: &Database) -> Result<(), ()> {
        self.inference(&InferenceState::new(db, self))
            .ensure_module_symbols_flow_analysis()
    }

    pub(super) fn ensure_annotation_or_type_comment_file(
        &self,
        db: &'db Database,
        start: CodeIndex,
        mut code: Cow<str>,
    ) -> &'db Self {
        if let Some(sub_file_index) = self.sub_files.lookup_sub_file_at_position(start) {
            return db.loaded_python_file(sub_file_index);
        }
        if code.contains('\n') {
            // TODO this is a bit hacky, but will probably be good enough for all cases.
            // The parser currently is a bit weird and
            code = Cow::Owned(code.replace('\n', " "));
        }
        let tree = Tree::parse(code.into_owned().into_boxed_str());
        let points = Points::new(tree.length());
        let f = db.load_sub_file(self, |file_index| {
            let mut file = PythonFile::new_internal(
                file_index,
                tree,
                points,
                Diagnostics::default(),
                self.is_stub(),
                None,
                &db.project,
                self.ignore_type_errors,
            );
            file.super_file = Some(SuperFile {
                file: self.file_index,
                offset: Some(start),
            });
            file
        });
        // TODO just saving this in the cache and forgetting about it is a bad idea
        self.sub_files
            .save_sub_file_at_position(start, f.file_index);
        f
    }
    pub(super) fn ensure_forward_reference_file(
        &self,
        db: &'db Database,
        mut start: CodeIndex,
        code: Cow<str>,
    ) -> &'db Self {
        let maybe_new = code.trim_start();
        let whitespace_in_beginning = code.len() - maybe_new.len();
        if whitespace_in_beginning > 0 {
            start += whitespace_in_beginning as CodeIndex;
            self.ensure_annotation_or_type_comment_file(db, start, Cow::Borrowed(maybe_new))
        } else {
            self.ensure_annotation_or_type_comment_file(db, start, code)
        }
    }

    #[inline]
    pub fn is_stub(&self) -> bool {
        self.stub_cache.is_some()
    }

    pub fn normal_file_of_stub_file(&self, db: &'db Database) -> Option<&'db PythonFile> {
        let stub_cache = self.stub_cache.as_ref()?;
        let file_index = *stub_cache.non_stub.get_or_init(|| {
            let file_entry = self.file_entry(db);
            let (name, parent_dir) = name_and_parent_dir(file_entry, false);
            if let Some(py_name) = file_entry.name.strip_suffix("i")
                && let Some(file_entry) = file_entry.parent.with_entries(&db.vfs, |entries| {
                    match &*entries.search(py_name)? {
                        DirectoryEntry::File(f) => Some(f.clone()),
                        _ => None,
                    }
                })
            {
                return db.load_file_index_from_workspace(&file_entry, false);
            }
            match ImportResult::import_non_stub_for_stub_package(db, self, parent_dir, name)? {
                ImportResult::File(file_index) => {
                    assert_ne!(file_index, self.file_index);
                    Some(file_index)
                }
                ImportResult::Namespace(_) => None,
                ImportResult::PyTypedMissing => unreachable!(),
            }
        });
        db.ensure_file_for_file_index(file_index?).ok()
    }

    pub fn stub_file_of_normal_file(&self, db: &'db Database) -> Option<&'db PythonFile> {
        if self.is_stub() {
            return None;
        }
        let file_entry = self.file_entry(db);
        let (name, parent_dir) = name_and_parent_dir(file_entry, false);
        let py_name = format!("{}.pyi", file_entry.name.strip_suffix(".py")?);
        let file_index = if let Some(file_entry) =
            file_entry
                .parent
                .with_entries(&db.vfs, |entries| match &*entries.search(&py_name)? {
                    DirectoryEntry::File(f) => Some(f.clone()),
                    _ => None,
                }) {
            db.load_file_index_from_workspace(&file_entry, false)?
        } else {
            match ImportResult::import_stub_for_non_stub_package(db, self, parent_dir, name)? {
                ImportResult::File(file_index) => file_index,
                ImportResult::Namespace(_) => return None,
                ImportResult::PyTypedMissing => unreachable!(),
            }
        };
        let loaded = db.ensure_file_for_file_index(file_index).ok()?;
        if !loaded.is_stub() {
            return None;
        }
        assert_ne!(file_index, self.file_index);
        Some(loaded)
    }

    pub fn maybe_dunder_all(&self, db: &Database) -> Option<&[DbString]> {
        self.maybe_dunder_all
            .get_or_init(|| {
                self.symbol_table
                    .lookup_symbol("__all__")
                    .and_then(|dunder_all_index| {
                        let name_def = NodeRef::new(self, dunder_all_index)
                            .expect_name()
                            .name_def()
                            .unwrap();
                        if let Some((_, _, expr)) =
                            name_def
                                .maybe_assignment_definition()
                                .and_then(|assignment| {
                                    assignment.maybe_simple_type_expression_assignment()
                                })
                        {
                            let base = maybe_dunder_all_names(vec![], self.file_index, expr)?;
                            self.gather_dunder_all_modifications(db, dunder_all_index, base)
                        } else if let Some(NameImportParent::ImportFromAsName(as_name)) =
                            name_def.maybe_import()
                        {
                            let i_s = InferenceState::new(db, self);
                            let inference = self.inference(&i_s);
                            inference.infer_name_def(name_def);
                            // Just take the __all__ from the now calculated file. The exact
                            // position doesn't matter anymore, because that is calculated by
                            // exactly this method.
                            let name_def_point =
                                NodeRef::new(self, as_name.name_def().index()).point();
                            let base = name_def_point
                                .as_redirected_node_ref(db)
                                .file
                                .maybe_dunder_all(db)?;
                            self.gather_dunder_all_modifications(db, dunder_all_index, base.into())
                        } else {
                            None
                        }
                    })
            })
            .as_deref()
    }

    pub fn is_name_exported_for_star_import(&self, db: &Database, name: &str) -> bool {
        if let Some(dunder) = self.maybe_dunder_all(db) {
            // Name not in __all__
            if !dunder.iter().any(|x| x.as_str(db) == name) {
                debug!(
                    "Name {name} found in star imports of {}, but it's not in __all__",
                    self.file_path(db)
                );
                return false;
            }
        } else if name.starts_with('_') {
            return false;
        }
        true
    }

    fn gather_dunder_all_modifications(
        &self,
        db: &Database,
        dunder_all_index: NodeIndex,
        mut dunder_all: Vec<DbString>,
    ) -> Option<Box<[DbString]>> {
        let file_index = self.file_index;
        let check_multi_def = |dunder_all: Vec<DbString>, name: Name| -> Option<Vec<DbString>> {
            let name_def = name.name_def().unwrap();
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
            if let Some(primary) = name.maybe_atom_of_primary()
                && let PrimaryParent::Primary(maybe_call) = primary.parent()
                && let PrimaryContent::Execution(arg_details) = maybe_call.second()
                && let PrimaryContent::Attribute(attr) = primary.second()
            {
                let maybe_single = arg_details.maybe_single_positional();
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
                        );
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
            Some(dunder_all)
        };
        let p = self.points.get(dunder_all_index);
        if p.calculated() && p.maybe_specific() == Some(Specific::FirstNameOfNameDef) {
            for index in OtherDefinitionIterator::new(&self.points, dunder_all_index) {
                let name = NodeRef::new(self, index as NodeIndex).expect_name();
                dunder_all = check_multi_def(dunder_all, name)?
            }
        }
        for (index, point) in self.points.iter().enumerate() {
            if point.maybe_redirect_to(PointLink::new(file_index, dunder_all_index))
                && let Some(name) = NodeRef::new(self, index as NodeIndex).maybe_name()
            {
                dunder_all = check_ref(dunder_all, name)?
            }
        }
        Some(dunder_all.into())
    }

    pub fn file_entry(&self, db: &'db Database) -> &'db Arc<FileEntry> {
        db.vfs.file_entry(self.file_index)
    }

    pub fn file_path_with_scheme(&self, db: &'db Database) -> &'db PathWithScheme {
        db.vfs.file_path(self.file_index)
    }

    /// Returns false if the issue was not added
    pub fn add_issue(&self, i_s: &InferenceState, issue: Issue) -> bool {
        if !i_s.should_add_issue() || issue.kind.is_disabled(i_s.flags()) {
            let config = DiagnosticConfig {
                show_column_numbers: true,
                ..Default::default()
            };
            debug!(
                "Did ignore issue for now: {}",
                Diagnostic::new(i_s.db, self, &issue).as_string(&config, None)
            );
            return false;
        }
        self.add_issue_without_checking_for_disabled_error_codes(i_s.db, issue)
    }

    pub fn is_from_django(&self, db: &Database) -> bool {
        self.file_entry(db)
            .parent
            .most_outer_dir()
            .is_some_and(|dir| *dir.name == *"django-stubs")
    }

    /// Returns false if the issue was not added
    pub fn add_issue_without_checking_for_disabled_error_codes(
        &self,
        db: &'db Database,
        issue: Issue,
    ) -> bool {
        // This function adds issues in all normal cases and does not respect the InferenceState
        // mode.
        if self.ignore_type_errors {
            return false;
        }
        let (file, add) = match self.super_file {
            Some(super_file) if super_file.is_part_of_parent() => (
                db.loaded_python_file(super_file.file),
                super_file.offset.unwrap_or(0),
            ),
            _ => (self, 0),
        };
        let maybe_ignored = file
            .tree
            .type_ignore_comment_for(issue.start_position + add, issue.end_position + add);
        let config = DiagnosticConfig {
            show_column_numbers: true,
            ..Default::default()
        };
        let result = self.issues.add_if_not_ignored(issue, maybe_ignored);
        match &result {
            Ok(issue) => debug!(
                "NEW ISSUE: {}",
                Diagnostic::new(db, self, issue).as_string(&config, None)
            ),
            Err(issue) => debug!(
                "New ignored issue: {}",
                Diagnostic::new(db, self, &issue).as_string(&config, None)
            ),
        }
        result.is_ok()
    }

    pub(crate) fn name_and_parent_dir(
        &self,
        db: &'db Database,
    ) -> (&'db str, Option<Arc<Directory>>) {
        name_and_parent_dir(self.file_entry(db), true)
    }

    pub fn qualified_name(&self, db: &Database) -> String {
        let (name, parent_dir) = self.name_and_parent_dir(db);
        if let Some(parent_dir) = parent_dir {
            dotted_path_from_dir(&parent_dir) + "." + name
        } else {
            name.strip_suffix(STUBS_SUFFIX).unwrap_or(name).to_string()
        }
    }

    pub fn name(&self, db: &'db Database) -> &'db str {
        let (name, _) = self.name_and_parent_dir(db);
        name.strip_suffix(STUBS_SUFFIX).unwrap_or(name)
    }

    pub fn flags<'x>(&'x self, db: &'x Database) -> &'x FinalizedTypeCheckerFlags {
        self.maybe_more_specific_flags(db)
            .unwrap_or(&db.project.flags)
    }

    pub fn maybe_more_specific_flags<'x>(
        &'x self,
        db: &'x Database,
    ) -> Option<&'x FinalizedTypeCheckerFlags> {
        if let Some(super_file) = self.super_file {
            debug_assert!(self.flags.is_none());
            super_file.file(db).maybe_more_specific_flags(db)
        } else {
            self.flags.as_ref()
        }
    }

    pub fn has_unsupported_class_scoped_import(&self, db: &Database) -> bool {
        let i_s = &InferenceState::new(db, self);
        self.symbol_table.iter().any(|(_, index)| {
            NodeRef::new(self, *index)
                .infer_name_of_definition_by_index(i_s)
                .as_cow_type(i_s)
                .is_func_or_overload()
        }) || self.star_imports.iter().any(|star_import| {
            star_import.in_module_scope()
                && self
                    .star_import_file(db, star_import)
                    .is_some_and(|file| file.has_unsupported_class_scoped_import(db))
        })
    }

    pub fn original_file(&'db self, db: &'db Database) -> &'db Self {
        match self.super_file {
            Some(super_file) if super_file.is_part_of_parent() => {
                db.loaded_python_file(super_file.file).original_file(db)
            }
            _ => self,
        }
    }

    pub fn process_delayed_diagnostics(&self, db: &Database) {
        loop {
            let delayed = std::mem::take(&mut *self.delayed_diagnostics.write().unwrap());
            if delayed.is_empty() {
                break;
            }
            FLOW_ANALYSIS.with(|fa| fa.process_delayed_diagnostics(db, delayed));
        }
    }

    pub fn lines_context_around_range(
        &'db self,
        db: &'db Database,
        line_range: Range<usize>,
        add_lines_at_start_and_end: usize,
    ) -> impl Iterator<Item = (usize, &'db str)> {
        let from_line: usize = (line_range.start as isize - add_lines_at_start_and_end as isize)
            .try_into()
            .unwrap_or_default();
        let file = self.original_file(db);
        file.newline_indices
            .numbers_with_lines(file.tree.code(), from_line)
            .take(line_range.len() + 1 + 2 * add_lines_at_start_and_end)
    }
}

pub fn dotted_path_from_dir(dir: &Directory) -> String {
    if let Ok(parent_dir) = dir.parent.maybe_dir() {
        dotted_path_from_dir(&parent_dir) + "." + &dir.name
    } else {
        let n = &dir.name;
        n.strip_suffix(STUBS_SUFFIX).unwrap_or(n).to_string()
    }
}

fn name_and_parent_dir(entry: &FileEntry, skip_stubs: bool) -> (&str, Option<Arc<Directory>>) {
    let name = &entry.name;
    let name = name
        .strip_suffix(".py")
        .or_else(|| name.strip_suffix(".pyi"))
        .unwrap_or(name);
    if name == "__init__"
        && let Ok(dir) = entry.parent.maybe_dir()
    {
        // It's ok to transmute here, because dir.name will exist as the database is
        // non-mutable, which should be fine.
        let mut dir_name = unsafe { std::mem::transmute::<&str, &str>(dir.name.as_ref()) };
        if skip_stubs {
            dir_name = dir_name.strip_suffix("-stubs").unwrap_or(dir_name);
        }
        return (dir_name, dir.parent.maybe_dir().ok());
    }
    (name, entry.parent.maybe_dir().ok())
}

fn info_from_directives<'x>(
    project: &PythonProject,
    file_entry: &FileEntry,
    issues: &Diagnostics,
    directives: impl Iterator<Item = (CodeIndex, &'x str)>,
) -> DirectivesInfos {
    // Directives like `# mypy: disallow-any-generics`
    let mut flags = None;

    if !project.overrides.is_empty() {
        let (name, parent_dir) = name_and_parent_dir(file_entry, true);
        for override_ in &project.overrides {
            if override_
                .module
                .matches_file_path(name, parent_dir.as_deref())
            {
                if flags.is_none() {
                    flags = Some(project.flags.clone().into_unfinalized());
                }
                override_
                    .apply_to_flags(flags.as_mut().unwrap())
                    .expect("Issues with loading config overrides, TODO need better error");
            }
        }
    }

    for (start_position, rest) in directives {
        let splitter = DirectiveSplitter {
            issues,
            rest,
            start_position,
        };
        for (name, value) in splitter {
            let name = name.replace('-', "_");
            if flags.is_none() {
                flags = Some(project.flags.clone().into_unfinalized());
            }
            let mut check = || -> anyhow::Result<_> {
                let value = match value {
                    Some(value) => IniOrTomlValue::Ini(value),
                    None => IniOrTomlValue::InlineConfigNoValue,
                };
                set_flag(flags.as_mut().unwrap(), &name, value, true)?;
                Ok(())
            };
            if let Err(err) = check() {
                issues
                    .add_if_not_ignored(
                        Issue::from_start_stop(
                            start_position,
                            start_position + rest.len() as CodeIndex,
                            IssueKind::DirectiveSyntaxError(err.to_string().into()),
                        ),
                        None,
                    )
                    .ok();
            }
        }
    }
    DirectivesInfos { flags }
}

struct DirectivesInfos {
    flags: Option<TypeCheckerFlags>,
}

struct DirectiveSplitter<'db, 'code> {
    issues: &'db Diagnostics,
    rest: &'code str,
    start_position: CodeIndex,
}

impl<'code> Iterator for DirectiveSplitter<'_, 'code> {
    type Item = (&'code str, Option<&'code str>);
    fn next(&mut self) -> Option<Self::Item> {
        let split_name_value =
            |start_position: CodeIndex, directive: &'code str, had_quotation_marks: bool| {
                let (name, value) = if let Some((first, second)) = directive.split_once('=') {
                    let mut second = second.trim();
                    if had_quotation_marks {
                        if second.chars().next().is_some_and(|first| first == '"')
                            && second.chars().last().is_some_and(|last| last == '"')
                        {
                            second = &second[1..second.len() - 1];
                        } else {
                            self.issues
                                .add_if_not_ignored(
                                    Issue::from_start_stop(
                                        start_position - 1,
                                        start_position,
                                        IssueKind::DirectiveSyntaxError(
                                            "Content after quote in configuration comment".into(),
                                        ),
                                    ),
                                    None,
                                )
                                .ok();
                            second = &second[1..];
                        }
                    }
                    (first.trim(), Some(second))
                } else {
                    (directive.trim(), None)
                };
                if name.contains('"') {
                    self.issues
                        .add_if_not_ignored(
                            Issue::from_start_stop(
                                start_position - 1,
                                start_position,
                                IssueKind::DirectiveSyntaxError(
                                    "Quotes should not be part of the key".into(),
                                ),
                            ),
                            None,
                        )
                        .ok();
                }
                Some((name, value))
            };
        let mut opened_quotation_mark = false;
        let mut had_quotation_marks = false;
        for (i, n) in self.rest.bytes().enumerate() {
            if opened_quotation_mark {
                if n == b'"' {
                    opened_quotation_mark = false;
                }
            } else if n == b'"' {
                opened_quotation_mark = true;
                had_quotation_marks = true;
            } else if n == b',' {
                self.start_position += i as CodeIndex;
                let result = &self.rest[..i];
                self.rest = &self.rest[i + 1..];
                return split_name_value(self.start_position, result, had_quotation_marks);
            }
        }
        if opened_quotation_mark {
            self.issues
                .add_if_not_ignored(
                    Issue::from_start_stop(
                        self.start_position,
                        self.start_position + self.rest.len() as CodeIndex,
                        IssueKind::DirectiveSyntaxError(
                            "Unterminated quote in configuration comment".into(),
                        ),
                    ),
                    None,
                )
                .ok();
        } else {
            let rest = self.rest.trim();
            if !rest.is_empty() {
                self.rest = "";
                return split_name_value(self.start_position, rest, had_quotation_marks);
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

// An Iterator that goes through all nodes except the given one
pub(crate) struct OtherDefinitionIterator<'a> {
    points: &'a Points,
    start: NodeIndex,
    current: NodeIndex,
}

impl<'a> OtherDefinitionIterator<'a> {
    pub fn new(points: &'a Points, start: NodeIndex) -> Self {
        debug_assert!(points.get(start).is_name_of_name_def_like());
        Self {
            points,
            start,
            current: start,
        }
    }

    pub fn is_single_definition(mut self) -> bool {
        self.next().is_none()
    }
}

impl Iterator for OtherDefinitionIterator<'_> {
    type Item = NodeIndex;

    fn next(&mut self) -> Option<Self::Item> {
        let p = self.points.get(self.current);
        debug_assert!(p.is_name_of_name_def_like(), "{p:?}");
        let next = p.node_index();
        if next == self.start {
            None
        } else {
            self.current = next;
            Some(next)
        }
    }
}

#[derive(Clone, Default)]
struct StubCache {
    non_stub: OnceLock<Option<FileIndex>>,
}

fn add_error_if_typeshed_is_overwritten(file_entry: &FileEntry) -> Option<IssueKind> {
    let is_err = || {
        if *file_entry.name == *"typing.pyi"
            && let Ok(workspace) = file_entry.parent.maybe_workspace()
            && workspace.kind != WorkspaceKind::Typeshed
        {
            true
        } else if *file_entry.name == *"__init__.pyi"
            && let Ok(dir) = file_entry.parent.maybe_dir()
            && *dir.name == *"typing"
            && let Ok(workspace) = dir.parent.maybe_workspace()
            && workspace.kind != WorkspaceKind::Typeshed
        {
            true
        } else {
            false
        }
    };
    is_err().then_some(IssueKind::InvalidShadowingOfTypeshedModule { module: "typing" })
}
