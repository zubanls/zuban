use std::{
    cell::{OnceCell, RefCell},
    collections::HashMap,
    fmt,
    rc::Rc,
};

use parsa_python_cst::*;

use super::{
    file_state::{File, Leaf},
    inference::Inference,
    name_binder::{DbInfos, NameBinder},
};
use crate::{
    config::{set_flag_and_return_ignore_errors, IniOrTomlValue, OverrideConfig},
    database::{
        ComplexPoint, Database, FileIndex, Locality, LocalityLink, Point, PointLink, Points,
        PythonProject, Specific,
    },
    debug,
    diagnostics::{Diagnostic, DiagnosticConfig, Diagnostics, Issue, IssueKind},
    imports::{ImportResult, STUBS_SUFFIX},
    inference_state::InferenceState,
    inferred::Inferred,
    lines::NewlineIndices,
    matching::ResultContext,
    name::{FilePosition, Names, TreeName},
    node_ref::NodeRef,
    type_::DbString,
    utils::{InsertOnlyVec, SymbolTable},
    workspaces::{Directory, DirectoryEntry, FileEntry},
    TypeCheckerFlags,
};

#[derive(Default, Debug, Clone)]
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

    pub fn clear(&mut self) {
        self.0.clear()
    }
}

#[derive(Clone)]
pub struct PythonFile {
    pub tree: Tree, // TODO should probably not be public
    pub symbol_table: SymbolTable,
    maybe_dunder_all: OnceCell<Option<Box<[DbString]>>>, // For __all__
    //all_names_bloom_filter: Option<BloomFilter<&str>>,
    pub points: Points,
    pub complex_points: ComplexValues,
    pub file_index: FileIndex,
    pub issues: Diagnostics,
    pub star_imports: Box<[StarImport]>,
    sub_files: RefCell<HashMap<CodeIndex, FileIndex>>,
    pub(crate) super_file: Option<FileIndex>,
    stub_cache: Option<StubCache>,
    pub ignore_type_errors: bool,
    flags: Option<TypeCheckerFlags>,

    newline_indices: NewlineIndices,
}

impl File for PythonFile {
    fn implementation<'db>(&self, _names: Names<'db>) -> Names<'db> {
        unimplemented!()
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
        unimplemented!()
    }

    fn file_index(&self) -> FileIndex {
        self.file_index
    }

    fn code(&self) -> &str {
        self.tree.code()
    }

    fn node_start_position(&self, n: NodeIndex) -> FilePosition {
        FilePosition::new(self, self.tree.node_start_position(n))
    }

    fn node_end_position(&self, n: NodeIndex) -> FilePosition {
        FilePosition::new(self, self.tree.node_end_position(n))
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
            let result = self.inference(&i_s).calculate_diagnostics();
            debug_assert!(result.is_ok());
        }
        let flags = self.flags(db);
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
        if let Some(cache) = self.stub_cache.as_mut() {
            *cache = StubCache::default();
        }
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
            self.flags.take(),
            project,
            self.ignore_type_errors,
        );
    }

    fn has_super_file(&self) -> bool {
        self.super_file.is_some()
    }
}

#[derive(Debug, Clone)]
pub struct StarImport {
    pub scope: NodeIndex,
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
    pub fn from_path_and_code(
        project: &PythonProject,
        file_index: FileIndex,
        file_entry: &FileEntry,
        path: &str,
        code: Box<str>,
    ) -> Self {
        debug!("Initialize {path} ({file_index})");
        let is_stub = path.ends_with(".pyi");
        PythonFile::new(project, file_index, &file_entry, code, is_stub)
    }

    pub fn new(
        project_options: &PythonProject,
        file_index: FileIndex,
        file_entry: &FileEntry,
        code: Box<str>,
        is_stub: bool,
    ) -> Self {
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
            file_entry,
            &issues,
            tree.mypy_inline_config_directives(),
        );
        ignore_type_errors |= directives_info.ignore_errors;
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
        let complex_points = Default::default();
        let star_imports: RefCell<Vec<StarImport>> = Default::default();
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
                file_index,
                is_stub,
            },
            |binder| binder.index_file(tree.root()),
        );
        Self {
            tree,
            file_index,
            symbol_table,
            maybe_dunder_all: OnceCell::default(),
            points,
            complex_points,
            star_imports: star_imports.into_inner().into_boxed_slice(),
            issues,
            newline_indices: NewlineIndices::new(),
            sub_files: Default::default(),
            super_file: None,
            stub_cache: is_stub.then(StubCache::default),
            ignore_type_errors,
            flags,
        }
    }

    pub fn inference<'file, 'i_s>(
        &'file self,
        i_s: &'i_s InferenceState<'db, 'i_s>,
    ) -> Inference<'db, 'file, 'i_s> {
        Inference { file: self, i_s }
    }

    pub fn lookup_global(&self, name: &str) -> Option<LocalityLink> {
        self.symbol_table
            .lookup_symbol(name)
            .map(|node_index| LocalityLink {
                file: self.file_index,
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
        let tree = Tree::parse(Box::from(code.into_string() + "\n"));
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
            file.super_file = Some(self.file_index);
            file
        });
        // TODO just saving this in the cache and forgetting about it is a bad idea
        self.sub_files.borrow_mut().insert(start, f.file_index);
        f
    }

    pub fn is_stub_or_in_protocol(&self, i_s: &InferenceState) -> bool {
        if let Some(current_class) = i_s.current_class() {
            if current_class.is_protocol(i_s.db) {
                return true;
            }
        }
        self.is_stub()
    }

    #[inline]
    pub fn is_stub(&self) -> bool {
        self.stub_cache.is_some()
    }

    pub fn in_partial_stubs(&self, db: &Database) -> bool {
        self.stub_cache.as_ref().is_some_and(|cache| {
            *cache.partial.get_or_init(|| {
                let Some(dir) = self.file_entry(db).parent.most_outer_dir() else {
                    return false;
                };
                if !dir.name.ends_with(STUBS_SUFFIX) {
                    // partial is only relevant for -stubs, otherwise we don't really care.
                    return false;
                }
                dir.search("py.typed").is_some_and(|entry| match &*entry {
                    // TODO we are currently never invalidating this file, when it changes
                    DirectoryEntry::File(entry) => db
                        .vfs
                        .read_file(&entry.path(db.vfs.as_ref()))
                        .is_ok_and(|code| code.contains("partial\n")),
                    _ => false,
                })
            })
        })
    }

    pub fn normal_file_of_stub_file(&self, db: &'db Database) -> Option<&'db PythonFile> {
        let stub_cache = self.stub_cache.as_ref()?;
        let file_index = *stub_cache.non_stub.get_or_init(|| {
            let (name, parent_dir) = name_and_parent_dir(self.file_entry(db), false);
            match ImportResult::import_non_stub_for_stub_package(
                db,
                self.file_index,
                parent_dir,
                name,
            )? {
                ImportResult::File(file_index) => {
                    assert_ne!(file_index, self.file_index);
                    Some(file_index)
                }
                ImportResult::Namespace(_) => None,
                ImportResult::PyTypedMissing => unreachable!(),
            }
        });
        Some(db.loaded_python_file(file_index?))
    }

    pub fn maybe_dunder_all(&self, db: &Database) -> Option<&[DbString]> {
        self.maybe_dunder_all
            .get_or_init(|| {
                self.symbol_table
                    .lookup_symbol("__all__")
                    .and_then(|dunder_all_index| {
                        let name_def = NodeRef::new(self, dunder_all_index)
                            .as_name()
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
                            let i_s = InferenceState::new(db);
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
        if p.calculated() && p.maybe_specific() == Some(Specific::NameOfNameDef) {
            for index in MultiDefinitionIterator::new(&self.points, dunder_all_index) {
                let name = NodeRef::new(self, index as NodeIndex).as_name();
                dunder_all = check_multi_def(dunder_all, name)?
            }
        }
        for (index, point) in self.points.iter().enumerate() {
            if point.maybe_redirect_to(PointLink::new(file_index, dunder_all_index)) {
                if let Some(name) = NodeRef::new(self, index as NodeIndex).maybe_name() {
                    dunder_all = check_ref(dunder_all, name)?
                }
            }
        }
        Some(dunder_all.into())
    }

    pub fn file_entry(&self, db: &'db Database) -> &'db Rc<FileEntry> {
        db.file_state(self.file_index).file_entry()
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

    pub(crate) fn name_and_parent_dir(
        &self,
        db: &'db Database,
    ) -> (&'db str, Option<Rc<Directory>>) {
        name_and_parent_dir(self.file_entry(db), true)
    }

    pub fn qualified_name(&self, db: &Database) -> String {
        let (name, parent_dir) = name_and_parent_dir(self.file_entry(db), true);
        if let Some(parent_dir) = parent_dir {
            dotted_path_from_dir(&parent_dir) + "." + name
        } else {
            name.strip_suffix(STUBS_SUFFIX).unwrap_or(name).to_string()
        }
    }

    pub fn flags<'x>(&'x self, db: &'x Database) -> &'x TypeCheckerFlags {
        if let Some(super_file) = self.super_file {
            debug_assert!(self.flags.is_none());
            db.loaded_python_file(super_file).flags(db)
        } else {
            self.flags.as_ref().unwrap_or(&db.project.flags)
        }
    }

    pub fn has_unsupported_class_scoped_import(&self, db: &Database) -> bool {
        let i_s = &InferenceState::new(db);
        let inference = self.inference(i_s);
        self.symbol_table.iter().any(|(_, index)| {
            inference
                .infer_name_of_definition_by_index(*index)
                .as_cow_type(i_s)
                .is_func_or_overload()
        }) || self.star_imports.iter().any(|star_import| {
            star_import.in_module_scope()
                && star_import
                    .to_file(&inference)
                    .is_some_and(|file| file.has_unsupported_class_scoped_import(db))
        })
    }
}

pub fn dotted_path_from_dir(dir: &Directory) -> String {
    if let Ok(parent_dir) = dir.parent.maybe_dir() {
        dotted_path_from_dir(&parent_dir) + "." + &dir.name
    } else {
        dir.name.to_string()
    }
}

fn name_and_parent_dir(entry: &FileEntry, skip_stubs: bool) -> (&str, Option<Rc<Directory>>) {
    let name = &entry.name;
    let name = name
        .strip_suffix(".py")
        .or_else(|| name.strip_suffix(".pyi"))
        .unwrap_or(name);
    if name == "__init__" {
        if let Ok(dir) = entry.parent.maybe_dir() {
            // It's ok to transmute here, because dir.name will exist as the database is
            // non-mutable, which should be fine.
            let mut dir_name = unsafe { std::mem::transmute::<&str, &str>(dir.name.as_ref()) };
            if skip_stubs {
                dir_name = dir_name.strip_suffix("-stubs").unwrap_or(dir_name);
            }
            return (dir_name, dir.parent.maybe_dir().ok());
        }
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
    let mut ignore_errors = false;
    let mut flags = None;

    if !project.overrides.is_empty() {
        let (name, parent_dir) = name_and_parent_dir(file_entry, true);
        for override_ in &project.overrides {
            if override_config_matches_file_path(override_, name, parent_dir.as_deref()) {
                if flags.is_none() {
                    flags = Some(project.flags.clone());
                }
                ignore_errors |= override_
                    .apply_to_flags_and_return_ignore_errors(flags.as_mut().unwrap())
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
                flags = Some(project.flags.clone());
            }
            let mut check = || -> anyhow::Result<_> {
                let value = match value {
                    Some(value) => IniOrTomlValue::Ini(value),
                    None => IniOrTomlValue::InlineConfigNoValue,
                };
                ignore_errors |=
                    set_flag_and_return_ignore_errors(flags.as_mut().unwrap(), &name, value)?;
                Ok(())
            };
            if let Err(err) = check() {
                issues
                    .add_if_not_ignored(
                        Issue {
                            kind: IssueKind::DirectiveSyntaxError(err.to_string().into()),
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

pub fn override_config_matches_file_path(
    config: &OverrideConfig,
    name: &str,
    parent_dir: Option<&Directory>,
) -> bool {
    fn parent_count(dir: Option<&Directory>) -> usize {
        if let Some(dir) = dir {
            parent_count(dir.parent.maybe_dir().ok().as_deref()) + 1
        } else {
            0
        }
    }
    fn nth_parent<'x>(name: &'x str, dir: Option<&Directory>, n: usize) -> &'x str {
        if n == 0 {
            name
        } else {
            let dir = dir.unwrap();
            nth_parent(
                // This transmute is fine, because we're only local and the parents will not
                // change during the parent function.
                unsafe { std::mem::transmute::<&str, &str>(dir.name.as_ref()) },
                dir.parent.maybe_dir().ok().as_deref(),
                n - 1,
            )
        }
    }
    let actual_path_count = parent_count(parent_dir) + 1;
    if actual_path_count != config.module.path.len() && !config.module.star
        || config.module.path.len() > actual_path_count
    {
        return false;
    }
    for (i, override_part) in config.module.path.iter().enumerate() {
        if override_part.as_ref() != nth_parent(name, parent_dir, actual_path_count - i - 1) {
            return false;
        }
    }
    true
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
                                    Issue {
                                        kind: IssueKind::DirectiveSyntaxError(
                                            "Content after quote in configuration comment".into(),
                                        ),
                                        start_position: start_position - 1,
                                        end_position: start_position,
                                    },
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
                            Issue {
                                kind: IssueKind::DirectiveSyntaxError(
                                    "Quotes should not be part of the key".into(),
                                ),
                                start_position: start_position - 1,
                                end_position: start_position,
                            },
                            None,
                        )
                        .ok();
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
                return split_name_value(self.start_position, result, had_quotation_marks);
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

pub struct MultiDefinitionIterator<'a> {
    points: &'a Points,
    start: NodeIndex,
    current: NodeIndex,
}

impl<'a> MultiDefinitionIterator<'a> {
    pub fn new(points: &'a Points, start: NodeIndex) -> Self {
        debug_assert_eq!(
            points.get(start).maybe_specific(),
            Some(Specific::NameOfNameDef)
        );
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
        debug_assert_eq!(p.maybe_specific(), Some(Specific::NameOfNameDef));
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
    partial: OnceCell<bool>,
    non_stub: OnceCell<Option<FileIndex>>,
}
