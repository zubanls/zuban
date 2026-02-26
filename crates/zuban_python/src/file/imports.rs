use parsa_python_cst::{
    DottedAsName, DottedAsNameContent, DottedImportName, DottedImportNameContent, ImportFrom,
    ImportFromTargets, ImportName, Name, NameImportParent, NodeIndex,
};
use vfs::{Directory, DirectoryEntry, FileEntry, Parent};

use crate::{
    database::{Database, Locality, Point, PointKind, Specific},
    debug,
    diagnostics::IssueKind,
    imports::{
        ImportAncestor, ImportResult, LoadedImportResult, STUBS_SUFFIX, find_import_ancestor,
        global_import, namespace_import_with_unloaded_file, python_import_with_needs_exact_case,
    },
    inference_state::InferenceState,
    inferred::Inferred,
    node_ref::NodeRef,
    type_::{LookupResult, Type},
};

use super::{PythonFile, python_file::StarImport};

impl PythonFile {
    pub(super) fn global_import(&self, db: &Database, name: Name) -> Option<ImportResult> {
        let result = global_import(db, self, name.as_str());
        if let Some(result) = &result {
            debug!(
                "Global import '{}': {:?}",
                name.as_code(),
                result.debug_info(db),
            );
        }
        result
    }

    pub fn cache_import_dotted_name(
        &self,
        db: &Database,
        dotted: DottedImportName,
        base: Option<ImportResult>,
    ) -> Option<ImportResult> {
        let node_ref = NodeRef::new(self, dotted.index());
        let p = node_ref.point();
        if p.calculated() {
            return load_saved_results(node_ref, p);
        }
        let infer_name = |base, name: Name| {
            let mut in_stub_and_has_getattr = false;
            let result = match &base {
                ImportResult::File(file_index) => {
                    let file_entry = db.vfs.file_entry(*file_index);
                    let r = sub_module_import(db, self, file_entry, name.as_code());

                    // This is such weird logic. I don't understand at all why Mypy is doing this.
                    // It seems to come from here:
                    // https://github.com/python/mypy/blob/bc591c756a453bb6a78a31e734b1f0aa475e90e0/mypy/semanal_pass1.py#L87-L96
                    if r.is_none()
                        && db.file_path(*file_index).ends_with(".pyi")
                        && db
                            .ensure_file_for_file_index(*file_index)
                            .is_ok_and(|module| module.lookup_symbol("__getattr__").is_some())
                    {
                        in_stub_and_has_getattr = true
                    }
                    r
                }
                ImportResult::Namespace(namespace) => {
                    namespace_import_with_unloaded_file(db, self, namespace, name.as_str())
                }
                ImportResult::PyTypedMissing => Some(ImportResult::PyTypedMissing),
            };
            if let Some(imported) = &result {
                debug!(
                    "Imported {:?} for {:?}",
                    imported.debug_info(db),
                    dotted.as_code(),
                );
            } else if in_stub_and_has_getattr {
                debug!(
                    "Ignored import of {}, because of a __getattr__ in a stub file",
                    name.as_str()
                );
            } else if !self.flags(db).ignore_missing_imports {
                let module_name = if let Some(base_loaded) = base.ensured_loaded_file(db) {
                    format!("{}.{}", base_loaded.qualified_name(db), name.as_str()).into()
                } else {
                    // TODO this is not correct and weird, but it's probably pretty rare that a
                    // file is deleted but still in the virtual filesystem.
                    dotted.as_code().into()
                };
                NodeRef::new(self, name.index())
                    .add_type_issue(db, IssueKind::ModuleNotFound { module_name });
            }
            result
        };
        let result = match dotted.unpack() {
            DottedImportNameContent::Name(name) => {
                if let Some(base) = base {
                    infer_name(base, name)
                } else {
                    let result = self.global_import(db, name);
                    if result.is_none() {
                        self.add_module_not_found(db, name)
                    }
                    result
                }
            }
            DottedImportNameContent::DottedName(dotted_name, name) => {
                let result = self.cache_import_dotted_name(db, dotted_name, base)?;
                infer_name(result, name)
            }
        };
        cache_import_results(node_ref, &result);
        result
    }

    pub(super) fn infer_dotted_as_name_import(
        &self,
        db: &Database,
        dotted_as_name: DottedAsName,
    ) -> Inferred {
        match self.cache_dotted_as_name_import(db, dotted_as_name) {
            Some(import_result) => import_result.into_inferred(db),
            None => Inferred::new_module_not_found(),
        }
    }

    pub fn cache_dotted_as_name_import(
        &self,
        db: &Database,
        dotted_as_name: DottedAsName,
    ) -> Option<ImportResult> {
        let saved_at = NodeRef::new(self, dotted_as_name.index());
        let point = saved_at.point();
        if point.calculated() {
            return load_saved_results(saved_at, point);
        }
        let result = match dotted_as_name.unpack() {
            DottedAsNameContent::Simple(name_def, rest) => {
                let result = self.global_import(db, name_def.name());
                if result.is_none() {
                    self.add_module_not_found(db, name_def.name())
                }
                if let Some(rest) = rest
                    && result.is_some()
                {
                    self.cache_import_dotted_name(db, rest, result.clone());
                }
                result
            }
            DottedAsNameContent::WithAs(dotted_name, _) => {
                self.cache_import_dotted_name(db, dotted_name, None)
            }
        };
        cache_import_results(saved_at, &result);
        result
    }

    pub(super) fn import_from_first_part(
        &self,
        db: &Database,
        import_from: ImportFrom,
    ) -> Option<LoadedImportResult> {
        self.import_from_first_part_without_loading_file(db, import_from)?
            .ensured_loaded_file(db)
    }

    pub fn import_from_first_part_without_loading_file(
        &self,
        db: &Database,
        import_from: ImportFrom,
    ) -> Option<ImportResult> {
        let (level, dotted_name) = import_from.level_with_dotted_name();
        self.import_from_first_part_calculation_without_loading_file(
            db,
            level,
            dotted_name,
            |issue| NodeRef::new(self, import_from.index()).add_type_issue(db, issue),
        )
    }

    pub fn import_from_first_part_calculation_without_loading_file(
        &self,
        db: &Database,
        level: usize,
        dotted_name: Option<DottedImportName>,
        add_issue: impl FnOnce(IssueKind) -> bool,
    ) -> Option<ImportResult> {
        let maybe_level_file = if level > 0 {
            match find_import_ancestor(db, self, level) {
                ImportAncestor::Found(import_result) => Some(import_result),
                ImportAncestor::Workspace => {
                    add_issue(IssueKind::NoParentModule);
                    // This is not correct in theory, we should simply abort here. However in
                    // practice this can be useful, because if the sys path is wrong this still
                    // provides some information, especially with completions/goto.
                    None
                }
                ImportAncestor::NoParentModule => {
                    add_issue(IssueKind::NoParentModule);
                    return None;
                }
            }
        } else {
            None
        };
        match dotted_name {
            Some(dotted_name) => self.cache_import_dotted_name(db, dotted_name, maybe_level_file),
            None => maybe_level_file,
        }
    }

    pub(super) fn assign_star_import(
        &self,
        db: &Database,
        import_from: ImportFrom,
        star_index: NodeIndex,
    ) {
        let from_first_part = self.import_from_first_part(db, import_from);
        // Nothing to do here, was calculated earlier
        let point = match from_first_part.as_deref() {
            Some(ImportResult::File(file_index)) => {
                Point::new_file_reference(*file_index, Locality::Todo)
            }
            // Currently we don't support namespace star imports
            Some(ImportResult::Namespace { .. }) => {
                Point::new_specific(Specific::ModuleNotFound, Locality::Todo)
            }
            Some(ImportResult::PyTypedMissing) => {
                Point::new_specific(Specific::ModuleNotFound, Locality::Todo)
            }
            None => Point::new_specific(Specific::ModuleNotFound, Locality::Todo),
        };
        self.points.set(star_index, point);
    }

    #[inline]
    pub fn star_import_file<'db>(
        &self,
        db: &'db Database,
        star_import: &StarImport,
    ) -> Option<&'db PythonFile> {
        let point = self.points.get(star_import.star_node);
        if point.calculated() {
            return if point.maybe_specific() == Some(Specific::ModuleNotFound) {
                None
            } else {
                Some(db.loaded_python_file(point.file_index()))
            };
        }
        let import_from = NodeRef::new(self, star_import.import_from_node).expect_import_from();
        self.assign_star_import(db, import_from, star_import.star_node);
        debug_assert!(self.points.get(star_import.star_node).calculated());
        self.star_import_file(db, star_import)
    }

    pub(super) fn add_module_not_found(&self, db: &Database, name: Name) {
        if !self.flags(db).ignore_missing_imports {
            NodeRef::new(self, name.index()).add_type_issue(
                db,
                IssueKind::ModuleNotFound {
                    module_name: Box::from(name.as_str()),
                },
            );
        }
    }

    pub fn sub_module(&self, db: &Database, name: &str) -> Option<LoadedImportResult> {
        let (entry, _) = self.file_entry_and_is_package(db);
        sub_module_import(db, self, entry, name)?.ensured_loaded_file(db)
    }

    pub fn sub_module_lookup(&self, db: &Database, name: &str) -> Option<LookupResult> {
        Some(match self.sub_module(db, name)?.into_import_result() {
            ImportResult::File(file_index) => LookupResult::FileReference(file_index),
            ImportResult::Namespace(ns) => {
                LookupResult::UnknownName(Inferred::from_type(Type::Namespace(ns.clone())))
            }
            ImportResult::PyTypedMissing => unreachable!(),
        })
    }

    pub fn maybe_submodule_reexport(
        &self,
        i_s: &InferenceState,
        name_ref: NodeRef,
        name: &str,
    ) -> Option<LookupResult> {
        let import = name_ref.maybe_import_of_name_in_symbol_table()?;
        let submodule_reexport = |import_result| {
            if let Some(ImportResult::File(f)) = import_result
                && f == self.file_index
            {
                return Some(
                    self.sub_module_lookup(i_s.db, name)
                        .unwrap_or(LookupResult::None),
                );
            }
            None
        };
        match import {
            NameImportParent::ImportFromAsName(imp) => {
                let import_from = imp.import_from()?;
                // from . import x simply imports the module that exists in the same
                // directory anyway and should not be considered a reexport.
                submodule_reexport(
                    self.import_from_first_part(i_s.db, import_from)
                        .map(|i| i.into_import_result()),
                )
            }
            NameImportParent::DottedAsName(dotted) => {
                if let DottedAsNameContent::WithAs(dotted, _) = dotted.unpack() {
                    // Only import `foo.bar as bar` can be a submodule.
                    // `import foo.bar` just exports the name foo.
                    if let DottedImportNameContent::DottedName(super_, _) = dotted.unpack() {
                        submodule_reexport(self.cache_import_dotted_name(i_s.db, super_, None))
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
        }
    }

    fn find_potential_import_from_files(
        &self,
        db: &Database,
        import_from: ImportFrom,
        mut on_potential_file: impl FnMut(ImportResult),
    ) {
        let Some(imp) = self.import_from_first_part_without_loading_file(db, import_from) else {
            return;
        };
        match import_from.unpack_targets() {
            ImportFromTargets::Star(_) => on_potential_file(imp),
            ImportFromTargets::Iterator(targets) => match imp {
                ImportResult::File(file_index) => {
                    let file_entry = db.vfs.file_entry(file_index);
                    on_potential_file(imp);
                    if is_package_name(file_entry) {
                        for target in targets {
                            let name = target.unpack().0;
                            if let Some(imp) =
                                sub_module_import(db, self, file_entry, name.as_code())
                            {
                                on_potential_file(imp)
                            }
                        }
                    }
                }
                ImportResult::Namespace(namespace) => {
                    for target in targets {
                        let name = target.unpack().0;
                        if let Some(imp) =
                            namespace_import_with_unloaded_file(db, self, &namespace, name.as_str())
                        {
                            on_potential_file(imp)
                        }
                    }
                }
                ImportResult::PyTypedMissing => (),
            },
        }
    }

    pub fn find_potential_import_for_import_node_index(
        &self,
        db: &Database,
        node_index: NodeIndex,
        mut on_potential_file: impl FnMut(ImportResult),
    ) {
        match ImportFrom::maybe_by_index(&self.tree, node_index) {
            Some(import_from) => {
                self.find_potential_import_from_files(db, import_from, on_potential_file)
            }
            None => {
                for dotted in ImportName::by_index(&self.tree, node_index).iter_dotted_as_names() {
                    if let Some(imp) = self.cache_dotted_as_name_import(db, dotted) {
                        on_potential_file(imp)
                    }
                }
            }
        }
    }
}

fn sub_module_import(
    db: &Database,
    in_file: &PythonFile,
    file_entry: &FileEntry,
    name: &str,
) -> Option<ImportResult> {
    if !is_package_name(file_entry) {
        return None;
    }
    match &file_entry.parent {
        Parent::Directory(dir) => python_import_with_needs_exact_case(
            db,
            in_file,
            std::iter::once((Directory::entries(&db.vfs, &dir.upgrade().unwrap()), false)),
            name,
            true,
            true,
        )
        .or_else(|| {
            if in_partial_stubs(db, file_entry) {
                let file = db
                    .ensure_file_for_file_index(file_entry.get_file_index()?)
                    .ok()?;
                Some(
                    file.normal_file_of_stub_file(db)?
                        .sub_module(db, name)?
                        .into_import_result(),
                )
            } else {
                None
            }
        }),
        Parent::Workspace(_) => None,
    }
}

fn in_partial_stubs(db: &Database, file_entry: &FileEntry) -> bool {
    let Some(dir) = file_entry.parent.most_outer_dir() else {
        return false;
    };
    if !dir.name.ends_with(STUBS_SUFFIX) {
        // partial is only relevant for -stubs, otherwise we don't really care.
        return false;
    }
    Directory::entries(&db.vfs, &dir)
        .search("py.typed")
        .is_some_and(|entry| match &*entry {
            // TODO we are currently never invalidating this file, when it changes
            DirectoryEntry::File(entry) => db
                .vfs
                .handler
                .read_and_watch_file(&entry.absolute_path(&*db.vfs.handler))
                .is_some_and(|code| code.contains("partial")),
            _ => false,
        })
}

pub(super) fn is_package_name(file_entry: &FileEntry) -> bool {
    &*file_entry.name == "__init__.py" || &*file_entry.name == "__init__.pyi"
}

fn cache_import_results(node_ref: NodeRef, result: &Option<ImportResult>) {
    match result {
        Some(ImportResult::File(f)) => {
            node_ref.set_point(Point::new_file_reference(*f, Locality::Complex))
        }
        Some(ImportResult::Namespace(n)) => node_ref.insert_type(Type::Namespace(n.clone())),
        Some(ImportResult::PyTypedMissing) => node_ref.set_point(Point::new_specific(
            Specific::PyTypedMissing,
            Locality::Complex,
        )),
        None => node_ref.set_point(Point::new_specific(
            Specific::ModuleNotFound,
            Locality::Complex,
        )),
    }
}

fn load_saved_results(node_ref: NodeRef, p: Point) -> Option<ImportResult> {
    match p.kind() {
        PointKind::FileReference => Some(ImportResult::File(p.file_index())),
        PointKind::Specific => {
            if p.specific() == Specific::PyTypedMissing {
                Some(ImportResult::PyTypedMissing)
            } else {
                debug_assert!(matches!(
                    p.specific(),
                    Specific::AnyDueToError | Specific::ModuleNotFound
                ));
                None
            }
        }
        PointKind::Complex => match node_ref.maybe_type().unwrap() {
            Type::Namespace(ns) => Some(ImportResult::Namespace(ns.clone())),
            _ => unreachable!(),
        },
        _ => unreachable!(),
    }
}
