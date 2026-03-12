use std::{
    ops::Deref,
    sync::{Arc, Weak},
};

use utils::match_case;
use vfs::{Directory, DirectoryEntry, Entries, FileIndex, Workspace, WorkspaceKind};

use crate::{
    database::Database,
    file::PythonFile,
    inferred::Inferred,
    type_::{Namespace, Type},
};

pub const STUBS_SUFFIX: &str = "-stubs";
const INIT_PY: &str = "__init__.py";
const INIT_PYI: &str = "__init__.pyi";

#[derive(Debug, Clone)]
pub(crate) enum ImportResult {
    File(FileIndex),
    Namespace(Arc<Namespace>), // A Python Namespace package, i.e. a directory
    PyTypedMissing,            // Files exist, but the py.typed marker is missing.
}

impl ImportResult {
    pub fn ensured_loaded_file(self, db: &Database) -> Option<LoadedImportResult> {
        if let Self::File(file_index) = self {
            db.ensure_file_for_file_index(file_index).ok()?;
        }
        Some(LoadedImportResult(self))
    }

    pub fn into_inferred(self, db: &Database) -> Inferred {
        let Some(result) = self.ensured_loaded_file(db) else {
            // TODO this should probably cause an error (the file was not there anymore)
            return Inferred::new_module_not_found();
        };
        match result.0 {
            ImportResult::File(file_index) => Inferred::new_file_reference(file_index),
            ImportResult::Namespace(namespace) => {
                Inferred::from_type(Type::Namespace(namespace.clone()))
            }
            Self::PyTypedMissing => Inferred::new_any_from_error(),
        }
    }

    pub fn import(
        self,
        db: &Database,
        original_file: &PythonFile,
        name: &str,
    ) -> Option<ImportResult> {
        match self.ensured_loaded_file(db)?.0 {
            Self::File(file_index) => Some(
                db.loaded_python_file(file_index)
                    .sub_module(db, name)?
                    .into_import_result(),
            ),
            Self::Namespace(ns) => python_import(
                db,
                original_file,
                ns.directories
                    .iter()
                    .map(|d| Directory::entries(&db.vfs, d)),
                name,
            ),
            Self::PyTypedMissing => unreachable!(),
        }
    }

    pub fn import_non_stub_for_stub_package(
        db: &Database,
        original_file: &PythonFile,
        parent_dir: Option<Arc<Directory>>,
        name: &str,
    ) -> Option<Self> {
        let result = if let Some(parent_dir) = parent_dir {
            Self::import_non_stub_for_stub_package(
                db,
                original_file,
                parent_dir.parent.maybe_dir().ok(),
                &parent_dir.name,
            )?
            .import(db, original_file, name)
        } else if let Some(suffix) = name.strip_suffix(STUBS_SUFFIX) {
            global_import_without_stubs_first(db, original_file, suffix)
        } else {
            python_import_with_needs_exact_case(
                db,
                original_file,
                db.vfs
                    .workspaces
                    .iter()
                    .filter(|w| !matches!(w.kind, WorkspaceKind::Typeshed))
                    .map(|w| (&w.entries, false)),
                name,
                false,
                false,
            )
        };
        match result {
            Some(ImportResult::File(f)) if f == original_file.file_index => None,
            _ => result,
        }
    }

    pub fn import_stub_for_non_stub_package(
        db: &Database,
        original_file: &PythonFile,
        parent_dir: Option<Arc<Directory>>,
        name: &str,
    ) -> Option<Self> {
        if let Some(parent_dir) = parent_dir {
            Self::import_stub_for_non_stub_package(
                db,
                original_file,
                parent_dir.parent.maybe_dir().ok(),
                &parent_dir.name,
            )?
            .import(db, original_file, name)
        } else {
            global_import_of_stubs_folders(db, original_file, name)
        }
    }

    pub fn debug_info<'x>(&'x self, db: &'x Database) -> String {
        match self {
            Self::File(f) => format!("{} ({f})", db.file_path(*f)),
            Self::Namespace(namespace) => {
                format!("namespace {}", namespace.debug_path(db))
            }
            Self::PyTypedMissing => "<py.typed missing>".into(),
        }
    }
}

impl std::ops::Deref for LoadedImportResult {
    type Target = ImportResult;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

pub(crate) struct LoadedImportResult(ImportResult);

impl LoadedImportResult {
    pub fn qualified_name(&self, db: &Database) -> String {
        match &self.0 {
            ImportResult::File(file_index) => db.loaded_python_file(*file_index).qualified_name(db),
            ImportResult::Namespace(ns) => ns.qualified_name(),
            ImportResult::PyTypedMissing => unreachable!(),
        }
    }

    pub fn into_import_result(self) -> ImportResult {
        self.0
    }
}

pub fn global_import<'a>(
    db: &'a Database,
    from_file: &PythonFile,
    name: &'a str,
) -> Option<ImportResult> {
    if name == "typing" {
        return Some(ImportResult::File(db.python_state.typing().file_index));
    }
    // First try <package>-stubs
    global_import_of_stubs_folders(db, from_file, name)
        .or_else(|| {
            python_import_with_needs_exact_case(
                db,
                from_file,
                db.vfs
                    .workspaces
                    .iter()
                    .map(|w| (&w.entries, w.part_of_site_packages())),
                name,
                false,
                true,
            )
        })
        .or_else(|| {
            if !db.project.settings.explicit_package_bases {
                // Since the sys path is sometimes not complete and people have weird setups we
                // simply allow the first outer directory without an `__init__.py[i]` as an
                // additional sys path entry. --explicit-package-bases deactivates this.
                let mut parent = from_file.file_entry(db).parent.clone();
                while let Ok(dir) = parent.maybe_dir() {
                    if load_init_file(db, &dir, from_file.file_index).is_none() {
                        return python_import_with_needs_exact_case(
                            db,
                            from_file,
                            std::iter::once((Directory::entries(&db.vfs, &dir), false)),
                            name,
                            false,
                            true,
                        );
                    }
                    parent = dir.parent.clone()
                }
            }
            None
        })
}

fn global_import_of_stubs_folders<'a>(
    db: &'a Database,
    from_file: &PythonFile,
    name: &'a str,
) -> Option<ImportResult> {
    global_import_without_stubs_first(db, from_file, &format!("{name}{STUBS_SUFFIX}"))
}

fn global_import_without_stubs_first<'a>(
    db: &'a Database,
    from_file: &PythonFile,
    name: &'a str,
) -> Option<ImportResult> {
    python_import(
        db,
        from_file,
        db.vfs.workspaces.iter().map(|d| &d.entries),
        name,
    )
}

pub fn namespace_import_with_unloaded_file(
    db: &Database,
    from_file: &PythonFile,
    namespace: &Namespace,
    name: &str,
) -> Option<ImportResult> {
    let result = python_import(
        db,
        from_file,
        namespace
            .directories
            .iter()
            .map(|d| Directory::entries(&db.vfs, d)),
        name,
    )
    .or_else(|| {
        // If the namespace does not have a specific import, we check if we are in a
        // <foo>-stubs package and import the non-stubs version of that package.
        namespace
            .directories
            .iter()
            .filter_map(|dir| {
                ImportResult::import_non_stub_for_stub_package(
                    db,
                    from_file,
                    Some(dir.clone()),
                    name,
                )
            })
            .next()
    });
    // Since we are in a namespace, we need to verify the case where a namespace within
    // site-packages has a py.typed in one of the subdirectories.
    if let Some(ImportResult::File(file_index)) = result {
        let file_entry = db.vfs.file_entry(file_index);
        let mut parent = file_entry.parent.clone();
        loop {
            match parent.maybe_dir() {
                Ok(dir) => {
                    if Directory::entries(&db.vfs, &dir)
                        .search("py.typed")
                        .is_some()
                        || dir.name.ends_with(STUBS_SUFFIX)
                    {
                        return result;
                    }
                    parent = dir.parent.clone();
                }
                Err(parent_workspace) => {
                    for workspace in db.vfs.workspaces.iter() {
                        if workspace.root_path() == parent_workspace.upgrade().unwrap().root_path()
                        {
                            if workspace.part_of_site_packages() {
                                return Some(ImportResult::PyTypedMissing);
                            } else {
                                return result;
                            }
                        }
                    }
                    unreachable!()
                }
            }
        }
    }
    result
}

pub fn namespace_import(
    db: &Database,
    from_file: &PythonFile,
    namespace: &Namespace,
    name: &str,
) -> Option<LoadedImportResult> {
    namespace_import_with_unloaded_file(db, from_file, namespace, name)?.ensured_loaded_file(db)
}

pub fn python_import<'x>(
    db: &Database,
    from_file: &PythonFile,
    dirs: impl Iterator<Item = &'x Entries>,
    name: &str,
) -> Option<ImportResult> {
    python_import_with_needs_exact_case(db, from_file, dirs.map(|d| (d, false)), name, false, true)
}

pub fn python_import_with_needs_exact_case<'x>(
    db: &Database,
    from_file: &PythonFile,
    // Directory / Needs py.typed pairing
    dirs: impl Iterator<Item = (&'x Entries, bool)>,
    name: &str,
    needs_exact_case: bool,
    check_stubs: bool,
) -> Option<ImportResult> {
    let mut python_file_index = None;
    let mut stub_file_index = None;
    let mut namespace_directories = vec![];

    // TODO these format!() always allocate a lot and don't seem to be necessary
    let name_py = format!("{name}.py");
    let name_pyi = format!("{name}.pyi");

    for (dir, needs_py_typed) in dirs {
        let mut had_namespace_dir = false;
        // Unfortunately the non-exact case requires us to iter through all entries.
        let mut directory_imports = |dir| {
            let result = load_init_file(db, dir, from_file.file_index);
            if let Some(file_index) = result {
                if needs_py_typed
                    && !from_file.flags(db).follow_untyped_imports
                    && Directory::entries(&db.vfs, dir)
                        .search("py.typed")
                        .is_none()
                {
                    return Some(ImportResult::PyTypedMissing);
                }
                return Some(ImportResult::File(file_index));
            }
            had_namespace_dir = true;
            namespace_directories.push(dir.clone());
            None
        };
        let mut file_imports = |file, is_py_file: bool| {
            if needs_py_typed && !from_file.flags(db).follow_untyped_imports {
                return Some(ImportResult::PyTypedMissing);
            }
            let file_index = db.vfs.ensure_file_index(file);
            if is_py_file {
                python_file_index = Some((file.clone(), file_index));
            } else {
                stub_file_index = Some((file.clone(), file_index));
            }
            None
        };
        // TODO
        if true || needs_exact_case {
            for (_, entry) in dir.borrow().iter() {
                match entry {
                    DirectoryEntry::Directory(dir2) => {
                        if match_c(db, dir2.name.as_ref(), name, needs_exact_case)
                            && let result @ Some(_) = directory_imports(dir2)
                        {
                            return result;
                        }
                    }
                    DirectoryEntry::File(file) => {
                        let is_py_file = match_c(db, &file.name, &name_py, needs_exact_case);
                        if is_py_file
                            || check_stubs && match_c(db, &file.name, &name_pyi, needs_exact_case)
                        {
                            if let result @ Some(_) = file_imports(file, is_py_file) {
                                return result;
                            }
                        }
                    }
                    DirectoryEntry::MissingEntry { .. } | DirectoryEntry::Gitignore(_) => (),
                }
            }
        } else {
        }
        if let Some((file_entry, file_index)) = stub_file_index.take().or(python_file_index.take())
        {
            file_entry.add_invalidation(from_file.file_index);
            return Some(ImportResult::File(file_index));
        }
        let mut add_missing = dir.add_missing_entry_callback(from_file.file_index);
        add_missing(&name_py);
        if check_stubs {
            add_missing(&name_pyi);
        }
        // The folder should not exist for folder/__init__.py or a namespace.
        if !had_namespace_dir {
            add_missing(name);
        }
    }
    if !namespace_directories.is_empty() {
        return Some(ImportResult::Namespace(Arc::new(Namespace {
            directories: namespace_directories.into(),
        })));
    }
    if name == "django-stubs" {
        if let Some(workspace) = ensure_django_stubs_workspace_and_return_newly_created(db) {
            return python_import_with_needs_exact_case(
                db,
                from_file,
                std::iter::once((&workspace.entries, false)),
                name,
                needs_exact_case,
                check_stubs,
            );
        }
    }
    None
}

#[inline]
fn match_c(db: &Database, x: &str, y: &str, needs_exact_case: bool) -> bool {
    if needs_exact_case {
        x == y
    } else {
        match_case(db.project.flags.case_sensitive, x, y)
    }
}

fn ensure_django_stubs_workspace_and_return_newly_created(
    db: &Database,
) -> Option<impl Deref<Target = &Workspace>> {
    let mut django_path = None;
    for workspace in db.vfs.workspaces.iter() {
        if django_path.is_none() && workspace.kind == WorkspaceKind::Typeshed {
            django_path = Some(
                db.vfs.handler.normalize_unchecked_abs_path(
                    workspace
                        .root_path
                        .as_ref()
                        .as_ref()
                        .parent()?
                        .parent()?
                        .join("django-stubs")
                        .to_str()
                        .expect("The initial path is utf-8"),
                ),
            );
        } else if let Some(django_path) = &django_path {
            if *django_path == workspace.root_path {
                // It was already added previously
                return None;
            }
        }
    }
    debug_assert!(django_path.is_some());
    db.vfs
        .add_workspace(django_path?, WorkspaceKind::SitePackages);
    Some(db.vfs.workspaces.expect_last())
}

fn load_init_file(
    db: &Database,
    content: &Arc<Directory>,
    from_file: FileIndex,
) -> Option<FileIndex> {
    let entries = Directory::entries(&db.vfs, content);
    load_init_file_from_entries(db, entries, from_file)
}

fn load_init_file_from_entries(
    db: &Database,
    entries: &Entries,
    from_file: FileIndex,
) -> Option<FileIndex> {
    let mut found_py = None;
    for (_, child) in entries.borrow().iter() {
        if let DirectoryEntry::File(entry) = child {
            if match_c(db, &entry.name, INIT_PYI, false) {
                let found_file_index = db.vfs.ensure_file_index(entry);
                entry.add_invalidation(from_file);
                return Some(found_file_index);
            }
            if match_c(db, &entry.name, INIT_PY, false) {
                found_py = Some(entry.clone());
            }
        }
    }
    let mut add_missing = entries.add_missing_entry_callback(from_file);
    add_missing(INIT_PYI);
    if let Some(found_py) = found_py {
        drop(add_missing); // Ensure that we avoid the borrow
        let found_file_index = db.vfs.ensure_file_index(&found_py);
        found_py.add_invalidation(from_file);
        Some(found_file_index)
    } else {
        add_missing(INIT_PY);
        None
    }
}

pub enum ImportAncestor {
    Found(ImportResult),
    Workspace,
    NoParentModule,
}

pub fn find_import_ancestor(db: &Database, file: &PythonFile, level: usize) -> ImportAncestor {
    debug_assert!(level > 0);
    let invalid = |workspace: &Weak<Workspace>, current_level| match level - current_level {
        0 => {
            if !db.project.settings.explicit_package_bases {
                // While technically the sys path says that this is a workspace, we probably just
                // have the wrong sys path and since this is annoying for most users, just allow
                // the user to access the workspace as a relative directory.
                let workspace = workspace.upgrade().unwrap();
                if let Some(index) =
                    load_init_file_from_entries(db, &workspace.entries, file.file_index)
                {
                    return ImportAncestor::Found(ImportResult::File(index));
                }
            }
            ImportAncestor::Workspace
        }
        _ => ImportAncestor::NoParentModule,
    };
    let mut parent = match file.file_entry(db).parent.maybe_dir() {
        Ok(dir) => dir,
        Err(workspace) => return invalid(workspace, 1),
    };
    for i in 1..level {
        parent = match parent.parent.maybe_dir() {
            Ok(dir) => dir,
            Err(workspace) => return invalid(workspace, i + 1),
        };
    }
    ImportAncestor::Found(match load_init_file(db, &parent, file.file_index) {
        Some(index) => ImportResult::File(index),
        None => ImportResult::Namespace(Arc::new(Namespace {
            directories: [parent].into(),
        })),
    })
}
