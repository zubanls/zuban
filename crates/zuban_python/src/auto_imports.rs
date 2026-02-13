use std::{
    collections::hash_map::Entry,
    path::Path,
    sync::{Arc, Mutex, OnceLock},
};

use config::ProjectOptions;
use parsa_python_cst::{
    CodeIndex, DottedImportName, DottedImportNameContent, Name, NameImportParent, Scope,
};
use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use utils::FastHashMap;
use vfs::{Directory, DirectoryEntry, Entries, FileEntry, Parent, PathWithScheme, WorkspaceKind};

use crate::{
    CodeAction, Project, RunCause,
    database::Database,
    file::{
        File as _, FileImport, PythonFile, dotted_path_from_dir,
        is_private_import_and_not_in_dunder_all,
    },
    imports::ImportResult,
    inference_state::InferenceState,
    node_ref::NodeRef,
    recoverable_error,
    utils::is_file_with_python_ending,
};

pub(crate) struct ImportFinder<'db> {
    db: &'db Database,
    name: &'db str,
    found: Mutex<Vec<PotentialImport<'db>>>,
}

#[derive(Clone, Copy)]
pub(crate) struct PotentialImport<'db> {
    file: &'db PythonFile,
    needs_additional_name: bool,
}

impl PotentialImport<'_> {
    pub(crate) fn title(&self, db: &Database, name: &str) -> String {
        let (dot, rest) = if self.needs_additional_name {
            (".", name)
        } else {
            ("", "")
        };
        format!("Import `{}{dot}{rest}`", self.file.qualified_name(db))
    }
}

impl<'db> ImportFinder<'db> {
    pub(crate) fn find_importable_name(
        db: &'db Database,
        name: &'db str,
    ) -> Vec<PotentialImport<'db>> {
        let slf = ImportFinder {
            db,
            name,
            found: Default::default(),
        };
        for workspace in db.vfs.workspaces.iter() {
            match &workspace.kind {
                WorkspaceKind::TypeChecking => {
                    slf.find_importable_name_in_entries(&workspace.entries, false, true)
                }
                WorkspaceKind::SitePackages => {
                    slf.find_importable_name_in_entries(&workspace.entries, false, false)
                }
                WorkspaceKind::PythonStdLib => (), // Already added as part of typeshed
                WorkspaceKind::Typeshed => {
                    let symbols = TypeshedSymbols::cached(db);
                    let mut found = slf.found.lock().unwrap();
                    let mut try_to_add = |typeshed_file: &TypeshedFile, needs_additional_name| {
                        let path = db
                            .vfs
                            .handler
                            .normalize_unchecked_abs_path(&typeshed_file.path);
                        if let Some(file_index) =
                            db.file_by_file_path(&PathWithScheme::with_file_scheme(path))
                        {
                            found.push(PotentialImport {
                                file: db.loaded_python_file(file_index),
                                needs_additional_name,
                            });
                        }
                    };
                    for typeshed_file in symbols.lookup(name) {
                        try_to_add(typeshed_file, true)
                    }
                    if let Some(typeshed_file) = symbols.lookup_top_level_file(name) {
                        try_to_add(typeshed_file, false)
                    }
                }
                // These are not reachable via normal sys path and we should therefore not add this
                // to the auto imports
                WorkspaceKind::Fallback => (),
            };
        }
        slf.found.into_inner().unwrap()
    }

    fn find_importable_name_in_entries(
        &self,
        entries: &Entries,
        in_package: bool,
        add_submodules: bool,
    ) {
        if in_package {
            if let Some(entry) = entries
                .search("__init__.pyi")
                .filter(|x| !matches!(&**x, DirectoryEntry::MissingEntry(_)))
                .or_else(|| entries.search("__init__.py"))
                && let DirectoryEntry::File(__init__) = &*entry
            {
                // We have to make sure to drop the entry otherwise star import finding can cause
                // deadlocks, because the entries are modified there (missing entries are added).
                let __init__ = __init__.clone();
                drop(entry);

                if self.find_importable_name_in_file_entry(&__init__, !add_submodules) {
                    // If we find a name in __init__.py, we should probably not be looking up the other
                    // imports.
                    return;
                }
            }
            if !add_submodules {
                return;
            }
        }
        let entries: Vec<_> = entries
            .borrow()
            .iter()
            .filter_map(|dir_entry| match dir_entry {
                DirectoryEntry::MissingEntry(_) | DirectoryEntry::Gitignore(_) => None,
                e => Some(e.clone()),
            })
            .collect();
        entries.into_par_iter().for_each(|entry| match entry {
            DirectoryEntry::File(entry) => {
                // Only find importable files like foo.py that have importable file endings and
                // don't have symbols in there like dashes and spaces.
                // TODO there are a lot of other symbols that are invalid
                if is_file_with_python_ending(&entry.name)
                    && !entry.name.contains(" ")
                    && !entry.name.contains("-")
                {
                    self.find_importable_name_in_file_entry(&entry, false);
                }
            }
            DirectoryEntry::MissingEntry(_) | DirectoryEntry::Gitignore(_) => {
                unreachable!("Removed above")
            }
            DirectoryEntry::Directory(dir) => self.find_importable_name_in_entries(
                Directory::entries(&*self.db.vfs.handler, &dir),
                true,
                add_submodules,
            ),
        })
    }

    fn find_importable_name_in_file_entry(
        &self,
        entry: &Arc<FileEntry>,
        add_star_imports: bool,
    ) -> bool {
        let Some(file) = self.db.load_file_from_workspace(entry) else {
            return false;
        };
        if file.name(self.db) == self.name {
            self.found.lock().unwrap().push(PotentialImport {
                file,
                needs_additional_name: false,
            })
        }
        if let Some(symbol) = file.lookup_symbol(self.name) {
            if is_private_import_and_not_in_dunder_all(self.db, symbol, |imp| match imp {
                NameImportParent::ImportFromAsName(from_as_name) => from_as_name
                    .import_from()
                    .is_some_and(|import_from| match import_from.level_with_dotted_name() {
                        (0, Some(imp)) => {
                            let (_, is_package) = file.file_entry_and_is_package(self.db);
                            !(is_package || has_import_of_file(self.db, file, imp))
                        }
                        (1, _) => false, // Imports from the same package are not private
                        // Levels bigger than two should not be public
                        _ => true,
                    }),
                NameImportParent::DottedAsName(_) => true,
            }) {
                return false;
            }
            self.found.lock().unwrap().push(PotentialImport {
                file,
                needs_additional_name: true,
            });
            return true;
        } else if add_star_imports {
            if file
                .name_resolution_for_types(&InferenceState::new(self.db, file))
                .lookup_from_star_import(self.name, false)
                .is_some()
            {
                self.found.lock().unwrap().push(PotentialImport {
                    file,
                    needs_additional_name: true,
                });
                return true;
            }
        }
        false
    }
}

fn all_recursive_public_typeshed_file_entries(
    db: &Database,
    entries: &Entries,
) -> Vec<Arc<FileEntry>> {
    fn recurse(db: &Database, found: &mut Vec<Arc<FileEntry>>, entries: &Entries) {
        entries.borrow().iter().for_each(|entry| {
            match entry {
                DirectoryEntry::File(entry) => {
                    // Underscored modules are private, while dunder modules are not like
                    // __init__.pyi
                    if entry.name.starts_with('_') && !entry.name.starts_with("__") {
                        return;
                    }
                    found.push(entry.clone())
                }
                DirectoryEntry::Directory(dir) => {
                    // Underscored packages are private
                    // There's a directory in stdlib called @tests
                    if dir.name.starts_with('_') || dir.name.starts_with('@') {
                        return;
                    }
                    recurse(db, found, Directory::entries(&*db.vfs.handler, dir))
                }
                DirectoryEntry::MissingEntry(_) | DirectoryEntry::Gitignore(_) => (),
            }
        })
    }
    let mut found = vec![];
    recurse(db, &mut found, entries);
    found
}

pub(crate) fn create_import_code_action<'db>(
    db: &'db Database,
    from_file: &'db PythonFile,
    potential: PotentialImport,
    title: String,
    name: Name,
) -> CodeAction<'db> {
    if potential.needs_additional_name {
        // Try to find an import that matches
        for imp in &from_file.all_imports {
            let is_reachable = || {
                imp.node_index < name.index() || matches!(name.parent_scope(), Scope::Function(_))
            };
            if imp.in_global_scope
                && is_reachable()
                && let Some(imp) = NodeRef::new(from_file, imp.node_index).maybe_import_from()
                && matches!(
                    from_file.import_from_first_part_without_loading_file(db, imp),
                    Some(ImportResult::File(i)) if i == potential.file.file_index
                )
            {
                let insertion = imp.insertion_point_for_new_name(name.as_code());
                let pos = from_file.byte_to_position_infos(db, insertion.insertion_code_index);
                return CodeAction {
                    title,
                    start_of_change: pos,
                    end_of_change: pos,
                    replacement: insertion.addition,
                };
            }
        }
    }

    let mut newlines_at_start = String::default();
    let pos = position_for_import(db, from_file, potential, &mut newlines_at_start);
    let additional_newline_needed = if matches!(
        from_file.tree.code().as_bytes().get(pos as usize),
        Some(b'\n' | b'\r')
    ) {
        ""
    } else {
        "\n"
    };
    let replacement = if potential.needs_additional_name {
        format!(
            "{newlines_at_start}from {} import {}\n{additional_newline_needed}",
            potential.file.qualified_name(db),
            name.as_code()
        )
    } else if let (_, Some(parent_dir)) = potential.file.name_and_parent_dir(db) {
        format!(
            "{newlines_at_start}from {} import {}\n{additional_newline_needed}",
            dotted_path_from_dir(&parent_dir),
            name.as_code()
        )
    } else {
        format!(
            "{newlines_at_start}import {}\n{additional_newline_needed}",
            potential.file.qualified_name(db)
        )
    };
    let pos = from_file.byte_to_position_infos(db, pos);
    CodeAction {
        title,
        start_of_change: pos,
        end_of_change: pos,
        replacement,
    }
}

fn position_for_import<'db>(
    db: &'db Database,
    from_file: &'db PythonFile,
    potential: PotentialImport,
    newlines_at_start: &mut String,
) -> CodeIndex {
    let end_of_imports = from_file.tree.initial_imports_end_code_index();
    let auto_import_kind = file_to_kind(db, potential.file);
    let mut previous_match = None;
    for imp in from_file.all_imports.iter() {
        let node_ref = NodeRef::new(from_file, imp.node_index);
        if node_ref.node_start_position() >= end_of_imports {
            break;
        }
        if let Some(kind) = imp.kind_for_auto_imports(db, from_file) {
            if kind > auto_import_kind {
                return if let Some((previous_kind, prev)) = previous_match {
                    if previous_kind < auto_import_kind {
                        newlines_at_start.push('\n');
                    }
                    prev
                } else {
                    node_ref.node_start_position()
                };
            }
            let newline_end_after_import = || {
                let end = node_ref.node_end_position();
                if let Some(newline_index) = from_file.tree.code()[end as usize..].find('\n') {
                    end + newline_index as CodeIndex + 1
                } else {
                    recoverable_error!("An import should always have a newline afterwards");
                    end
                }
            };
            previous_match = Some((kind, newline_end_after_import()));
        }
    }
    if let Some((kind, prev)) = previous_match {
        if kind < auto_import_kind {
            newlines_at_start.push('\n');
        }
        prev
    } else {
        end_of_imports
    }
}

#[derive(PartialOrd, PartialEq)]
enum ImportKind {
    StdLib,
    ThirdParty,
    Project,
}

fn file_to_kind(db: &Database, file: &PythonFile) -> ImportKind {
    match &file.file_entry(db).parent.workspace().kind {
        vfs::WorkspaceKind::TypeChecking | vfs::WorkspaceKind::Fallback => ImportKind::Project,
        vfs::WorkspaceKind::SitePackages => ImportKind::ThirdParty,
        vfs::WorkspaceKind::Typeshed | vfs::WorkspaceKind::PythonStdLib => ImportKind::StdLib,
    }
}

impl FileImport {
    fn kind_for_auto_imports(&self, db: &Database, from_file: &PythonFile) -> Option<ImportKind> {
        let check = |imp_result: Option<ImportResult>| match imp_result? {
            ImportResult::File(file_index) => {
                Some(file_to_kind(db, db.loaded_python_file(file_index)))
            }
            ImportResult::PyTypedMissing => Some(ImportKind::ThirdParty),
            ImportResult::Namespace(_) => None,
        };
        let node_ref = NodeRef::new(from_file, self.node_index);
        if let Some(import_from) = node_ref.maybe_import_from() {
            check(from_file.import_from_first_part_without_loading_file(db, import_from))
        } else {
            // We just use the first file that can be loaded, because this is a heuristic anyway.
            for dotted in node_ref.expect_import_name().iter_dotted_as_names() {
                if let Some(result) = check(from_file.cache_dotted_as_name_import(db, dotted)) {
                    return Some(result);
                }
            }
            None
        }
    }
}

#[derive(Serialize, Deserialize, Default, Debug)]
struct TypeshedFile {
    // This should probably be an Arc<NormalizedPath>, but I'm not sure how to
    // deserialize that.
    path: String,
}

type TypeshedFileIndex = u32;

#[derive(Serialize, Deserialize, Default, Debug)]
struct TypeshedSymbols {
    files: Vec<TypeshedFile>,
    toplevel_import_names: FastHashMap<String, TypeshedFileIndex>,
    // The value is the vec of a file index in the typeshed symbols.
    // It's a linked list not a Vec, because most of the time there's only one definition for a
    // name.
    symbols_to_files: FastHashMap<String, SingleLinkedList<TypeshedFileIndex>>,
}

#[derive(Serialize, Deserialize)]
struct VersionedTypeshedSymbols {
    version: usize,
    typeshed_path: String,
    symbols: TypeshedSymbols,
}

impl TypeshedSymbols {
    fn cached(db: &Database) -> &'static Self {
        static CELL: OnceLock<TypeshedSymbols> = OnceLock::new();
        const TYPESHED_CACHE_VERSION: usize = 1;
        CELL.get_or_init(|| {
            let cache = || {
                let mut options = ProjectOptions::default();
                options.settings.typeshed_path = db.project.settings.typeshed_path.clone();
                let project = Project::without_watcher(options, RunCause::LanguageServer);
                Self::generate_typeshed_symbols(&project.db)
            };

            let cache_dir = dirs::cache_dir().map(|c| c.join("zuban"));
            if let Some(cache_dir) = cache_dir
                && std::fs::create_dir_all(&cache_dir).is_ok()
            {
                const CACHE_FILE_NAME: &'static str = "typeshed.cache";
                let file = cache_dir.join(CACHE_FILE_NAME);
                let typeshed_path =
                    db.project
                        .settings
                        .typeshed_path
                        .clone()
                        .unwrap_or_else(|| {
                            for workspace in db.vfs.workspaces.iter() {
                                if matches!(&workspace.kind, WorkspaceKind::Typeshed) {
                                    return workspace.root_path.clone();
                                }
                            }
                            unreachable!("There should always be a typeshed workspace kind")
                        });
                if let Some(cached) = load_cache::<VersionedTypeshedSymbols>(&file)
                    && cached.version == TYPESHED_CACHE_VERSION
                    && *cached.typeshed_path.as_str() == ***typeshed_path
                {
                    return cached.symbols;
                }
                let result = VersionedTypeshedSymbols {
                    version: TYPESHED_CACHE_VERSION,
                    typeshed_path: typeshed_path.to_string(),
                    symbols: cache(),
                };
                match utils::serialize_binary(&result) {
                    Ok(bytes) => {
                        if let Err(err) = std::fs::write(file, bytes) {
                            tracing::error!("Could not save typeshed.cache: {err:?}");
                        }
                    }
                    Err(err) => tracing::error!("Could not serialize typeshed.cache: {err:?}"),
                };
                return result.symbols;
            }
            cache()
        })
    }

    fn generate_typeshed_symbols(db: &Database) -> Self {
        let found: Mutex<Self> = Default::default();
        for workspace in db.vfs.workspaces.iter() {
            if matches!(&workspace.kind, WorkspaceKind::Typeshed) {
                all_recursive_public_typeshed_file_entries(db, &workspace.entries)
                    .par_iter()
                    .for_each(|entry| {
                        let file = db
                            .load_file_from_workspace(entry)
                            .expect("Expected there to be all typeshed files");

                        let mut found = found.lock().unwrap();
                        let index = found.files.len() as u32;
                        found.files.push(TypeshedFile {
                            path: (**file.file_path(db)).to_string(),
                        });
                        let insert_symbol = |found: &mut Self, name: &str| match found
                            .symbols_to_files
                            .entry(name.to_string())
                        {
                            Entry::Occupied(mut occupied) => occupied.get_mut().insert_last(index),
                            Entry::Vacant(vacant) => {
                                vacant.insert_entry(SingleLinkedList::new(index));
                            }
                        };
                        match &entry.parent {
                            Parent::Directory(dir) => {
                                let dir = dir.upgrade().unwrap();
                                if entry.name.as_ref() == "__init__.pyi" {
                                    Directory::entries(&*db.vfs.handler, &dir)
                                        .borrow()
                                        .iter()
                                        .for_each(|dir_entry| {
                                            let name = dir_entry.name();
                                            if name != "__init__.pyi" {
                                                insert_symbol(
                                                    &mut found,
                                                    name.trim_end_matches(".pyi"),
                                                )
                                            }
                                        })
                                }
                            }
                            Parent::Workspace(_) => {
                                let result = found
                                    .toplevel_import_names
                                    .insert(file.name(db).to_string(), index);
                                debug_assert!(result.is_none());
                            }
                        }
                        // Builtins are already reachable
                        if file.file_index == db.python_state.builtins().file_index
                            // For now disable typing_extensions, because it essentially contains
                            // the almost exact same items as typing.pyi
                            || entry.name.as_ref() == "typing_extensions.pyi"
                        {
                            return;
                        }
                        for (name, &node_index) in file.symbol_table.iter() {
                            if is_private_import_and_not_in_dunder_all(
                                db,
                                NodeRef::new(file, node_index),
                                |_| true,
                            ) {
                                continue;
                            }
                            insert_symbol(&mut found, name)
                        }
                    })
            }
        }
        found.into_inner().unwrap()
    }

    fn lookup(&self, name: &str) -> impl Iterator<Item = &'_ TypeshedFile> {
        self.symbols_to_files
            .get(name)
            .map(|lst| lst.iter().map(|&index| &self.files[index as usize]))
            .into_iter()
            .flatten()
    }

    fn lookup_top_level_file(&self, name: &str) -> Option<&'_ TypeshedFile> {
        let index = self.toplevel_import_names.get(name)?;
        Some(&self.files[*index as usize])
    }
}

fn load_cache<T: for<'a> Deserialize<'a>>(path: &Path) -> Option<T> {
    match std::fs::read(path) {
        //Some(result),
        Ok(bytes) => match utils::deserialize_binary(&bytes) {
            Ok(result) => Some(result),
            Err(err) => {
                tracing::warn!("Tried to deserialize the typeshed cache, but got: {err:?}");
                None
            }
        },
        Err(err) => {
            tracing::info!("Tried reading typeshed cache, got: {err:?}");
            None
        }
    }
}

#[derive(Debug, Serialize, Deserialize)]
struct SingleLinkedList<T> {
    value: T,
    next: Option<Box<Self>>,
}

impl<T> SingleLinkedList<T> {
    fn new(value: T) -> Self {
        Self { value, next: None }
    }

    fn insert_last(&mut self, value: T) {
        let mut current = self;
        while let Some(ref mut next) = current.next {
            current = next;
        }
        current.next = Some(Box::new(Self { value, next: None }));
    }

    fn iter(&self) -> SingleLinkedListIter<'_, T> {
        SingleLinkedListIter { next: Some(self) }
    }
}

pub struct SingleLinkedListIter<'a, T> {
    next: Option<&'a SingleLinkedList<T>>,
}

impl<'a, T> Iterator for SingleLinkedListIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.next.map(|node| {
            self.next = node.next.as_deref();
            &node.value
        })
    }
}

fn has_import_of_file(db: &Database, file: &PythonFile, dotted: DottedImportName) -> bool {
    if let DottedImportNameContent::DottedName(dotted_inner, _) = dotted.unpack()
        && has_import_of_file(db, file, dotted_inner)
    {
        return true;
    };
    if let Some(result) = file.cache_import_dotted_name(db, dotted, None) {
        match result {
            ImportResult::File(file_index) => file_index == file.file_index,
            ImportResult::Namespace(_) => false,
            ImportResult::PyTypedMissing => false,
        }
    } else {
        false
    }
}
