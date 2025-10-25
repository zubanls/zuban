use std::sync::{Arc, Mutex, RwLock};

use config::TypeCheckerFlags;
use rayon::prelude::*;
use utils::FastHashSet;
use vfs::{
    DirOrFile, Directory, DirectoryEntry, Entries, FileEntry, FileIndex, GlobAbsPath, LocalFS,
    PathWithScheme,
};

use crate::{
    database::Database, diagnostics::Diagnostic, file::PythonFile, imports::ImportResult,
    utils::join_with_commas,
};

pub(crate) fn diagnostics_for_relevant_files<'db>(
    db: &'db Database,
    on_file: impl FnMut(&'db PythonFile) -> Vec<Diagnostic<'db>>,
) -> anyhow::Result<Vec<Diagnostic<'db>>> {
    let files = FileSelector::find_files(db)?;
    Ok(files
        .into_iter()
        .map(on_file)
        .reduce(|mut vec1, vec2| {
            vec1.extend(vec2);
            vec1
        })
        .unwrap_or_default())
}

pub(crate) fn all_typechecked_files<'db>(
    db: &'db Database,
) -> (
    FastHashSet<FileIndex>,
    Vec<(Arc<FileEntry>, PathWithScheme)>,
) {
    let mut selector = FileSelector::new(db);
    selector.search_all_typechecked_files();
    (
        selector.file_indexes.into_inner().unwrap(),
        selector.to_be_loaded,
    )
}

fn should_skip(flags: &TypeCheckerFlags, rel_path: &str) -> bool {
    if !rel_path.ends_with(".py") && !rel_path.ends_with(".pyi") {
        return true;
    }
    flags.excludes.iter().any(|e| e.regex.is_match(rel_path))
}

struct FileSelector<'db> {
    db: &'db Database,
    to_be_loaded: Vec<(Arc<FileEntry>, PathWithScheme)>,
    file_indexes: RwLock<FastHashSet<FileIndex>>,
    added_file: bool,
}

impl<'db> FileSelector<'db> {
    fn new(db: &'db Database) -> Self {
        Self {
            db,
            to_be_loaded: vec![],
            file_indexes: Default::default(),
            added_file: false,
        }
    }

    fn find_files(db: &'db Database) -> anyhow::Result<Vec<&'db PythonFile>> {
        let mut selector = Self::new(db);
        selector.search_in_workspaces()?;
        let loaded_file_entries: Mutex<FastHashSet<ArcPtrWrapper>> = Mutex::new(
            selector
                .to_be_loaded
                .iter()
                .map(|l| ArcPtrWrapper(Arc::as_ptr(&l.0)))
                .collect(),
        );
        selector.to_be_loaded.par_iter().for_each(|(file, _)| {
            if let Some(new_index) = db.load_file_from_workspace(file, false) {
                selector.file_indexes.write().unwrap().insert(new_index);
                let file = db.loaded_python_file(new_index);
                find_imports_and_preload_files(db, file, &loaded_file_entries)
            }
        });
        let vfs_handler = &*db.vfs.handler;
        let mut vec: Vec<_> = selector
            .file_indexes
            .into_inner()
            .unwrap()
            .into_iter()
            .map(|file_index| db.loaded_python_file(file_index))
            // TODO shouldn't this be done before name binding?
            .filter(|file| {
                let p = file.file_entry(db).relative_path(vfs_handler);
                if let Some(more_specific_flags) = file.maybe_more_specific_flags(db) {
                    // We need to recheck, because we might have more specific information now for this
                    // file now that it's parsed.
                    if should_skip(more_specific_flags, &p) {
                        return false;
                    }
                }
                true
            })
            .collect();
        // Sort to have at least somewhat of a deterministic order, it's probably easier to debug
        // it that way.
        vec.sort_by_key(|file| file.file_index);
        Ok(vec)
    }

    fn search_all_typechecked_files(&mut self) {
        for entries in self.db.vfs.workspaces.entries_to_type_check() {
            self.handle_entries(entries)
        }
    }

    fn search_in_workspaces(&mut self) -> anyhow::Result<()> {
        // In case there are no files provided we simply scan everything. This might not be
        // efficient in some cases, but people can easily just scan the parts they wish.
        let check_files = &self.db.project.settings.files_or_directories_to_check;
        let vfs_handler = &*self.db.vfs.handler;
        if check_files.is_empty() {
            self.search_all_typechecked_files();
            if !self.added_file {
                anyhow::bail!("No Python files found to check")
            }
        } else {
            // First try to remove the "obvious" parts. This is the much faster code path that does
            // not need to walk the whole tree and simply tries to search for the relevant files.
            // Most people will probably not provide a glob path, they provide an actual path to a
            // file or directory and will land here.
            let not_yet_checked_globs: Vec<&GlobAbsPath> = check_files
                .iter()
                .filter_map(|pattern| {
                    if let Some(path) = pattern.maybe_simple_path() {
                        self.added_file = false;
                        let normalized =
                            LocalFS::without_watcher().normalized_path_from_current_dir(path);
                        match self.db.vfs.search_path(
                            self.db.project.flags.case_sensitive,
                            &PathWithScheme::with_file_scheme(normalized.clone()),
                        ) {
                            Some(DirOrFile::Dir(dir)) => self.handle_dir(&dir),
                            Some(DirOrFile::File(file)) => self.add_file(file),
                            None => {
                                for workspace in self.db.vfs.workspaces.iter() {
                                    if workspace.root_path_starts_with(&normalized) {
                                        self.handle_entries(&workspace.entries)
                                    }
                                }
                            }
                        }
                        if !self.added_file {
                            Some(Err(anyhow::anyhow!(
                                "No Python files found to check for {path}"
                            )))
                        } else {
                            None
                        }
                    } else {
                        Some(Ok(pattern))
                    }
                })
                .collect::<anyhow::Result<Vec<_>>>()?;

            if !not_yet_checked_globs.is_empty() {
                self.added_file = false;
                for entries in self.db.vfs.workspaces.entries_to_type_check() {
                    entries.walk_entries(vfs_handler, &mut |in_dir, entry| {
                        let path = match entry {
                            DirectoryEntry::File(file) => file.absolute_path(vfs_handler),
                            DirectoryEntry::MissingEntry(_) => return false,
                            DirectoryEntry::Directory(dir) => dir.absolute_path(vfs_handler),
                        };
                        if not_yet_checked_globs
                            .iter()
                            .any(|glob| glob.matches(vfs_handler, path.path()))
                        {
                            self.handle_entry(in_dir, entry);
                            false
                        } else {
                            true
                        }
                    });
                }
                if !self.added_file {
                    let paths = join_with_commas(not_yet_checked_globs.iter().map(|g| g.as_str()));
                    anyhow::bail!("No Python files found to check in {paths}");
                }
            }
        }
        Ok(())
    }

    fn add_file(&mut self, file: Arc<FileEntry>) {
        self.added_file = true;
        if let Some(file_index) = file.get_file_index() {
            self.file_indexes.write().unwrap().insert(file_index);
        } else {
            let path = file.absolute_path(&*self.db.vfs.handler);
            self.to_be_loaded.push((file, path));
        }
    }

    fn handle_entry(&mut self, parent_entries: &Entries, entry: &DirectoryEntry) {
        match entry {
            DirectoryEntry::File(file) => {
                if !should_skip(
                    &self.db.project.flags,
                    &file.relative_path(&*self.db.vfs.handler),
                ) && !ignore_py_if_overwritten_by_pyi(parent_entries, file)
                {
                    self.add_file(file.clone())
                }
            }
            DirectoryEntry::MissingEntry(_) => (),
            DirectoryEntry::Directory(dir) => self.handle_dir(dir),
        }
    }

    fn handle_dir(&mut self, dir: &Arc<Directory>) {
        self.handle_entries(Directory::entries(&*self.db.vfs.handler, dir))
    }

    fn handle_entries(&mut self, entries: &Entries) {
        for entry in &entries.iter() {
            self.handle_entry(entries, entry)
        }
    }
}

fn ignore_py_if_overwritten_by_pyi(parent_entries: &Entries, file: &FileEntry) -> bool {
    if !file.name.ends_with(".py") {
        return false;
    }
    parent_entries
        .search(&format!("{}i", &file.name))
        .is_some_and(|e| matches!(*e, DirectoryEntry::File(_)))
}

#[derive(Hash, Eq, PartialEq)]
struct ArcPtrWrapper(*const FileEntry);
// We use this only for Pointer equality checks so it's fine
unsafe impl Sync for ArcPtrWrapper {}
unsafe impl Send for ArcPtrWrapper {}

fn find_imports_and_preload_files(
    db: &Database,
    file: &PythonFile,
    loaded_file_entries: &Mutex<FastHashSet<ArcPtrWrapper>>,
) {
    let mut need_to_load_files = FastHashSet::default();
    for node_index in &file.all_imports {
        file.find_potential_import_for_import_node_index(db, *node_index, |on_file| match on_file {
            ImportResult::File(file_index) => {
                let ptr = ArcPtrWrapper(Arc::as_ptr(db.vfs.file_entry(file_index)));
                if loaded_file_entries.lock().unwrap().insert(ptr) {
                    need_to_load_files.insert(file_index);
                }
            }
            ImportResult::Namespace(_) => (),
            ImportResult::PyTypedMissing => (),
        })
    }
    need_to_load_files.into_par_iter().for_each(|file_index| {
        if let Ok(_file) = db.ensure_file_for_file_index(file_index) {
            // TODO should we preload all files? At the moment this seems not necessary
            //find_imports_and_preload_files(db, file, loaded_file_entries)
        }
    });
}
