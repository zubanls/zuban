use std::rc::Rc;

use config::TypeCheckerFlags;
use vfs::{
    AbsPath, DirOrFile, Directory, DirectoryEntry, Entries, FileEntry, FileIndex, LocalFS,
    PathWithScheme,
};

use crate::{database::Database, file::PythonFile};

pub fn with_relevant_files<'db>(db: &'db Database, mut on_file: impl FnMut(&'db PythonFile)) {
    let vfs_handler = &*db.vfs.handler;
    for file_index in FilePicker::find_file_indexes(db) {
        let python_file = db.loaded_python_file(file_index);
        let p = python_file.file_entry(&db).absolute_path(vfs_handler);
        if let Some(more_specific_flags) = python_file.maybe_more_specific_flags(&db) {
            // We need to recheck, because we might have more specific information now for this
            // file now that it's parsed.
            // This is not necessary in theory, but might it might be better to do it this way so
            // we avoid things like checking for the homeassistant/core special cases for hundreds
            // of folders.
            if should_skip(more_specific_flags, p.path()) {
                continue;
            }
        }
        on_file(python_file)
    }
}

fn should_skip(flags: &TypeCheckerFlags, path: &AbsPath) -> bool {
    if !path.ends_with(".py") && !path.ends_with(".pyi") {
        return true;
    }
    flags.excludes.iter().any(|e| e.regex.is_match(path))
}

pub(crate) struct FilePicker<'db> {
    db: &'db Database,
    to_be_loaded: Vec<(Rc<FileEntry>, PathWithScheme)>,
    file_indexes: Vec<FileIndex>,
}

//vfs_handler: &'db dyn VfsHandler, , files: &[GlobAbsPath]
//vfs_handler, &db.project.settings.files_or_directories_to_check
impl<'db> FilePicker<'db> {
    fn find_file_indexes(db: &'db Database) -> Vec<FileIndex> {
        let mut picker = Self {
            db,
            to_be_loaded: vec![],
            file_indexes: vec![],
        };
        picker.search_in_workspaces();
        for (file, _) in picker.to_be_loaded {
            if let Some(new_index) = db.load_file_from_workspace(&file, false) {
                picker.file_indexes.push(new_index);
            }
        }
        picker.file_indexes
    }

    pub fn search_in_workspaces(&mut self) {
        // In case there are no files provided we simply scan everything. This might not be
        // efficient in some cases, but people can easily just scan the parts they wish.
        let check_files = &self.db.project.settings.files_or_directories_to_check;
        let vfs_handler = &*self.db.vfs.handler;
        if check_files.is_empty() {
            for entries in self.db.vfs.workspaces.entries_to_type_check() {
                self.handle_entries(entries)
            }
        } else {
            // First try to remove the "obvious" parts. This is the much faster code path that does
            // not need to walk the whole tree and simply tries to search for the relevant files.
            // Most people will probably not provide a glob path, they provide an actual path to a
            // file or directory and will land here.
            let not_yet_checked_globs: Vec<_> = check_files
                .iter()
                .filter(|pattern| {
                    if let Some(path) = pattern.maybe_simple_path() {
                        match self.db.vfs.search_path(
                            self.db.project.flags.case_sensitive,
                            &PathWithScheme::with_file_scheme(
                                vfs_handler.normalize_rc_path(
                                    LocalFS::without_watcher()
                                        .abs_path_from_current_dir(path.to_string()),
                                ),
                            ),
                        ) {
                            Some(DirOrFile::Dir(dir)) => self.handle_dir(&dir),
                            Some(DirOrFile::File(file)) => self.add_file(file),
                            None => (),
                        }
                        false
                    } else {
                        true
                    }
                })
                .collect();

            if !not_yet_checked_globs.is_empty() {
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
            }
        }
    }

    fn add_file(&mut self, file: Rc<FileEntry>) {
        if let Some(file_index) = file.get_file_index() {
            self.file_indexes.push(file_index);
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
                    file.absolute_path(&*self.db.vfs.handler).path(),
                ) && !ignore_py_if_overwritten_by_pyi(parent_entries, file)
                {
                    self.add_file(file.clone())
                }
            }
            DirectoryEntry::MissingEntry(_) => (),
            DirectoryEntry::Directory(dir) => self.handle_dir(dir),
        }
    }

    fn handle_dir(&mut self, dir: &Rc<Directory>) {
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
