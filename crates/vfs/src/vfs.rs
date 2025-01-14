use std::{collections::HashMap, ops::BitOrAssign, pin::Pin, rc::Rc};

use tracing::Level;
use utils::{FastHashSet, InsertOnlyVec};

use crate::{
    tree::{InvalidationDetail, Invalidations},
    workspaces::Workspaces,
    DirectoryEntry, FileEntry, FileIndex, Parent, VfsHandler, WorkspaceKind,
};

pub trait VfsFile: Unpin {
    fn code(&self) -> &str;
    fn invalidate_references_to(&mut self, file_index: FileIndex);
}

pub struct Vfs<F: VfsFile> {
    pub handler: Box<dyn VfsHandler>,
    pub workspaces: Workspaces,
    pub files: InsertOnlyVec<FileState<F>>,
    in_memory_files: HashMap<Box<str>, FileIndex>,
}

impl<F: VfsFile> Vfs<F> {
    pub fn new(handler: Box<dyn VfsHandler>) -> Self {
        Self {
            handler,
            workspaces: Default::default(),
            files: Default::default(),
            in_memory_files: Default::default(),
        }
    }

    pub fn with_reused_test_resources<'x>(
        &mut self,
        handler: Box<dyn VfsHandler>,
        type_checked_dirs: impl DoubleEndedIterator<Item = &'x String>,
    ) -> Self
    where
        F: Clone,
    {
        let mut files = vec![];
        let mut workspaces = self.workspaces.clone_with_new_rcs();
        for file_state in self.files.iter_mut() {
            fn search_parent(
                workspaces: &Workspaces,
                parent: Parent,
                name: &str,
            ) -> DirectoryEntry {
                let tmp;
                let parent_dir = match parent {
                    Parent::Directory(dir) => {
                        tmp = dir.upgrade().unwrap();
                        &tmp
                    }
                    Parent::Workspace(w_name) => {
                        &workspaces
                            .iter()
                            .find(|workspace| *workspace.root_path() == **w_name)
                            .unwrap()
                            .directory
                    }
                };
                let x = parent_dir.search(name).unwrap().clone();
                x
            }
            fn replace_from_new_workspace(workspaces: &Workspaces, parent: &Parent) -> Parent {
                match parent {
                    Parent::Directory(dir) => {
                        let dir = dir.upgrade().unwrap();
                        let replaced = replace_from_new_workspace(workspaces, &dir.parent);
                        let search = search_parent(workspaces, replaced, &dir.name);
                        let DirectoryEntry::Directory(new_dir) = search else {
                            unreachable!();
                        };
                        Parent::Directory(Rc::downgrade(&new_dir))
                    }
                    Parent::Workspace(_) => parent.clone(),
                }
            }
            let current_entry = file_state.file_entry();
            let parent_dir = replace_from_new_workspace(&workspaces, &current_entry.parent);
            let DirectoryEntry::File(new_file_entry) =
                search_parent(&workspaces, parent_dir, &current_entry.name)
            else {
                unreachable!()
            };
            //debug_assert_ne!(new_file_entry.as_ref() as *const _, current_entry.as_ref() as *const _);
            files.push(file_state.clone_box(new_file_entry.clone()));
        }

        for p in type_checked_dirs.rev() {
            workspaces.add_at_start(&*self.handler, p.clone(), WorkspaceKind::TypeChecking)
        }

        Self {
            handler,
            workspaces,
            files: files.into(),
            in_memory_files: Default::default(),
        }
    }

    pub fn add_workspace(&mut self, root_path: String, kind: WorkspaceKind) {
        self.workspaces.add(&*self.handler, root_path, kind)
    }

    pub fn search_path(&self, case_sensitive: bool, path: &str) -> Option<Rc<FileEntry>> {
        self.workspaces
            .search_path(&*self.handler, case_sensitive, path)
    }

    fn invalidate_files(
        &mut self,
        original_file_index: FileIndex,
        invalidations: Invalidations,
    ) -> InvalidationResult {
        let InvalidationDetail::Some(invalidations) = invalidations.into_iter() else {
            // This means that the file was created with `invalidates_db = true`, which
            // means we have to invalidate the whole database.
            tracing::info!(
                "Invalidate whole db because we have invalidated {}",
                self.file_state(original_file_index).path
            );
            return InvalidationResult::InvalidatedDb;
        };
        for invalid_index in invalidations {
            let file = self.file_state_mut(invalid_index);
            let new_invalidations = file.file_entry.invalidations.take();
            file.invalidate_references_to(original_file_index);

            if let InvalidationDetail::Some(invs) = new_invalidations.iter() {
                for invalidation in &invs {
                    let p = &self.file_state(*invalidation).path;
                    tracing::debug!(
                        "Invalidate {p} because we have invalidated {}",
                        self.file_state(invalid_index).path
                    );
                }
            }
            if self.invalidate_files(original_file_index, new_invalidations)
                == InvalidationResult::InvalidatedDb
            {
                return InvalidationResult::InvalidatedDb;
            }
        }
        InvalidationResult::InvalidatedFiles
    }

    pub fn file(&self, index: FileIndex) -> Option<&F> {
        self.files.get(index.0 as usize).unwrap().file()
    }

    pub fn file_path(&self, index: FileIndex) -> &str {
        &self.file_state(index).path
    }

    pub fn file_entry(&self, index: FileIndex) -> &Rc<FileEntry> {
        &self.file_state(index).file_entry
    }

    fn file_state(&self, index: FileIndex) -> &FileState<F> {
        self.files.get(index.0 as usize).unwrap()
    }

    fn file_state_mut(&mut self, index: FileIndex) -> &mut FileState<F> {
        &mut self.files[index.0 as usize]
    }

    pub fn load_file_from_workspace(
        &self,
        file_entry: Rc<FileEntry>,
        invalidates_db: bool,
        new_file: impl FnOnce(FileIndex, Box<str>) -> F,
    ) -> Option<FileIndex> {
        // A loader should be available for all files in the workspace.
        let path = file_entry.path(&*self.handler);
        let code = self.handler.read_and_watch_file(&path)?;
        let file_index = self.with_added_file(
            file_entry.clone(),
            path.into(),
            invalidates_db,
            |file_index| new_file(file_index, code.into()),
        );
        file_entry.set_file_index(file_index);
        Some(file_index)
    }

    pub fn in_memory_file(&mut self, path: &str) -> Option<FileIndex> {
        self.in_memory_files.get(path).cloned()
    }

    pub fn load_in_memory_file(
        &mut self,
        case_sensitive: bool,
        path: Box<str>,
        code: Box<str>,
        new_file: impl FnOnce(FileIndex, &FileEntry, Box<str>) -> F,
    ) -> (FileIndex, InvalidationResult) {
        tracing::info!("Loading in memory file: {path}");
        let ensured = self
            .workspaces
            .ensure_file(&*self.handler, case_sensitive, &path);

        let in_mem_file = self.in_memory_file(&path);
        debug_assert!(
            in_mem_file.is_none()
                || in_mem_file.is_some() && ensured.file_entry.get_file_index().is_some(),
            "{path}; in_mem_file: {in_mem_file:?}; ensured file_index: {:?}",
            ensured.file_entry.get_file_index(),
        );

        let in_mem_file = in_mem_file.or_else(|| {
            let file_index = ensured.file_entry.get_file_index()?;
            self.in_memory_files.insert(path.clone(), file_index);
            Some(file_index)
        });
        let mut file_invalidations = Default::default();
        if let Some(file_index) = in_mem_file {
            if self.file_state(file_index).code() == Some(&code) {
                // It already exists with the same code, we can therefore skip generating a new
                // file.
                return (file_index, InvalidationResult::InvalidatedFiles);
            }

            let file_state = &mut self.files[file_index.0 as usize];
            file_invalidations = file_state.file_entry.invalidations.take();
            file_state.unload();
        }

        let file_index = if let Some(file_index) = in_mem_file {
            let file = new_file(file_index, &ensured.file_entry, code);
            let new_file_state = Box::pin(FileState::new_parsed(
                ensured.file_entry,
                path,
                file,
                file_invalidations.invalidates_db(),
            ));
            self.files.set(file_index.0 as usize, new_file_state);
            if std::cfg!(debug_assertions) {
                let new = self.file_state(file_index);
                debug_assert!(
                    new.file_entry.get_file_index().is_some(),
                    "for {}",
                    new.path
                );
            }
            file_index
        } else {
            let file_index = self.with_added_file(
                ensured.file_entry.clone(),
                path.clone(),
                false,
                |file_index| new_file(file_index, &ensured.file_entry, code),
            );
            self.in_memory_files.insert(path.clone(), file_index);
            ensured.set_file_index(file_index);
            file_index
        };
        if tracing::enabled!(Level::INFO) {
            if let InvalidationDetail::Some(invs) = ensured.invalidations.iter() {
                for invalidation in &invs {
                    let p = &self.file_state(*invalidation).path;
                    let path = &self.file_state(file_index).path;
                    tracing::info!("Invalidate {p} because we're loading {path}");
                }
            }
        }
        let mut result = self.invalidate_files(file_index, ensured.invalidations);
        result |= self.invalidate_files(file_index, file_invalidations);
        (file_index, result)
    }

    fn unload_file(&mut self, case_sensitive: bool, file_index: FileIndex) -> InvalidationResult {
        let file_state = &mut self.files[file_index.0 as usize];
        self.workspaces
            .unload_file(&*self.handler, case_sensitive, &file_state.path);
        file_state.unload();
        let invalidations = file_state.file_entry.invalidations.take();
        self.invalidate_files(file_index, invalidations)
    }

    pub fn unload_in_memory_file(
        &mut self,
        case_sensitive: bool,
        path: &str,
        to_file: impl FnOnce(&FileState<F>, FileIndex, Box<str>) -> F,
    ) -> Result<InvalidationResult, &'static str> {
        if let Some(file_index) = self.in_memory_files.remove(path) {
            if let Some(on_file_system_code) = self.handler.read_and_watch_file(path) {
                let file_state = &mut self.files[file_index.0 as usize];
                // In case the code matches the one already in the file, we don't have to do anything.
                // This is the very typical case of closing a buffer after saving it and therefore
                // unloading the file from memory and using the file from the file system.
                if Some(on_file_system_code.as_str()) != file_state.code() {
                    Ok(self.update_file(file_index, on_file_system_code.into(), to_file))
                } else {
                    Ok(InvalidationResult::InvalidatedFiles)
                }
            } else {
                Ok(self.unload_file(case_sensitive, file_index))
            }
        } else {
            Err("The path is not known to be an in memory file")
        }
    }

    pub fn unload_all_in_memory_files(&mut self, case_sensitive: bool) -> InvalidationResult {
        let in_memory_files = std::mem::take(&mut self.in_memory_files);
        let mut result = InvalidationResult::InvalidatedFiles;
        for (_path, file_index) in in_memory_files.into_iter() {
            result |= self.unload_file(case_sensitive, file_index);
        }
        result
    }

    pub fn delete_in_memory_files_directory(
        &mut self,
        case_sensitive: bool,
        mut dir_path: &str,
        to_file: impl Fn(&FileState<F>, FileIndex, Box<str>) -> F,
    ) -> Result<InvalidationResult, String> {
        // TODO this method feels weird
        if let Some(p) = dir_path.strip_suffix('/') {
            dir_path = p;
        }

        let in_mem_paths: Vec<_> = self
            .in_memory_files
            .iter()
            .filter_map(|(path, _)| {
                let l = dir_path.len();
                let matches = path.starts_with(dir_path)
                    && path
                        .get(l..l + 1)
                        .is_some_and(|chr| chr.starts_with(self.handler.separator()));
                matches.then_some(path.clone())
            })
            .collect();
        let mut invalidation_result = InvalidationResult::InvalidatedFiles;
        for path in in_mem_paths {
            invalidation_result |= self
                .unload_in_memory_file(case_sensitive, &path, &to_file)
                .unwrap();
        }
        self.workspaces
            .delete_directory(&*self.handler, case_sensitive, dir_path)?;
        Ok(invalidation_result)
    }

    pub fn invalidate_path(&mut self, case_sensitive: bool, path: &str) -> InvalidationResult {
        if self.in_memory_files.contains_key(path) {
            // In memory files override all file system events
            return InvalidationResult::InvalidatedFiles;
        }
        let mut invalidates_db = false;
        let mut all_invalidations = FastHashSet::default();

        if let Some((workspace, parent, replace_name)) = self
            .workspaces
            .search_potential_parent_for_invalidation(&*self.handler, case_sensitive, path)
        {
            let mut check_invalidations_for_dir_entry = |e: &_| match e {
                DirectoryEntry::File(f) => {
                    if let Some(file_index) = f.get_file_index() {
                        all_invalidations.insert(file_index);
                    }
                }
                DirectoryEntry::MissingEntry(missing) => match missing.invalidations.iter() {
                    InvalidationDetail::InvalidatesDb => invalidates_db = true,
                    InvalidationDetail::Some(invs) => all_invalidations.extend(invs.into_iter()),
                },
                DirectoryEntry::Directory(_) => (),
            };
            let new_entry = self.handler.walk_and_watch_dirs(path, parent.clone());
            let d = parent.maybe_dir();
            let in_dir = d.as_deref().unwrap_or(&workspace.directory);
            if let DirectoryEntry::MissingEntry(_) = new_entry {
                tracing::debug!("Decided to remove {replace_name} from VFS");
                if let Some(r) = in_dir.remove_name(replace_name) {
                    check_invalidations_for_dir_entry(&r)
                }
            } else if let Some(mut to_replace) = in_dir.search_mut(replace_name) {
                tracing::debug!("Decided to replace {replace_name} in VFS");
                to_replace.walk_entries(&mut |e| check_invalidations_for_dir_entry(e));
                *to_replace = new_entry;
            } else {
                tracing::debug!("Decided to add {replace_name} to VFS");
                in_dir.entries.borrow_mut().push(new_entry);
            }
        }

        let len = all_invalidations.len();
        if invalidates_db {
            tracing::debug!("invalidate_path caused an invalidated db");
            return InvalidationResult::InvalidatedDb;
        }
        for inv in all_invalidations.into_iter() {
            if self.unload_file(case_sensitive, inv) == InvalidationResult::InvalidatedDb {
                tracing::debug!("invalidate_path caused an invalidated db");
                return InvalidationResult::InvalidatedDb;
            }
        }
        tracing::debug!("invalidate_path caused {len} direct invalidations");
        InvalidationResult::InvalidatedFiles
    }

    fn update_file(
        &mut self,
        file_index: FileIndex,
        new_code: Box<str>,
        to_file: impl FnOnce(&FileState<F>, FileIndex, Box<str>) -> F,
    ) -> InvalidationResult {
        let file_state = self.file_state_mut(file_index);
        file_state.unload();
        let invalidations = file_state.file_entry.invalidations.take();
        let new_file = to_file(file_state, file_index, new_code);
        file_state.update(new_file);
        self.invalidate_files(file_index, invalidations)
    }

    fn with_added_file(
        &self,
        file_entry: Rc<FileEntry>,
        path: Box<str>,
        invalidates_db: bool,
        new_file: impl FnOnce(FileIndex) -> F,
    ) -> FileIndex {
        let file_index = FileIndex(self.files.len() as u32);
        let new_file = new_file(file_index);
        self.files.push(Box::pin(FileState::new_parsed(
            file_entry,
            path,
            new_file,
            invalidates_db,
        )));
        file_index
    }

    pub fn create_sub_file(
        &self,
        super_file_index: FileIndex,
        add: impl FnOnce(FileIndex) -> F,
    ) -> FileIndex {
        let file_entry = self.file_state(super_file_index).file_entry.clone();
        let invalidates_db = file_entry.invalidations.invalidates_db();
        self.with_added_file(file_entry, "".into(), invalidates_db, add)
    }
}

#[must_use]
#[derive(PartialEq)]
pub enum InvalidationResult {
    InvalidatedFiles,
    InvalidatedDb,
}

impl BitOrAssign for InvalidationResult {
    fn bitor_assign(&mut self, rhs: Self) {
        if *self == InvalidationResult::InvalidatedFiles {
            *self = rhs;
        }
    }
}

#[derive(Debug, Clone)]
pub struct FileState<F> {
    path: Box<str>,
    file_entry: Rc<FileEntry>,
    state: InternalFileExistence<F>,
}

impl<F: VfsFile> FileState<F> {
    pub fn new_parsed(
        file_entry: Rc<FileEntry>,
        path: Box<str>,
        file: F,
        invalidates_db: bool,
    ) -> Self {
        if invalidates_db {
            file_entry.invalidations.set_invalidates_db();
        }
        Self {
            file_entry,
            path,
            state: InternalFileExistence::Parsed(file),
        }
    }

    fn update(&mut self, file: F) {
        debug_assert!(matches!(self.state, InternalFileExistence::Unloaded));
        self.state = InternalFileExistence::Parsed(file)
    }

    pub fn file(&self) -> Option<&F> {
        match &self.state {
            InternalFileExistence::Unloaded => None,
            InternalFileExistence::Parsed(f) => Some(f),
        }
    }

    pub fn file_mut(&mut self) -> Option<&mut F> {
        match &mut self.state {
            InternalFileExistence::Parsed(f) => Some(f),
            _ => None,
        }
    }

    fn code(&self) -> Option<&str> {
        Some(self.file()?.code())
    }

    pub fn file_entry(&self) -> &Rc<FileEntry> {
        &self.file_entry
    }

    pub fn unload(&mut self) {
        self.state = InternalFileExistence::Unloaded;
    }

    fn invalidate_references_to(&mut self, file_index: FileIndex) {
        if let InternalFileExistence::Parsed(f) = &mut self.state {
            f.invalidate_references_to(file_index)
        }
    }
}

impl<F: Clone> FileState<F> {
    pub fn clone_box(&self, new_file_entry: Rc<FileEntry>) -> Pin<Box<Self>> {
        let mut new = self.clone();
        new.file_entry = new_file_entry;
        Box::pin(new)
    }
}

#[derive(Clone, Debug)]
enum InternalFileExistence<F> {
    Unloaded,
    Parsed(F),
}
