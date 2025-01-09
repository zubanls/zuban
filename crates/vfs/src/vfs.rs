use std::{collections::HashMap, ops::BitOrAssign, pin::Pin, rc::Rc};

use utils::InsertOnlyVec;

use crate::{
    FileEntry, FileIndex, InvalidationDetail, Invalidations, VfsHandler, WorkspaceKind, Workspaces,
};

pub trait VfsFile: Unpin {
    fn code(&self) -> &str;
    fn invalidate_references_to(&mut self, file_index: FileIndex);
}

pub struct Vfs<F: VfsFile> {
    pub handler: Box<dyn VfsHandler>,
    pub workspaces: Workspaces,
    pub files: InsertOnlyVec<FileState<F>>,
    pub in_memory_files: HashMap<Box<str>, FileIndex>,
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

    pub fn add_workspace(&mut self, root_path: String, kind: WorkspaceKind) {
        self.workspaces.add(&*self.handler, root_path, kind)
    }

    pub fn search_file(&self, case_sensitive: bool, path: &str) -> Option<Rc<FileEntry>> {
        self.workspaces
            .search_file(&*self.handler, case_sensitive, path)
    }

    pub fn invalidate_files(
        &mut self,
        original_file_index: FileIndex,
        invalidations: Invalidations,
    ) -> InvalidationResult {
        let InvalidationDetail::Some(invalidations) = invalidations.into_iter() else {
            // This means that the file was created with `invalidates_db = true`, which
            // means we have to invalidate the whole database.
            tracing::info!(
                "Invalidate whole db because we have invalidated {}",
                self.file(original_file_index).path()
            );
            return InvalidationResult::InvalidatedDb;
        };
        for invalid_index in invalidations {
            let file = self.file_mut(invalid_index);
            let new_invalidations = file.file_entry.invalidations.take();
            file.invalidate_references_to(original_file_index);

            if let InvalidationDetail::Some(invs) = new_invalidations.iter() {
                for invalidation in &invs {
                    let p = self.file(*invalidation).path();
                    tracing::debug!(
                        "Invalidate {p} because we have invalidated {}",
                        self.file(invalid_index).path()
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

    pub fn file(&self, index: FileIndex) -> &FileState<F> {
        self.files.get(index.0 as usize).unwrap()
    }

    fn file_mut(&mut self, index: FileIndex) -> &mut FileState<F> {
        &mut self.files[index.0 as usize]
    }

    pub fn load_file_from_workspace(
        &self,
        file_entry: Rc<FileEntry>,
        invalidates_db: bool,
        new_file: impl FnOnce(FileIndex, &str, Box<str>) -> F,
    ) -> Option<FileIndex> {
        // A loader should be available for all files in the workspace.
        let path = file_entry.path(&*self.handler);
        let code = self.handler.read_and_watch_file(&path)?;
        let file_index = self.with_added_file(
            file_entry.clone(),
            path.into(),
            invalidates_db,
            |path, file_index| new_file(file_index, path, code.into()),
        );
        file_entry.file_index.set(file_index);
        Some(file_index)
    }

    pub fn in_memory_file(&mut self, path: &str) -> Option<FileIndex> {
        self.in_memory_files.get(path).cloned()
    }

    fn unload_in_memory_file_internal(
        &mut self,
        case_sensitive: bool,
        file_index: FileIndex,
    ) -> InvalidationResult {
        let file_state = &mut self.files[file_index.0 as usize];
        let path = file_state.path();
        self.workspaces
            .unload_file(&*self.handler, case_sensitive, path);
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
                Ok(self.unload_in_memory_file_internal(case_sensitive, file_index))
            }
        } else {
            Err("The path is not known to be an in memory file")
        }
    }

    pub fn unload_all_in_memory_files(&mut self, case_sensitive: bool) -> InvalidationResult {
        let in_memory_files = std::mem::take(&mut self.in_memory_files);
        let mut result = InvalidationResult::InvalidatedFiles;
        for (_path, file_index) in in_memory_files.into_iter() {
            result |= self.unload_in_memory_file_internal(case_sensitive, file_index);
        }
        result
    }

    fn update_file(
        &mut self,
        file_index: FileIndex,
        new_code: Box<str>,
        to_file: impl FnOnce(&FileState<F>, FileIndex, Box<str>) -> F,
    ) -> InvalidationResult {
        let file_state = self.file_mut(file_index);
        file_state.unload();
        let invalidations = file_state.file_entry.invalidations.take();
        let new_file = to_file(file_state, file_index, new_code);
        file_state.update(new_file);
        self.invalidate_files(file_index, invalidations)
    }

    pub fn with_added_file(
        &self,
        file_entry: Rc<FileEntry>,
        path: Box<str>,
        invalidates_db: bool,
        new_file: impl FnOnce(&str, FileIndex) -> F,
    ) -> FileIndex {
        let file_index = FileIndex(self.files.len() as u32);
        let new_file = new_file(&path, file_index);
        self.files.push(Box::pin(FileState::new_parsed(
            file_entry,
            path,
            new_file,
            invalidates_db,
        )));
        file_index
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
    pub fn unload_and_return_invalidations(&mut self) -> Invalidations {
        self.state = InternalFileExistence::Unloaded;
        self.file_entry.invalidations.take()
    }

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

    pub fn maybe_loaded_file_mut(&mut self) -> Option<&mut F> {
        match &mut self.state {
            InternalFileExistence::Parsed(f) => Some(f),
            _ => None,
        }
    }

    fn code(&self) -> Option<&str> {
        Some(self.file()?.code())
    }

    pub fn path(&self) -> &str {
        &self.path
    }

    pub fn file_entry(&self) -> &Rc<FileEntry> {
        &self.file_entry
    }

    fn unload(&mut self) {
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
