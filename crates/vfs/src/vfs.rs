use std::{collections::HashMap, ops::BitOrAssign, rc::Rc};

use utils::InsertOnlyVec;

use crate::{
    FileEntry, FileIndex, InvalidationDetail, Invalidations, VfsHandler, WorkspaceKind, Workspaces,
};

pub trait VfsFile: Unpin {
    fn code(&self) -> Option<&str>;
    fn path(&self) -> &str;
    fn file_entry(&self) -> &Rc<FileEntry>;
    fn unload(&mut self);
    fn invalidate_references_to(&mut self, file_index: FileIndex);
}

pub struct Vfs<F: VfsFile> {
    pub handler: Box<dyn VfsHandler>,
    pub workspaces: Workspaces,
    pub files: InsertOnlyVec<F>,
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
            let new_invalidations = file.file_entry().invalidations.take();
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

    pub fn file(&self, index: FileIndex) -> &F {
        self.files.get(index.0 as usize).unwrap()
    }

    fn file_mut(&mut self, index: FileIndex) -> &mut F {
        &mut self.files[index.0 as usize]
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
        let invalidations = file_state.file_entry().invalidations.take();
        self.invalidate_files(file_index, invalidations)
    }

    pub fn unload_in_memory_file(
        &mut self,
        case_sensitive: bool,
        path: &str,
        to_file: impl FnOnce(&mut F, FileIndex, Box<str>),
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
        to_file: impl FnOnce(&mut F, FileIndex, Box<str>),
    ) -> InvalidationResult {
        let file_state = self.file_mut(file_index);
        file_state.unload();
        let invalidations = file_state.file_entry().invalidations.take();
        to_file(file_state, file_index, new_code);
        self.invalidate_files(file_index, invalidations)
    }

    pub fn in_memory_file(&mut self, path: &str) -> Option<FileIndex> {
        self.in_memory_files.get(path).cloned()
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
