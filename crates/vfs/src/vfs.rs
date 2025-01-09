use std::{collections::HashMap, rc::Rc};

use config::TypeCheckerFlags;
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

    pub fn search_file(&self, flags: &TypeCheckerFlags, path: &str) -> Option<Rc<FileEntry>> {
        self.workspaces.search_file(flags, &*self.handler, path)
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

    pub fn in_memory_file(&mut self, path: &str) -> Option<FileIndex> {
        self.in_memory_files.get(path).cloned()
    }
}

#[derive(PartialEq)]
pub enum InvalidationResult {
    InvalidatedFiles,
    InvalidatedDb,
}
