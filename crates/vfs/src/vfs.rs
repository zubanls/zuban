use std::rc::Rc;

use config::TypeCheckerFlags;
use utils::InsertOnlyVec;

use crate::{FileEntry, VfsHandler, WorkspaceKind, Workspaces};

pub trait VfsFile {
    fn code(&self) -> Option<&str>;
    fn unload(&mut self);
}

pub struct Vfs<F: VfsFile> {
    pub handler: Box<dyn VfsHandler>,
    pub workspaces: Workspaces,
    pub files: InsertOnlyVec<F>,
}

impl<F: VfsFile> Vfs<F> {
    pub fn new(handler: Box<dyn VfsHandler>) -> Self {
        Self {
            handler,
            workspaces: Default::default(),
            files: Default::default(),
        }
    }

    pub fn add_workspace(&mut self, root_path: String, kind: WorkspaceKind) {
        self.workspaces.add(&*self.handler, root_path, kind)
    }

    pub fn search_file(&self, flags: &TypeCheckerFlags, path: &str) -> Option<Rc<FileEntry>> {
        self.workspaces.search_file(flags, &*self.handler, path)
    }
}
