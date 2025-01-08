use std::rc::Rc;

use config::TypeCheckerFlags;

use crate::{FileEntry, VfsHandler, WorkspaceKind, Workspaces};

pub struct Vfs {
    pub handler: Box<dyn VfsHandler>,
    pub workspaces: Workspaces,
}

impl Vfs {
    pub fn new(handler: Box<dyn VfsHandler>) -> Self {
        Self {
            handler,
            workspaces: Default::default(),
        }
    }

    pub fn add_workspace(&mut self, root_path: String, kind: WorkspaceKind) {
        self.workspaces.add(&*self.handler, root_path, kind)
    }

    pub fn search_file(&self, flags: &TypeCheckerFlags, path: &str) -> Option<Rc<FileEntry>> {
        self.workspaces.search_file(flags, &*self.handler, path)
    }
}
