use std::{hash::Hasher, sync::Arc};

use vfs::Directory;

use crate::{database::Database, file::dotted_path_from_dir, utils::join_with_commas};

#[derive(Debug, Clone)]
pub(crate) struct Namespace {
    pub directories: Arc<[Arc<Directory>]>,
}

impl Namespace {
    pub fn qualified_name(&self) -> String {
        dotted_path_from_dir(self.directories.first().unwrap())
    }

    pub fn debug_path(&self, db: &Database) -> String {
        join_with_commas(
            self.directories
                .iter()
                .map(|d| d.absolute_path(&*db.vfs.handler).path().to_string()),
        )
    }
}

impl std::cmp::PartialEq for Namespace {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.directories, &other.directories)
    }
}

impl std::hash::Hash for Namespace {
    fn hash<H: Hasher>(&self, state: &mut H) {
        Arc::as_ptr(&self.directories).hash(state);
    }
}

impl std::cmp::Eq for Namespace {}
