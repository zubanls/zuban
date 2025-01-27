// Some parts are copied from rust-analyzer

mod local_fs;
mod tree;
mod utils;
mod vfs;
mod workspaces;

use std::path::Path;

use crossbeam_channel::Receiver;

pub use local_fs::LocalFS;
pub use tree::{Directory, DirectoryEntry, FileEntry, FileIndex, Parent};
pub use vfs::{InvalidationResult, Vfs, VfsFile};
pub use workspaces::{Workspace, WorkspaceKind};

pub type NotifyEvent = notify::Result<notify::Event>;

/// Interface for reading and watching files.                                  
pub trait VfsHandler {
    /// Load the content of the given file, returning [`None`] if it does not  
    /// exists.                                                                
    fn read_and_watch_file(&self, path: &str) -> Option<String>;
    fn notify_receiver(&self) -> Option<&Receiver<NotifyEvent>>;
    fn walk_and_watch_dirs(&self, path: &str, initial_parent: Parent) -> DirectoryEntry;

    fn separator(&self) -> char {
        std::path::MAIN_SEPARATOR
    }
    fn strip_separator_prefix<'a>(&self, path: &'a str) -> Option<&'a str> {
        let mut result = path.strip_prefix(self.separator());
        if cfg!(target_os = "windows") {
            result = result.or_else(|| path.strip_prefix('/'));
        }
        result
    }
    fn strip_separator_suffix<'a>(&self, path: &'a str) -> Option<&'a str> {
        let mut result = path.strip_suffix(self.separator());
        if cfg!(target_os = "windows") {
            result = result.or_else(|| path.strip_suffix('/'));
        }
        result
    }

    fn split_off_folder<'a>(&self, path: &'a str) -> (&'a str, Option<&'a str>);
    fn is_sub_file_of(&self, path: &str, maybe_parent: &str) -> bool {
        Path::new(path).starts_with(Path::new(maybe_parent))
    }
}
