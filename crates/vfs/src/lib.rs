// Some parts are copied from rust-analyzer

mod glob_abs_path;
#[cfg(feature = "watch")]
mod local_fs;
#[cfg(not(feature = "watch"))]
mod local_fs_stub;
mod memory;
mod normalized_path;
mod path;
mod tree;
mod vfs;
mod workspaces;

use std::{borrow::Cow, path::Path, sync::Arc};

#[cfg(feature = "watch")]
pub use glob_abs_path::GlobAbsPath;
#[cfg(feature = "watch")]
pub use local_fs::{LocalFS, SimpleLocalFS};
#[cfg(not(feature = "watch"))]
pub use local_fs_stub::{LocalFS, SimpleLocalFS};
pub use memory::InMemoryFs;
pub use normalized_path::NormalizedPath;
pub use path::AbsPath;
pub use tree::{DirOrFile, Directory, DirectoryEntry, Entries, FileEntry, FileIndex, Parent};
pub use vfs::{InvalidationResult, PathWithScheme, Vfs, VfsFile, VfsPanicRecovery};
pub use workspaces::{Workspace, WorkspaceKind};

#[cfg(feature = "watch")]
pub type NotifyEvent = notify::Result<notify::Event>;
#[cfg(feature = "watch")]
pub type WatcherReceiver = crossbeam_channel::Receiver<NotifyEvent>;
#[cfg(not(feature = "watch"))]
pub type NotifyEvent = ();
#[cfg(not(feature = "watch"))]
pub type WatcherReceiver = ();

/// Interface for reading and watching files.                                  
pub trait VfsHandler: Sync + Send {
    /// Load the content of the given file, returning [`None`] if it does not  
    /// exists.                                                                
    fn read_and_watch_file(&self, path: &PathWithScheme) -> Option<String>;
    fn notify_receiver(&self) -> Option<&WatcherReceiver>;
    fn on_invalidated_in_memory_file(&self, path: PathWithScheme);
    fn read_and_watch_dir(&self, path: &str, parent: Parent) -> Entries;
    fn read_and_watch_entry(
        &self,
        path: &str,
        parent: Parent,
        replace_name: &str,
    ) -> Option<DirectoryEntry>;

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

    fn normalize_path<'s>(&self, path: &'s AbsPath) -> Cow<'s, NormalizedPath> {
        NormalizedPath::normalize(path)
    }
    fn normalize_rc_path(&self, path: Arc<AbsPath>) -> Arc<NormalizedPath> {
        match self.normalize_path(&path) {
            // If it's borrowed, it means it didn't change, so we can simply cast
            Cow::Borrowed(_) => NormalizedPath::new_arc(path),
            Cow::Owned(o) => o,
        }
    }

    fn absolute_path(&self, current_dir: &AbsPath, path: &str) -> Arc<AbsPath> {
        let p = Path::new(&path);
        if p.is_absolute() {
            self.unchecked_abs_path(path)
        } else {
            self.join(current_dir, path)
        }
    }

    fn normalize_uncheck_abs_path(&self, path: &str) -> Arc<NormalizedPath> {
        self.normalize_rc_path(self.unchecked_abs_path(path))
    }

    fn unchecked_abs_path(&self, mut path: &str) -> Arc<AbsPath> {
        if let Some(new_root_path) = self.strip_separator_suffix(path) {
            path = new_root_path;
        }
        AbsPath::new_arc(path.into())
    }

    fn unchecked_abs_path_from_uri(&self, path: Arc<str>) -> Arc<AbsPath> {
        AbsPath::new_arc(path)
    }

    fn unchecked_normalized_path(&self, path: Arc<AbsPath>) -> Arc<NormalizedPath> {
        NormalizedPath::new_arc(path)
    }

    fn join(&self, path: &AbsPath, name: &str) -> Arc<AbsPath> {
        self.unchecked_abs_path(Path::new(&**path).join(name).to_str().unwrap())
    }

    fn is_case_sensitive(&self) -> bool {
        cfg!(target_os = "windows")
    }

    fn is_unnecessary_invalidation(
        &self,
        _path: &AbsPath,
        _current_entry: Option<&DirectoryEntry>,
    ) -> bool {
        false
    }
}
