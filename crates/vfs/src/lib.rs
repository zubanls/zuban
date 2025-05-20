// Some parts are copied from rust-analyzer

mod glob_abs_path;
mod local_fs;
mod normalized_path;
mod path;
mod tree;
mod utils;
mod vfs;
mod workspaces;

use std::{borrow::Cow, path::Path, rc::Rc};

use crossbeam_channel::Receiver;

pub use glob_abs_path::GlobAbsPath;
pub use local_fs::{LocalFS, SimpleLocalFS};
pub use normalized_path::NormalizedPath;
pub use path::AbsPath;
pub use tree::{Directory, DirectoryEntry, Entries, FileEntry, FileIndex, Parent};
pub use vfs::{InvalidationResult, PathWithScheme, Vfs, VfsFile, VfsPanicRecovery};
pub use workspaces::{Workspace, WorkspaceKind};

pub type NotifyEvent = notify::Result<notify::Event>;

/// Interface for reading and watching files.                                  
pub trait VfsHandler {
    /// Load the content of the given file, returning [`None`] if it does not  
    /// exists.                                                                
    fn read_and_watch_file(&self, path: &PathWithScheme) -> Option<String>;
    fn notify_receiver(&self) -> Option<&Receiver<NotifyEvent>>;
    fn on_invalidated_in_memory_file(&self, path: PathWithScheme);
    fn walk_and_watch_dirs(
        &self,
        path: &str,
        initial_parent: Parent,
        is_root_node: bool,
    ) -> DirectoryEntry;

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
        if cfg!(target_os = "windows") && path.contains("/") {
            let p = AbsPath::new_rc(path.replace('/', "\\").into());
            return Cow::Owned(NormalizedPath::new_rc(p));
        }
        Cow::Borrowed(NormalizedPath::new(path))
    }
    fn normalize_rc_path(&self, path: Rc<AbsPath>) -> Rc<NormalizedPath> {
        match self.normalize_path(&path) {
            // If it's borrowed, it means it didn't change, so we can simply cast
            Cow::Borrowed(_) => NormalizedPath::new_rc(path),
            Cow::Owned(o) => o,
        }
    }

    fn absolute_path(&self, current_dir: &AbsPath, path: String) -> Rc<AbsPath> {
        let p = Path::new(&path);
        if p.is_absolute() {
            self.unchecked_abs_path(path)
        } else {
            self.join(current_dir, &path)
        }
    }

    fn unchecked_abs_path(&self, mut path: String) -> Rc<AbsPath> {
        if let Some(new_root_path) = self.strip_separator_suffix(path.as_str()) {
            path.truncate(new_root_path.len());
        }
        AbsPath::new_rc(path.into())
    }

    fn unchecked_abs_path_from_uri(&self, path: Rc<str>) -> Rc<AbsPath> {
        AbsPath::new_rc(path.into())
    }

    fn unchecked_normalized_path(&self, path: Rc<AbsPath>) -> Rc<NormalizedPath> {
        NormalizedPath::new_rc(path.into())
    }

    fn join(&self, path: &AbsPath, name: &str) -> Rc<AbsPath> {
        self.unchecked_abs_path(
            Path::new(&**path)
                .join(name)
                .into_os_string()
                .into_string()
                .unwrap(),
        )
    }

    fn is_case_sensitive(&self) -> bool {
        cfg!(target_os = "windows")
    }
}
