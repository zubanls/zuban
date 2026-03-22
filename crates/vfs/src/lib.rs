// Some parts are copied from rust-analyzer

mod glob_abs_path;

#[cfg(not(target_family = "wasm"))]
mod local_fs;

#[cfg(target_family = "wasm")]
#[path = "local_fs_stub.rs"]
mod local_fs;

mod memory;
mod normalized_path;
mod path;
mod tree;
mod vfs;
mod workspaces;

use std::{
    borrow::Cow,
    path::{Component, Path},
    sync::Arc,
};

pub use glob_abs_path::GlobAbsPath;

pub use local_fs::{LocalFS, SimpleLocalFS};

#[cfg(target_family = "wasm")]
pub use memory::InMemoryFs;

pub use normalized_path::NormalizedPath;
pub use path::AbsPath;
pub use tree::{
    DirOrFile, Directory, DirectoryEntry, Entries, FileEntry, FileIndex, GitignoreFile, Parent,
};
pub use vfs::{InvalidationResult, PathWithScheme, Vfs, VfsFile, VfsPanicRecovery};
pub use workspaces::{Workspace, WorkspaceKind, Workspaces, WorkspacesBuilder};

#[cfg(not(target_family = "wasm"))]
pub use crossbeam_channel::Receiver;

#[cfg(not(target_family = "wasm"))]
pub type NotifyEvent = notify::Result<notify::Event>;

#[cfg(target_family = "wasm")]
pub type NotifyEvent = ();

#[cfg(target_family = "wasm")]
use std::marker::PhantomData;

#[cfg(target_family = "wasm")]
pub type Receiver<T> = PhantomData<T>;

/// Interface for reading and watching files.                                  
pub trait VfsHandler: Sync + Send {
    /// Load the content of the given file, returning [`None`] if it does not  
    /// exists.                                                                
    fn read_and_watch_file(&self, path: &PathWithScheme) -> Option<String>;
    fn notify_receiver(&self) -> Option<&Receiver<NotifyEvent>>;
    fn on_invalidated_in_memory_file(&self, path: PathWithScheme);
    fn read_and_watch_dir(
        &self,
        workspaces: &[Arc<Workspace>],
        path: &str,
        parent: Parent,
    ) -> Entries;

    fn read_and_watch_entry(
        &self,
        workspaces: &[Arc<Workspace>],
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

    fn normalize_unchecked_abs_path(&self, path: &str) -> Arc<NormalizedPath> {
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

    fn parent_of_absolute_path<'path>(&self, path: &'path AbsPath) -> Option<&'path AbsPath> {
        Some(AbsPath::new(path.as_ref().parent()?.to_str().unwrap()))
    }

    fn path_relative_to(&self, from: &AbsPath, to: &Path) -> Option<String> {
        path_relative_to(from, to, self.separator())
    }

    fn split_off_first_item<'a>(&self, path: &'a str) -> (&'a str, Option<&'a str>) {
        let mut found = path.find(self.separator());
        if cfg!(target_os = "windows") {
            // Windows allows path with mixed separators
            if let Some(found_slash) = path.find('/')
                && found.is_none_or(|found| found <= found_slash)
            {
                found = Some(found_slash)
            }
        }
        if let Some(pos) = found {
            (&path[..pos], Some(&path[pos + 1..]))
        } else {
            (path, None)
        }
    }

    fn split_off_last_item<'a>(&self, path: &'a str) -> (Option<&'a str>, &'a str) {
        let mut found = path.rfind(self.separator());
        if cfg!(target_os = "windows") {
            // Windows allows path with mixed separators
            if let Some(found_slash) = path.rfind('/')
                && found.is_none_or(|found| found >= found_slash)
            {
                found = Some(found_slash)
            }
        }
        if let Some(pos) = found {
            (Some(&path[..pos]), &path[pos + 1..])
        } else {
            (None, path)
        }
    }
}

fn path_relative_to(from: &AbsPath, to: &Path, separator: char) -> Option<String> {
    let mut from_it = from.as_ref().components().peekable();
    let mut to_it = to.components().peekable();

    // Roots must match
    match (from_it.next(), to_it.next()) {
        (Some(a), Some(b)) if a == b => {}
        _ => return None,
    }

    // Find common prefix
    loop {
        match (from_it.peek(), to_it.peek()) {
            (Some(a), Some(b)) if a == b => {
                from_it.next();
                to_it.next();
            }
            _ => break,
        }
    }

    // Remaining components in `to` become `..`
    let mut out = String::new();
    for _ in to_it {
        out.push_str("..");
        out.push(separator);
    }

    // Remaining components in `to`
    let mut needs_separator = false;
    for c in from_it {
        if let Component::Normal(name) = c {
            if needs_separator {
                out.push(separator);
            }
            out.push_str(name.to_str().unwrap());
            needs_separator = true;
        }
    }
    Some(out)
}

#[cfg(test)]
mod tests {
    use crate::*;

    #[test]
    fn test_path_relative_to() {
        let abs = AbsPath::new("/foo/bar/baz");
        let check = |s: &str| path_relative_to(abs, Path::new(s), '/');
        assert_eq!(check("/foo/bar"), Some("baz".into()));
        assert_eq!(check("/foo/bar/"), Some("baz".into()));
        assert_eq!(check("/foo/"), Some("bar/baz".into()));
        assert_eq!(check("/foo"), Some("bar/baz".into()));
        assert_eq!(check("/"), Some("foo/bar/baz".into()));

        assert_eq!(check("/bar"), Some("../foo/bar/baz".into()));
        assert_eq!(check("/baz"), Some("../foo/bar/baz".into()));
        assert_eq!(check("/foo/other"), Some("../bar/baz".into()));
        assert_eq!(check("/foo/other/other2"), Some("../../bar/baz".into()));
        assert_eq!(check("/foo/bar/other"), Some("../baz".into()));
        assert_eq!(check("/foo/bar/other/other2"), Some("../../baz".into()));

        // Edge cases
        let root = AbsPath::new("/");
        assert_eq!(path_relative_to(root, Path::new(""), '/'), None);
        assert_eq!(path_relative_to(root, Path::new("/"), '/'), Some("".into()));
        assert_eq!(
            path_relative_to(root, Path::new("/foo"), '/'),
            Some("../".into())
        );
    }
}
