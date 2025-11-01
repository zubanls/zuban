use std::{
    path::{Path, PathBuf},
    sync::Arc,
};

use crate::{
    AbsPath, DirectoryEntry, Entries, FileEntry, NormalizedPath, Parent, PathWithScheme, VfsHandler,
};

pub type SimpleLocalFS = LocalFS<Box<dyn Fn(PathWithScheme) + Sync + Send>>;

#[derive(Clone)]
pub struct LocalFS<T: Fn(PathWithScheme) + Sync + Send> {
    on_invalidated_in_memory_file: Option<T>,
    separator: char,
}

impl<T: Fn(PathWithScheme) + Sync + Send> Default for LocalFS<T> {
    fn default() -> Self {
        Self {
            on_invalidated_in_memory_file: None,
            separator: '/',
        }
    }
}

impl<T: Fn(PathWithScheme) + Sync + Send> LocalFS<T> {
    pub fn without_watcher() -> Self {
        Self::default()
    }

    pub fn with_watcher(on_invalidated_in_memory_file: T) -> Self {
        Self {
            on_invalidated_in_memory_file: Some(on_invalidated_in_memory_file),
            ..Self::default()
        }
    }

    pub fn watch<P: AsRef<Path>>(&self, _path: P) {}

    pub fn current_dir(&self) -> Arc<AbsPath> {
        self.unchecked_abs_path("")
    }

    pub fn normalized_path_from_current_dir(&self, p: &str) -> Arc<NormalizedPath> {
        self.normalize_rc_path(self.absolute_path(&self.current_dir(), p))
    }

    fn join_path(&self, base: &AbsPath, name: &str) -> PathBuf {
        let base_path = Path::new(&**base);
        if base_path.as_os_str().is_empty() {
            PathBuf::from(name)
        } else {
            base_path.join(name)
        }
    }
}

impl<T: Fn(PathWithScheme) + Sync + Send> VfsHandler for LocalFS<T> {
    fn read_and_watch_file(&self, _path: &PathWithScheme) -> Option<String> {
        None
    }

    fn notify_receiver(&self) -> Option<&crate::WatcherReceiver> {
        None
    }

    fn on_invalidated_in_memory_file(&self, path: PathWithScheme) {
        if let Some(callback) = self.on_invalidated_in_memory_file.as_ref() {
            callback(path);
        }
    }

    fn read_and_watch_dir(&self, _path: &str, _parent: Parent) -> Entries {
        Entries::from_vec(Vec::new())
    }

    fn read_and_watch_entry(
        &self,
        _path: &str,
        _parent: Parent,
        _replace_name: &str,
    ) -> Option<DirectoryEntry> {
        None
    }

    fn separator(&self) -> char {
        self.separator
    }

    fn split_off_folder<'a>(&self, path: &'a str) -> (&'a str, Option<&'a str>) {
        if path.is_empty() {
            return (path, None);
        }
        let bytes = path.as_bytes();
        if let Some(pos) = bytes.iter().position(|b| *b == b'/' || *b == b'\\') {
            let (head, tail) = path.split_at(pos);
            let tail = &tail[1..];
            (head, if tail.is_empty() { None } else { Some(tail) })
        } else {
            (path, None)
        }
    }

    fn join(&self, path: &AbsPath, name: &str) -> Arc<AbsPath> {
        let joined = self.join_path(path, name);
        let joined = joined.to_str().unwrap_or(name);
        self.unchecked_abs_path(joined)
    }

    fn is_case_sensitive(&self) -> bool {
        true
    }
}
