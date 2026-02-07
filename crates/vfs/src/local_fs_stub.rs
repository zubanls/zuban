use std::{
    path::{Path, PathBuf},
    sync::Arc,
};

use crate::{
    AbsPath, DirectoryEntry, Entries, NormalizedPath, NotifyEvent, Parent, PathWithScheme,
    VfsHandler,
};

pub type SimpleLocalFS = LocalFS;

#[derive(Clone, Default)]
pub struct LocalFS;

impl LocalFS {
    pub fn without_watcher() -> Self {
        Self
    }
    pub fn with_watcher<T>(_: T) -> Self {
        Self
    }
    pub fn watch<P: AsRef<Path>>(&self, _: P) {}
    pub fn current_dir(&self) -> Arc<AbsPath> {
        self.unchecked_abs_path("")
    }
    pub fn normalized_path_from_current_dir(&self, p: &str) -> Arc<NormalizedPath> {
        self.normalize_rc_path(self.absolute_path(&self.current_dir(), p))
    }
}

impl VfsHandler for LocalFS {
    fn read_and_watch_file(&self, _: &PathWithScheme) -> Option<String> {
        None
    }
    fn notify_receiver(&self) -> Option<&crate::Receiver<NotifyEvent>> {
        None
    }
    fn on_invalidated_in_memory_file(&self, _: PathWithScheme) {}
    fn read_and_watch_dir(&self, _: &str, _: Parent) -> Entries {
        Entries::from_vec(vec![])
    }
    fn read_and_watch_entry(&self, _: &str, _: Parent, _: &str) -> Option<DirectoryEntry> {
        None
    }
    fn separator(&self) -> char {
        '/'
    }
    fn split_off_folder<'a>(&self, path: &'a str) -> (&'a str, Option<&'a str>) {
        if path.is_empty() {
            return (path, None);
        }
        if let Some(pos) = path
            .as_bytes()
            .iter()
            .position(|b| *b == b'/' || *b == b'\\')
        {
            let (head, tail) = path.split_at(pos);
            (
                head,
                if tail.len() > 1 {
                    Some(&tail[1..])
                } else {
                    None
                },
            )
        } else {
            (path, None)
        }
    }
    fn join(&self, path: &AbsPath, name: &str) -> Arc<AbsPath> {
        let p = Path::new(&**path);
        let joined = if p.as_os_str().is_empty() {
            PathBuf::from(name)
        } else {
            p.join(name)
        };
        self.unchecked_abs_path(joined.to_str().unwrap_or(name))
    }
    fn is_case_sensitive(&self) -> bool {
        true
    }
}
