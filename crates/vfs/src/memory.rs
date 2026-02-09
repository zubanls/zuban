use std::{
    collections::{BTreeSet, HashMap},
    path::{Component, Path, PathBuf},
    sync::{Arc, RwLock},
};

use crate::{
    AbsPath, Directory, DirectoryEntry, Entries, FileEntry, NotifyEvent, Parent, PathWithScheme,
    Receiver, VfsHandler,
};

#[derive(Clone, Default)]
pub struct InMemoryFs {
    inner: Arc<Inner>,
}

#[derive(Default)]
struct Inner {
    files: RwLock<HashMap<String, String>>,
    separator: char,
}

impl InMemoryFs {
    pub fn new() -> Self {
        Self {
            inner: Arc::new(Inner {
                files: Default::default(),
                separator: '/',
            }),
        }
    }

    pub fn set_file<S: AsRef<str>, C: Into<String>>(&self, path: S, contents: C) {
        let key = normalize_key(path.as_ref());
        self.inner
            .files
            .write()
            .unwrap()
            .insert(key, contents.into());
    }

    pub fn remove_file<S: AsRef<str>>(&self, path: S) {
        let key = normalize_key(path.as_ref());
        self.inner.files.write().unwrap().remove(&key);
    }

    pub fn read_file<S: AsRef<str>>(&self, path: S) -> Option<String> {
        let key = normalize_key(path.as_ref());
        self.inner.files.read().unwrap().get(&key).cloned()
    }

    pub fn clear(&self) {
        self.inner.files.write().unwrap().clear();
    }

    fn separator(&self) -> char {
        self.inner.separator
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

impl VfsHandler for InMemoryFs {
    fn read_and_watch_file(&self, path: &PathWithScheme) -> Option<String> {
        self.read_file(path.path.to_string())
    }

    fn notify_receiver(&self) -> Option<&Receiver<NotifyEvent>> {
        None
    }

    fn on_invalidated_in_memory_file(&self, _path: PathWithScheme) {}

    fn read_and_watch_dir(&self, path: &str, parent: Parent) -> Entries {
        let base = normalize_key(path);
        let mut file_children = Vec::new();
        let mut dir_children: BTreeSet<String> = BTreeSet::new();

        let prefix = if base.is_empty() {
            String::new()
        } else {
            format!("{base}/")
        };

        for key in self.inner.files.read().unwrap().keys() {
            if base.is_empty() {
                if let Some((first, rest)) = key.split_once('/') {
                    if rest.is_empty() {
                        file_children.push(first.to_string());
                    } else {
                        dir_children.insert(first.to_string());
                    }
                } else if !key.is_empty() {
                    file_children.push(key.clone());
                }
            } else if key == &base {
                file_children.push(key.clone());
            } else if let Some(stripped) = key.strip_prefix(&prefix) {
                if let Some((segment, rest)) = stripped.split_once('/') {
                    if rest.is_empty() {
                        file_children.push(segment.to_string());
                    } else {
                        dir_children.insert(segment.to_string());
                    }
                } else if !stripped.is_empty() {
                    file_children.push(stripped.to_string());
                }
            }
        }

        file_children.sort();

        let mut entries = Vec::with_capacity(dir_children.len() + file_children.len());
        for dir in dir_children {
            entries.push(DirectoryEntry::Directory(Directory::new(
                parent.clone(),
                dir.into_boxed_str(),
            )));
        }
        for file in file_children {
            entries.push(DirectoryEntry::File(FileEntry::new(
                parent.clone(),
                file.into_boxed_str(),
            )));
        }
        Entries::from_vec(entries)
    }

    fn read_and_watch_entry(
        &self,
        path: &str,
        parent: Parent,
        replace_name: &str,
    ) -> Option<DirectoryEntry> {
        let key = normalize_key(path);
        let files = self.inner.files.read().unwrap();
        if files.contains_key(&key) {
            return Some(DirectoryEntry::File(FileEntry::new(
                parent,
                replace_name.into(),
            )));
        }
        let prefix = format!("{key}/");
        if files.keys().any(|candidate| candidate.starts_with(&prefix)) {
            return Some(DirectoryEntry::Directory(Directory::new(
                parent,
                replace_name.into(),
            )));
        }
        None
    }

    fn separator(&self) -> char {
        self.separator()
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

fn normalize_key(path: &str) -> String {
    let mut buf = PathBuf::new();
    for component in Path::new(path).components() {
        match component {
            Component::CurDir => {}
            Component::ParentDir => {
                buf.pop();
            }
            other => buf.push(other.as_os_str()),
        }
    }
    let normalized = buf
        .to_str()
        .map(|s| s.replace('\\', "/"))
        .unwrap_or_else(|| path.replace('\\', "/"));
    normalized.trim_matches('/').to_string()
}
