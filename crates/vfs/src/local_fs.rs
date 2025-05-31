use std::{cell::RefCell, path::Path, rc::Rc};

use crossbeam_channel::{unbounded, Receiver};
use notify::{recommended_watcher, RecommendedWatcher, RecursiveMode, Watcher};

use crate::{
    AbsPath, Directory, DirectoryEntry, Entries, FileEntry, NotifyEvent, Parent, PathWithScheme,
    VfsHandler,
};

const GLOBALLY_IGNORED_FOLDERS: [&str; 3] = ["site-packages", "node_modules", "__pycache__"];

pub type SimpleLocalFS = LocalFS<Box<dyn Fn(PathWithScheme)>>;

pub struct LocalFS<T: Fn(PathWithScheme)> {
    watcher: Option<(RefCell<RecommendedWatcher>, Receiver<NotifyEvent>)>,
    on_invalidated_in_memory_file: Option<T>,
}

impl<T: Fn(PathWithScheme)> VfsHandler for LocalFS<T> {
    fn read_and_watch_file(&self, path: &PathWithScheme) -> Option<String> {
        tracing::debug!("Read from FS: {}", path.as_uri());
        if **path.scheme != *"file" {
            tracing::error!(
                "Tried to read from FS for the scheme: {}, scheme file was expected",
                &path.scheme
            );
            return None;
        }
        let path = &path.path;
        // Need to watch first, because otherwise the file might be read deleted and then watched.
        let p = path.as_ref().as_ref();
        self.watch(p);
        let result = std::fs::read_to_string(p);
        if let Err(error) = &result {
            tracing::warn!("Tried to read {path} but failed: {error}");
        }
        result.ok()
    }

    fn read_and_watch_dir(&self, path: &str, parent: Parent) -> Entries {
        let trace_err = |from, e: std::io::Error| match e.kind() {
            // Not found is a very ususal and expected thing so we lower the severity
            // here.
            std::io::ErrorKind::NotFound => {
                tracing::debug!("{from} error (base: {path}): {e}")
            }
            _ => tracing::error!("{from} error (base: {path}): {e}"),
        };
        let iterator = match std::fs::read_dir(path) {
            Ok(iterator) => iterator,
            Err(e) => {
                trace_err("Initial read dir", e);
                return Entries::default();
            }
        };
        let mut entries = vec![];
        for dir_entry in iterator {
            match dir_entry {
                Ok(dir_entry) => {
                    let name = dir_entry.file_name();
                    let Ok(name) = name.into_string() else {
                        let p = dir_entry.path();
                        tracing::info!("Listdir ignored {p:?}, because it's not UTF-8");
                        continue;
                    };
                    match dir_entry.file_type() {
                        Ok(file_type) => {
                            let new = if file_type.is_dir() {
                                ResolvedFileType::Directory
                            } else if file_type.is_symlink() {
                                match self.follow_symlink(dir_entry.path()) {
                                    Ok(resolved) => resolved,
                                    Err(err) => {
                                        tracing::error!("Follow symlink error, path={path}: {err}");
                                        continue;
                                    }
                                }
                            } else {
                                debug_assert!(file_type.is_file());
                                ResolvedFileType::File
                            };
                            if let Some(entry) = new.into_dir_entry(parent.clone(), name) {
                                entries.push(entry)
                            }
                        }
                        Err(err) => {
                            let path = dir_entry.path();
                            tracing::error!(
                                "Listdir filetype did error (path={path:?}, name={name}): {err}"
                            )
                        }
                    }
                }
                Err(e) => trace_err("Read dir entry", e),
            }
        }
        Entries::from_vec(entries)
    }

    fn read_entry(&self, path: &str, parent: Parent, replace_name: &str) -> Option<DirectoryEntry> {
        let metadata = match std::fs::symlink_metadata(path) {
            Ok(metadata) => metadata,
            Err(err) => {
                tracing::info!("Reading metatdata failed for path={path:?}: {err}");
                return None;
            }
        };
        let resolved = if metadata.is_dir() {
            ResolvedFileType::Directory
        } else if metadata.is_symlink() {
            match self.follow_symlink(path) {
                Ok(resolved) => resolved,
                Err(err) => {
                    tracing::info!("read_entry follow symlink error, path={path}: {err}");
                    return None;
                }
            }
        } else {
            debug_assert!(metadata.is_file());
            ResolvedFileType::File
        };
        resolved.into_dir_entry(parent, replace_name)
    }

    fn notify_receiver(&self) -> Option<&Receiver<NotifyEvent>> {
        self.watcher.as_ref().map(|(_, r)| r)
    }

    fn split_off_folder<'a>(&self, path: &'a str) -> (&'a str, Option<&'a str>) {
        let mut found = path.find(self.separator());
        if cfg!(target_os = "windows") {
            // Windows allows path with mixed separators
            if let Some(found_slash) = path.find('/') {
                if found.is_none_or(|found| found <= found_slash) {
                    found = Some(found_slash)
                }
            }
        }
        if let Some(pos) = found {
            (&path[..pos], Some(&path[pos + 1..]))
        } else {
            (path, None)
        }
    }

    fn on_invalidated_in_memory_file(&self, path: PathWithScheme) {
        if let Some(callback) = self.on_invalidated_in_memory_file.as_ref() {
            callback(path)
        }
    }
}

impl SimpleLocalFS {
    pub fn without_watcher() -> Self {
        Self {
            watcher: None,
            on_invalidated_in_memory_file: None,
        }
    }
}

impl<T: Fn(PathWithScheme)> LocalFS<T> {
    pub fn with_watcher(on_invalidated_memory_file: T) -> Self {
        let (watcher_sender, watcher_receiver) = unbounded();
        let watcher = log_notify_error(recommended_watcher(move |event| {
            // we don't care about the error. If sending fails that usually
            // means we were dropped, so unwrapping will just add to the
            // panic noise.

            if let Err(err) = watcher_sender.send(event) {
                tracing::warn!("Watch sender error: {err} (might be fine if terminating)")
            }
        }));
        Self {
            watcher: watcher.map(|w| (RefCell::new(w), watcher_receiver)),
            on_invalidated_in_memory_file: Some(on_invalidated_memory_file),
        }
    }

    pub fn watch(&self, path: &Path) {
        if let Some((watcher, _)) = &self.watcher {
            if cfg!(target_os = "windows") {
                // On windows adding the watch n times will cause n events. We therefore have to
                // remove the watch before adding it again. This is generally problematic, because
                // it might be modified during that time and we might lose an event.
                let _ = watcher.borrow_mut().unwatch(path);
            }
            log_notify_error(
                watcher
                    .borrow_mut()
                    .watch(path, RecursiveMode::NonRecursive),
            );
            tracing::debug!("Added watch for {path:?}");
        }
    }

    pub fn current_dir(&self) -> Rc<AbsPath> {
        self.unchecked_abs_path(
            std::env::current_dir()
                .unwrap()
                .into_os_string()
                .into_string()
                .unwrap(),
        )
    }

    pub fn abs_path_from_current_dir(&self, p: String) -> Rc<AbsPath> {
        self.absolute_path(&self.current_dir(), p)
    }

    fn follow_symlink<P: AsRef<Path>>(&self, path: P) -> std::io::Result<ResolvedFileType> {
        let path = path.as_ref();
        self.watch(path);
        let target_path = std::fs::read_link(path)?;
        let metadata = std::fs::symlink_metadata(&target_path)?;
        let file_type = metadata.file_type();
        if file_type.is_dir() {
            Ok(ResolvedFileType::Directory)
        } else if file_type.is_symlink() {
            self.follow_symlink(target_path)
        } else {
            debug_assert!(file_type.is_file());
            Ok(ResolvedFileType::File)
        }
    }
}

enum ResolvedFileType {
    File,
    Directory,
}

impl ResolvedFileType {
    fn into_dir_entry<N: Into<Box<str>> + AsRef<str>>(
        self,
        parent: Parent,
        name: N,
    ) -> Option<DirectoryEntry> {
        // This logic is derived from how Mypy does it. It ignores only very specific
        // folders: https://mypy.readthedocs.io/en/stable/command_line.html#cmdoption-mypy-exclude
        let n = name.as_ref();
        if n.starts_with('.') || GLOBALLY_IGNORED_FOLDERS.contains(&n) {
            return None;
        }

        Some(match self {
            ResolvedFileType::File => DirectoryEntry::File(FileEntry::new(parent, name.into())),
            ResolvedFileType::Directory => {
                DirectoryEntry::Directory(Directory::new(parent, name.into()))
            }
        })
    }
}

fn log_notify_error<T>(res: notify::Result<T>) -> Option<T> {
    res.map_err(|err| match &err.kind {
        notify::ErrorKind::Io(io_err) if matches!(io_err.kind(), std::io::ErrorKind::NotFound) => {
            // Adjust the severity here. It's normal that we couldn't watch something, because a
            // lot of the time the file doesn't exist when trying to watch something.
            tracing::debug!("notify error: {}", err)
        }
        notify::ErrorKind::PathNotFound => {
            // Same as above
            tracing::debug!("notify error: {}", err)
        }
        _ => tracing::warn!("notify error: {}", err),
    })
    .ok()
}
