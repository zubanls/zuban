use std::{
    cell::RefCell,
    path::{Path, PathBuf},
    rc::Rc,
};

use crossbeam_channel::{unbounded, Receiver};
use notify::{recommended_watcher, RecommendedWatcher, RecursiveMode, Watcher};
use walkdir::WalkDir;

use crate::{
    tree::MissingEntry, Directory, DirectoryEntry, FileEntry, NotifyEvent, Parent, VfsHandler,
};

const STUBS_SUFFIX: &str = "-stubs";

pub struct LocalFS {
    watcher: Option<(RefCell<RecommendedWatcher>, Receiver<NotifyEvent>)>,
}

impl VfsHandler for LocalFS {
    fn read_and_watch_file(&self, path: &str) -> Option<String> {
        tracing::debug!("Read from FS: {path}");
        // Need to watch first, because otherwise the file might be read deleted and then watched.
        self.watch(Path::new(path));
        let result = std::fs::read_to_string(path);
        if let Err(error) = &result {
            tracing::error!("Tried to read {path} but failed: {error}");
        }
        result.ok()
    }

    fn walk_and_watch_dirs(&self, path: &str, initial_parent: Parent) -> DirectoryEntry {
        let is_relevant_name =
            |name: &str| name.ends_with(".py") || name.ends_with(".pyi") || name == "py.typed";
        let path = path.trim_end_matches(self.separator());

        let mut is_first = true;
        self.watch(Path::new(path));
        let walker = WalkDir::new(path)
            .follow_links(true)
            .into_iter()
            .filter_entry(|entry| {
                entry.file_name().to_str().is_some_and(|name| {
                    if is_first {
                        // We always want the base dir
                        is_first = false;
                        return true;
                    }
                    if is_relevant_name(name) {
                        return true;
                    }
                    if name == "__pycache__" {
                        return false;
                    }
                    // Keep potential folders around. Most punctuation characters are not allowed
                    !name.chars().any(|c| match c {
                        '-' => !name.ends_with(STUBS_SUFFIX),
                        '_' => false,
                        _ => c.is_ascii_punctuation(),
                    })
                })
            });

        let mut stack: Vec<(PathBuf, Rc<Directory>)> = vec![];

        for e in walker {
            match e {
                Ok(dir_entry) => {
                    let p = dir_entry.path();
                    if !stack.is_empty() {
                        while !p.starts_with(&stack.last().unwrap().0) {
                            let n = stack.pop().unwrap().1;
                            stack
                                .last_mut()
                                .unwrap()
                                .1
                                .entries
                                .borrow_mut()
                                .push(DirectoryEntry::Directory(n));
                        }
                    }
                    let name = dir_entry.file_name();
                    if let Some(name) = name.to_str() {
                        match dir_entry.metadata() {
                            Ok(m) => {
                                let parent = if let Some(last) = stack.last() {
                                    let parent_dir = &last.1;
                                    match &parent_dir.parent {
                                        Parent::Workspace(root) if stack.len() == 1 => {
                                            Parent::Workspace(root.clone())
                                        }
                                        _ => Parent::Directory(Rc::downgrade(parent_dir)),
                                    }
                                } else {
                                    initial_parent.clone()
                                };
                                if m.is_dir() {
                                    self.watch(p);
                                    stack.push((p.to_owned(), Directory::new(parent, name.into())));
                                } else {
                                    let dir_entry =
                                        DirectoryEntry::File(FileEntry::new(parent, name.into()));
                                    if let Some(last_dir) = stack.last_mut() {
                                        last_dir.1.entries.borrow_mut().push(dir_entry)
                                    } else {
                                        if is_relevant_name(name) {
                                            return dir_entry;
                                        }
                                        break; // This case will just return a missing entry, which
                                               // is fine, because the file is not relevant
                                    }
                                }
                            }
                            Err(err) => {
                                tracing::error!("Walkdir metadata error (base: {path}): {err}")
                            }
                        }
                    } else {
                        tracing::info!("Walkdir ignored {p:?}, because it's not UTF-8")
                    }
                }
                Err(e) => {
                    match e.io_error().map(|e| e.kind()) {
                        // Not found is a very ususal and expected thing so we lower the severity
                        // here.
                        Some(std::io::ErrorKind::NotFound) => {
                            tracing::debug!("Walkdir error (base: {path}): {e}")
                        }
                        _ => tracing::error!("Walkdir error (base: {path}): {e}"),
                    };
                }
            }
        }
        while let Some(current) = stack.pop() {
            if let Some(parent) = stack.last_mut() {
                parent
                    .1
                    .entries
                    .borrow_mut()
                    .push(DirectoryEntry::Directory(current.1))
            } else {
                return DirectoryEntry::Directory(current.1);
            }
        }
        // TODO There is a chance that the dir does not exist and might be created later. We
        // should actually "watch" for that.
        DirectoryEntry::MissingEntry(MissingEntry {
            name: "".into(),
            invalidations: Default::default(),
        })
    }

    fn notify_receiver(&self) -> Option<&Receiver<NotifyEvent>> {
        self.watcher.as_ref().map(|(_, r)| r)
    }

    fn split_off_folder<'a>(&self, path: &'a str) -> (&'a str, Option<&'a str>) {
        if let Some(pos) = path.find(self.separator()) {
            (&path[..pos], Some(&path[pos + 1..]))
        } else {
            (path, None)
        }
    }
}

impl LocalFS {
    pub fn with_watcher() -> Self {
        let (watcher_sender, watcher_receiver) = unbounded();
        let watcher = log_notify_error(recommended_watcher(move |event| {
            // we don't care about the error. If sending fails that usually
            // means we were dropped, so unwrapping will just add to the
            // panic noise.

            if let Err(err) = watcher_sender.send(event) {
                tracing::warn!("Watch sender error: {err}")
            }
        }));
        Self {
            watcher: watcher.map(|w| (RefCell::new(w), watcher_receiver)),
        }
    }

    pub fn without_watcher() -> Self {
        Self { watcher: None }
    }

    fn watch(&self, path: &Path) {
        if let Some((watcher, _)) = &self.watcher {
            tracing::debug!("Added watch for {path:?}");
            log_notify_error(
                watcher
                    .borrow_mut()
                    .watch(path, RecursiveMode::NonRecursive),
            );
        }
    }
}

fn log_notify_error<T>(res: notify::Result<T>) -> Option<T> {
    res.map_err(|err| match &err.kind {
        notify::ErrorKind::Io(io_err) if matches!(io_err.kind(), std::io::ErrorKind::NotFound) => {
            // Adjust the severity here. It's normal that we couldn't watch something, because a
            // lot of the time the file doesn't exist when trying to watch something.
            tracing::debug!("notify error: {}", err)
        }
        _ => tracing::warn!("notify error: {}", err),
    })
    .ok()
}
