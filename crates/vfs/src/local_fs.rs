use std::{cell::RefCell, path::Path};

use crossbeam_channel::{unbounded, Receiver};
use notify::{recommended_watcher, EventKind, RecommendedWatcher, RecursiveMode, Watcher};
use walkdir::WalkDir;

use crate::{NotifyEvent, VfsHandler};

const STUBS_SUFFIX: &str = "-stubs";

pub struct LocalFS {
    watcher: Option<(RefCell<RecommendedWatcher>, Receiver<NotifyEvent>)>,
}

impl VfsHandler for LocalFS {
    fn read_and_watch_file(&self, path: &str) -> Option<String> {
        tracing::debug!("Read from FS: {path}");
        // Need to watch first, because otherwise the file might be read deleted and then watched.
        self.watch(path);
        let result = std::fs::read_to_string(path);
        if let Err(error) = &result {
            tracing::error!("Tried to read {path} but failed: {error}");
        }
        result.ok()
    }

    fn walk_and_watch_dirs(&self, path: &str) {
        let walker = WalkDir::new(path)
            .follow_links(true)
            .into_iter()
            .filter_entry(|entry| {
                entry.file_name().to_str().is_some_and(|name| {
                    if name.ends_with(".py") || name.ends_with(".pyi") || name == "py.typed" {
                        return true;
                    }
                    if name == "__pycache__" {
                        return false;
                    }
                    // Keep potential folders around
                    !name.contains('.') && (!name.contains('-') || name.ends_with(STUBS_SUFFIX))
                })
            });
        for e in walker {
            match e {
                Ok(dir_entry) => {
                    let p = dir_entry.path();
                    if let Some(path) = p.to_str() {
                        self.watch(path)
                    } else {
                        tracing::info!("Walkdir ignored {p:?}, because it's not UTF-8")
                    }
                }
                Err(e) => tracing::error!("Walkdir error (base: {path}): {e}"),
            }
        }
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

    fn watch(&self, path: &str) {
        if let Some((watcher, _)) = &self.watcher {
            tracing::debug!("Added watch for {path}");
            log_notify_error(
                watcher
                    .borrow_mut()
                    .watch(Path::new(path), RecursiveMode::NonRecursive),
            );
        }
    }
}

fn log_notify_error<T>(res: notify::Result<T>) -> Option<T> {
    res.map_err(|err| tracing::warn!("notify error: {}", err))
        .ok()
}
