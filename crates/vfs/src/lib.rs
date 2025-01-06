// Some parts are copied from rust-analyzer

use std::path::Path;

use crossbeam_channel::{unbounded, Receiver, Sender};
use notify::{recommended_watcher, EventKind, RecommendedWatcher, RecursiveMode, Watcher};
use walkdir::WalkDir;

type NotifyEvent = notify::Result<notify::Event>;

const STUBS_SUFFIX: &str = "-stubs";

/// Interface for reading and watching files.                                  
pub trait Vfs {
    /*
    /// Spawn a new handle with the given `sender`.
    fn spawn(workspaces: &[&str]) -> Self
    where
        Self: Sized;
    // -> Workspaces, Sender<NeedsWatch>, Receiver<Foo>
    */

    /// Load the content of the given file, returning [`None`] if it does not  
    /// exists.                                                                
    fn read_and_watch_file(&mut self, path: &str) -> Option<String>;
}

pub struct LocalFS {
    watcher: Option<(RecommendedWatcher, Receiver<NotifyEvent>)>,
}

impl Vfs for LocalFS {
    fn read_and_watch_file(&mut self, path: &str) -> Option<String> {
        tracing::debug!("Read from FS: {path}");
        // Need to watch first, because otherwise the file might be read deleted and then watched.
        self.watch(path);
        let result = std::fs::read_to_string(path);
        if let Err(error) = &result {
            tracing::error!("Tried to read {path} but failed: {error}");
        }
        result.ok()
    }
}

impl LocalFS {
    fn with_watcher() -> Self {
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
            watcher: watcher.map(|w| (w, watcher_receiver)),
        }
    }

    fn without_watcher() -> Self {
        Self { watcher: None }
    }

    fn walk_and_watch_dirs(path: &str) {
        let x = WalkDir::new(path)
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
    }

    fn watch(&mut self, path: &str) {
        if let Some((watcher, _)) = &mut self.watcher {
            log_notify_error(watcher.watch(Path::new(path), RecursiveMode::NonRecursive));
        }
    }
}

fn log_notify_error<T>(res: notify::Result<T>) -> Option<T> {
    res.map_err(|err| tracing::warn!("notify error: {}", err))
        .ok()
}

/*
struct ZubanPart {
    initial_dir_walkers: Vec<WalkDir>,
    read_file: Box,
}

fn spawn(workspaces: &[&str]) -> (ZubanPart, NotifyPart) {}

enum WorkspaceChange {
    File(path),
}

enum Read {}

enum VFSUpdate {
    Vec<WorkspaceChange>,
    ProjectChanged,
}
*/
