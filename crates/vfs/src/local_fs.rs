use std::{
    cell::RefCell,
    path::{Path, PathBuf},
    rc::Rc,
};

use crossbeam_channel::{unbounded, Receiver};
use notify::{recommended_watcher, RecommendedWatcher, RecursiveMode, Watcher};
use utils::FastHashSet;

use crate::{
    AbsPath, Directory, DirectoryEntry, Entries, FileEntry, NotifyEvent, Parent, PathWithScheme,
    VfsHandler,
};

const GLOBALLY_IGNORED_FOLDERS: [&str; 3] = ["site-packages", "node_modules", "__pycache__"];

pub type SimpleLocalFS = LocalFS<Box<dyn Fn(PathWithScheme)>>;

pub struct LocalFS<T: Fn(PathWithScheme)> {
    watcher: Option<(RefCell<RecommendedWatcher>, Receiver<NotifyEvent>)>,
    already_watched_dirs: RefCell<FastHashSet<PathBuf>>,
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
        self.watch(path);
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
                                match self.follow_and_watch_symlink(dir_entry.path()) {
                                    Ok(resolved) => resolved,
                                    Err(err) => {
                                        tracing::warn!("Follow symlink error, path={path}: {err}");
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

    fn read_and_watch_entry(
        &self,
        path: &str,
        parent: Parent,
        replace_name: &str,
    ) -> Option<DirectoryEntry> {
        let metadata = match std::fs::symlink_metadata(path) {
            Ok(metadata) => metadata,
            Err(err) => {
                tracing::info!("Reading metatdata failed for path={path:?}: {err}");
                return None;
            }
        };
        let resolved = if metadata.is_dir() {
            self.watch(path);
            ResolvedFileType::Directory
        } else if metadata.is_symlink() {
            match self.follow_and_watch_symlink(path) {
                Ok(resolved) => resolved,
                Err(err) => {
                    tracing::info!("read_entry follow symlink error, path={path}: {err}");
                    return None;
                }
            }
        } else {
            debug_assert!(metadata.is_file());
            self.watch(path);
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

    fn is_unnecessary_invalidation(
        &self,
        path: &AbsPath,
        current_entry: Option<&DirectoryEntry>,
    ) -> bool {
        if current_entry.is_some_and(|entry| matches!(entry, DirectoryEntry::Directory(_))) {
            if let Ok(metadata) = std::fs::metadata(path) {
                // The directory might have been created, but is not watched (relevant on Linux,
                // respectively on all operating systems that don't support recursive file
                // watchers).
                self.watch(path);

                // If it is still a directory, so we don't have to invalidate.
                //
                // Metadata changes do not affect our caches and file changes should lead to
                // separate notify events. This is really important on Windows where creating
                // a file leads to a directory change event + a file creation event. On Linux
                // an event is also generated, but for the path of the newly created file
                // (which is what we are intersted in).
                return metadata.is_dir();
            }
        }
        false
    }
}

impl SimpleLocalFS {
    pub fn without_watcher() -> Self {
        Self {
            watcher: None,
            already_watched_dirs: Default::default(),
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
            already_watched_dirs: Default::default(),
            on_invalidated_in_memory_file: Some(on_invalidated_memory_file),
        }
    }

    pub fn watch<P: AsRef<Path>>(&self, path: P) {
        let path = path.as_ref();
        if let Some((watcher, _)) = &self.watcher {
            if cfg!(any(
                target_os = "macos",
                target_os = "windows",
                target_os = "ios"
            )) {
                // On windows adding the watch n times will cause n events. We therefore used to
                // remove the watch before adding it again. This was generally problematic, because
                // it might be modified during that time and we might lose an event.
                // However now that we only watch a path if we do not already watch it it shouldn't
                // be an issue anymore.

                // Linux does not support recursive files.
                match std::fs::canonicalize(path) {
                    Ok(canonicalized) => {
                        let mut already_watched = self.already_watched_dirs.borrow_mut();
                        // General information:
                        // MacOS - FSEventStreamCreate: https://developer.apple.com/documentation/coreservices/1443980-fseventstreamcreate
                        // Windows - ReadDirectoryChangesW: https://learn.microsoft.com/en-us/windows/win32/api/winbase/nf-winbase-readdirectorychangesw
                        if let Some(_found) = already_watched
                            .iter()
                            .find(|watched| canonicalized.starts_with(watched))
                        {
                            // TODO While I'm not sure, I think MacOS simply works with paths, so
                            // watching should be fine. On Windows this feels different, because we
                            // are watching a directory handle. This complicates things, because we
                            // always provide a path (can be a file too) to notify. So if the
                            // parent directory of a file is removed (can be the parent of a
                            // symlink target as well) and recreated we might run into issues.
                            // So there might be edge cases where we lose watches for now.
                            // As one possible workaround we try to rewatch the same file again.
                            //
                            // This might however still not work in cases where the file tree is
                            // removed a level lower and then recreated later. In essence we would
                            // need to watch ALL ancestors (however this is probably also an issue
                            // on Linux and is only fine on MacOS).
                            if cfg!(target_os = "windows") {
                                /* TODO for now we disabled this
                                if &canonicalized == found {
                                    let _ = watcher.borrow_mut().unwatch(&canonicalized);
                                    log_notify_error(
                                        watcher
                                            .borrow_mut()
                                            .watch(&canonicalized, RecursiveMode::Recursive),
                                    );
                                    tracing::debug!("Removed and re-added recursive watch for {canonicalized:?}");
                                    already_watched.insert(canonicalized);
                                }
                                */
                            }
                        } else {
                            log_notify_error(
                                watcher
                                    .borrow_mut()
                                    .watch(&canonicalized, RecursiveMode::Recursive),
                            );
                            tracing::debug!("Added recursive watch for {canonicalized:?}");
                            already_watched.insert(canonicalized);
                        }
                    }
                    Err(err) => {
                        tracing::error!(
                            "Failed to canonicalize path {path:?} and did therefore not watch, because: {err}"
                        );
                    }
                }
            } else {
                log_notify_error(
                    watcher
                        .borrow_mut()
                        .watch(path, RecursiveMode::NonRecursive),
                );
                tracing::debug!("Added watch for {path:?}");
            }
        }
    }

    pub fn current_dir(&self) -> Rc<AbsPath> {
        self.unchecked_abs_path(std::env::current_dir().unwrap().to_str().unwrap())
    }

    pub fn abs_path_from_current_dir(&self, p: &str) -> Rc<AbsPath> {
        self.absolute_path(&self.current_dir(), p)
    }

    fn follow_and_watch_symlink<P: AsRef<Path>>(
        &self,
        path: P,
    ) -> Result<ResolvedFileType, String> {
        self.follow_symlink_internal(path.as_ref(), path.as_ref())
    }

    fn follow_symlink_internal(
        &self,
        origin_path: &Path,
        path: &Path,
    ) -> Result<ResolvedFileType, String> {
        self.watch(path);
        let target_path = std::fs::read_link(path).map_err(|e| format!("{e}"))?;
        let metadata = std::fs::symlink_metadata(&target_path).map_err(|e| format!("{e}"))?;
        let file_type = metadata.file_type();
        if file_type.is_dir() {
            // We use same_file here for comparing the entries, because just comparing the paths
            // can be hard, because they might be symlinks to e.g. `.`. Maybe cannonicalized paths
            // could work, but the walkdir crate works like that, so we are probably on the safe
            // side, because lots of well-known projects are using it.
            let target_handle =
                same_file::Handle::from_path(&target_path).map_err(|e| format!("{e}"))?;
            for p in origin_path.ancestors() {
                if let Ok(ancestor_handle) = same_file::Handle::from_path(p) {
                    if target_handle == ancestor_handle {
                        return Err(format!("Detected cycle in {target_path:?}"));
                    }
                }
            }
            Ok(ResolvedFileType::Directory)
        } else if file_type.is_symlink() {
            self.follow_symlink_internal(origin_path, &target_path)
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
