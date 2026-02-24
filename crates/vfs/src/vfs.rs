use std::{
    collections::HashMap,
    ops::BitOrAssign,
    pin::Pin,
    sync::{Arc, OnceLock},
};

use tracing::Level;
use utils::{FastHashSet, InsertOnlyVec};

use crate::{
    AbsPath, DirOrFile, Directory, DirectoryEntry, FileEntry, FileIndex, GitignoreFile,
    NormalizedPath, Parent, VfsHandler, WorkspaceKind,
    tree::{AddedKind, InvalidationDetail, Invalidations},
    workspaces::Workspaces,
};

thread_local! {
    static FILE_SCHEME: Arc<Box<str>> = Arc::new("file".into());
}

pub(crate) type Scheme = Arc<Box<str>>;

fn file_scheme() -> Scheme {
    FILE_SCHEME.with(|f| f.clone())
}

pub trait VfsFile: Unpin {
    type Artifacts;
    fn code(&self) -> &str;
    fn into_recoverable_artifacts(self) -> Self::Artifacts;
    fn invalidate_references_to(&mut self, file_index: Option<FileIndex>);
}

struct RecoveryFile<T> {
    path: PathWithScheme,
    artifacts: T,
    invalidates_db: bool,
    is_in_memory_file: bool,
}
pub struct VfsPanicRecovery<T> {
    files: Vec<RecoveryFile<T>>,
}

pub struct Vfs<F> {
    pub handler: Box<dyn VfsHandler>,
    pub workspaces: Workspaces,
    pub files: InsertOnlyVec<FileState<F>>,
    in_memory_files: HashMap<PathWithScheme, InMemoryKind>,
}

enum InMemoryKind {
    File(FileIndex),
    Gitignore(Arc<GitignoreFile>),
}

impl<F: VfsFile> Vfs<F> {
    pub fn new(handler: Box<dyn VfsHandler>) -> Self {
        Self {
            handler,
            workspaces: Default::default(),
            files: Default::default(),
            in_memory_files: Default::default(),
        }
    }

    pub fn with_reused_test_resources<'x>(
        &mut self,
        handler: Box<dyn VfsHandler>,
        type_checked_dirs: impl DoubleEndedIterator<Item = &'x NormalizedPath>,
    ) -> Self
    where
        F: Clone,
    {
        let mut files = vec![];
        let mut workspaces = self.workspaces.clone_with_new_rcs(&*handler);
        for file_state in self.files.iter_mut() {
            fn search_parent(
                vfs_handler: &dyn VfsHandler,
                workspaces: &Workspaces,
                parent: Parent,
                name: &str,
            ) -> DirectoryEntry {
                let tmp;
                let parent_entries = match parent {
                    Parent::Directory(dir) => {
                        tmp = dir.upgrade().unwrap();
                        Directory::entries_with_workspaces(vfs_handler, workspaces, &tmp)
                    }
                    Parent::Workspace(w) => {
                        let w = w.upgrade().unwrap();
                        let n = w.root_path();
                        &workspaces
                            .iter()
                            .find(|workspace| *workspace.root_path() == *n)
                            .unwrap()
                            .entries
                    }
                };

                parent_entries.search(name).unwrap().clone()
            }
            fn replace_from_new_workspace(
                vfs_handler: &dyn VfsHandler,
                workspaces: &Workspaces,
                parent: &Parent,
            ) -> Parent {
                match parent {
                    Parent::Directory(dir) => {
                        let dir = dir.upgrade().unwrap();
                        let replaced =
                            replace_from_new_workspace(vfs_handler, workspaces, &dir.parent);
                        let search = search_parent(vfs_handler, workspaces, replaced, &dir.name);
                        let DirectoryEntry::Directory(new_dir) = search else {
                            unreachable!();
                        };
                        Parent::Directory(Arc::downgrade(&new_dir))
                    }
                    Parent::Workspace(_) => parent.clone(),
                }
            }
            let current_entry = file_state.file_entry();
            let parent_dir =
                replace_from_new_workspace(&*handler, &workspaces, &current_entry.parent);
            let DirectoryEntry::File(new_file_entry) =
                search_parent(&*handler, &workspaces, parent_dir, &current_entry.name)
            else {
                unreachable!()
            };
            //debug_assert_ne!(new_file_entry.as_ref() as *const _, current_entry.as_ref() as *const _);
            files.push(file_state.clone_box(new_file_entry.clone()));
        }

        for p in type_checked_dirs.rev() {
            workspaces.add_at_start(
                &*self.handler,
                file_scheme(),
                p.to_owned(),
                WorkspaceKind::TypeChecking,
            )
        }

        Self {
            handler,
            workspaces,
            files: files.into(),
            in_memory_files: Default::default(),
        }
    }

    pub fn into_panic_recovery(self) -> VfsPanicRecovery<F::Artifacts> {
        VfsPanicRecovery {
            files: self
                .files
                .into_iter()
                .filter_map(|f| {
                    let file_state = Pin::into_inner(f);
                    if file_state.path.is_subfile() {
                        return None;
                    }
                    let is_in_memory_file = self.in_memory_files.contains_key(&file_state.path);
                    if is_in_memory_file {
                        // It might feel strange that loading a panic recovery calls this hook. However
                        // this simplifies a lot of code that would otherwise needed to be run after a
                        // panic. Essentially after a panic we do not know what changed between the panic
                        // and now, so we simply push the diagnostic to the user again.
                        self.handler
                            .on_invalidated_in_memory_file(file_state.path.clone());
                    }
                    Some(RecoveryFile {
                        is_in_memory_file,
                        path: file_state.path,
                        invalidates_db: file_state.file_entry.invalidations.invalidates_db(),
                        artifacts: file_state.file.into_inner()?.into_recoverable_artifacts(),
                    })
                })
                .collect(),
        }
    }

    pub fn load_panic_recovery(
        &mut self,
        case_sensitive: bool,
        recovery: VfsPanicRecovery<F::Artifacts>,
        new_file: impl Fn(FileIndex, &FileEntry, F::Artifacts) -> F,
    ) {
        debug_assert!(self.in_memory_files.is_empty());
        debug_assert!(self.files.is_empty());
        for recoverable_file in recovery.files.into_iter() {
            tracing::debug!(
                "Load recovered file {} (is in memory file: {})",
                &recoverable_file.path.path,
                recoverable_file.is_in_memory_file
            );
            let ensured = self.workspaces.ensure_file(
                &*self.handler,
                case_sensitive,
                &recoverable_file.path,
                // TODO this should not be an empty string, since it could include gitignore, but
                // that's currently not supported anyway so passing an empty string here is fine.
                "",
            );
            match ensured.kind {
                AddedKind::FileEntry(file_entry) => {
                    let file_index = self.with_added_file(
                        file_entry.clone(),
                        recoverable_file.path,
                        recoverable_file.invalidates_db,
                        |file_index| new_file(file_index, &file_entry, recoverable_file.artifacts),
                    );
                    if recoverable_file.is_in_memory_file {
                        let fs = self.file_state(file_index);
                        self.in_memory_files
                            .insert(fs.path.clone(), InMemoryKind::File(file_index));
                    }
                }
                AddedKind::Gitignore(_) => {
                    tracing::error!("Did not expect a gitignore in panic recovery")
                }
            }
        }
    }

    pub fn add_workspace(&self, root_path: Arc<NormalizedPath>, kind: WorkspaceKind) -> bool {
        self.workspaces
            .add(&*self.handler, file_scheme(), root_path, kind)
    }

    pub fn search_path(&self, case_sensitive: bool, path: &PathWithScheme) -> Option<DirOrFile> {
        self.workspaces
            .search_path(&*self.handler, case_sensitive, path)
    }

    fn invalidate_files(
        &mut self,
        original_file_index: Option<FileIndex>,
        invalidations: Invalidations,
    ) -> InvalidationResult {
        let InvalidationDetail::Some(invalidations) = invalidations.into_iter() else {
            // This means that the file was created with `invalidates_db = true`, which
            // means we have to invalidate the whole database.
            tracing::info!(
                "Invalidate whole db because we have invalidated {:?}",
                original_file_index.map(|f| &self.file_state(f).path)
            );
            for path in self.in_memory_files.keys() {
                self.handler.on_invalidated_in_memory_file(path.clone());
            }
            return InvalidationResult::InvalidatedDb;
        };
        for invalid_index in invalidations {
            if self.invalidate_file_by_index(original_file_index, invalid_index)
                == InvalidationResult::InvalidatedDb
            {
                return InvalidationResult::InvalidatedDb;
            }
        }
        InvalidationResult::InvalidatedFiles
    }

    fn invalidate_file_by_index(
        &mut self,
        original_file_index: Option<FileIndex>,
        invalid_index: FileIndex,
    ) -> InvalidationResult {
        let file = self.file_state_mut(invalid_index);
        let new_invalidations = file.file_entry.invalidations.take();
        file.invalidate_references_to(original_file_index);

        if let InvalidationDetail::Some(invs) = new_invalidations.iter() {
            for invalidation in &invs {
                let p = &self.file_state(*invalidation).path.path;
                tracing::debug!(
                    "Invalidate {p} because we have invalidated {}",
                    self.file_state(invalid_index).path.path
                );
            }
        }
        if self.invalidate_files(original_file_index, new_invalidations)
            == InvalidationResult::InvalidatedDb
        {
            return InvalidationResult::InvalidatedDb;
        }
        let file = self.file_state(invalid_index);
        if self.in_memory_files.contains_key(&file.path) {
            self.handler
                .on_invalidated_in_memory_file(file.path.clone());
        }
        InvalidationResult::InvalidatedFiles
    }

    pub fn file(&self, index: FileIndex) -> Option<&F> {
        self.files.get(index.0 as usize).unwrap().file()
    }

    pub fn file_mut(&mut self, index: FileIndex) -> Option<&mut F> {
        self.file_state_mut(index).file_mut()
    }

    pub fn file_path(&self, index: FileIndex) -> &PathWithScheme {
        &self.file_state(index).path
    }

    pub fn file_entry(&self, index: FileIndex) -> &Arc<FileEntry> {
        &self.file_state(index).file_entry
    }

    fn file_state(&self, index: FileIndex) -> &FileState<F> {
        self.files.get(index.0 as usize).unwrap()
    }

    fn file_state_mut(&mut self, index: FileIndex) -> &mut FileState<F> {
        &mut self.files[index.0 as usize]
    }

    pub fn ensure_file_index(&self, file_entry: &Arc<FileEntry>) -> FileIndex {
        file_entry.get_file_index().unwrap_or_else(|| {
            let path = file_entry.absolute_path(&*self.handler);
            self.add_uninitialized_file_state(file_entry.clone(), path, false)
                .1
        })
    }

    pub fn ensure_file_for_file_entry(
        &self,
        file_entry: Arc<FileEntry>,
        invalidates_db: bool,
        new_file: impl FnOnce(FileIndex, Box<str>) -> F,
    ) -> Option<FileIndex> {
        self.ensure_file_for_file_entry_with_conditional(
            file_entry,
            invalidates_db,
            |_| true,
            new_file,
        )
    }

    pub fn ensure_file_for_file_index(
        &self,
        file_index: FileIndex,
        new_file: impl FnOnce(&FileEntry, Box<str>) -> F,
    ) -> Result<&F, &'static str> {
        let file_state = self.file_state(file_index);
        assert_eq!(file_state.file_entry.get_file_index(), Some(file_index));
        if let Some(f) = self.ensure_file_for_file_entry_with_conditional(
            file_state.file_entry.clone(),
            false,
            |_| true,
            |_, code| new_file(&file_state.file_entry, code),
        ) {
            debug_assert_eq!(f, file_index);
            Ok(file_state.file().unwrap())
        } else {
            Err("File was not found in file system")
        }
    }

    pub fn ensure_file_for_file_entry_with_conditional(
        &self,
        file_entry: Arc<FileEntry>,
        invalidates_db: bool,
        should_load: impl Fn(&str) -> bool,
        new_file: impl FnOnce(FileIndex, Box<str>) -> F,
    ) -> Option<FileIndex> {
        if let Some(file_index) = file_entry.get_file_index() {
            let file_state = self.file_state(file_index);
            if file_state.file().is_some() {
                return Some(file_index);
            }
            let code = self.handler.read_and_watch_file(&file_state.path)?;
            if !should_load(&code) {
                return None;
            }
            file_state.update(new_file(file_index, code.into()));
            Some(file_index)
        } else {
            let path = file_entry.absolute_path(&*self.handler);
            let code = self.handler.read_and_watch_file(&path)?;
            if !should_load(&code) {
                return None;
            }

            let file_index =
                self.with_added_file(file_entry.clone(), path, invalidates_db, |file_index| {
                    new_file(file_index, code.into())
                });
            Some(file_index)
        }
    }

    pub fn in_memory_file(&mut self, path: &PathWithScheme) -> Option<FileIndex> {
        match self.in_memory_files.get(path)? {
            InMemoryKind::File(file_index) => Some(*file_index),
            InMemoryKind::Gitignore(_) => None,
        }
    }

    pub fn store_in_memory_file(
        &mut self,
        case_sensitive: bool,
        path: PathWithScheme,
        code: Box<str>,
        new_file: impl FnOnce(FileIndex, &FileEntry, Box<str>) -> F,
    ) -> (Option<FileIndex>, InvalidationResult) {
        tracing::info!("Loading in memory file: {}", &path.path);
        let ensured = self
            .workspaces
            .ensure_file(&*self.handler, case_sensitive, &path, &code);

        let file_entry = match ensured.kind {
            AddedKind::FileEntry(file_entry) => file_entry,
            AddedKind::Gitignore(g) => {
                self.in_memory_files
                    .insert(path.clone(), InMemoryKind::Gitignore(g));
                return (None, InvalidationResult::InvalidatedFiles);
            }
        };

        let in_mem_file = self.in_memory_file(&path);
        debug_assert!(
            in_mem_file.is_none() || in_mem_file.is_some() && file_entry.get_file_index().is_some(),
            "{path:?}; in_mem_file: {in_mem_file:?}; ensured file_index: {:?}",
            file_entry.get_file_index(),
        );

        let in_mem_file = in_mem_file.or_else(|| {
            let file_index = file_entry.get_file_index()?;
            self.in_memory_files
                .insert(path.clone(), InMemoryKind::File(file_index));
            Some(file_index)
        });
        self.handler.on_invalidated_in_memory_file(path.clone());
        let mut result = InvalidationResult::InvalidatedFiles;
        if let Some(file_index) = in_mem_file {
            if self.file_state(file_index).code() == Some(&code) {
                // It already exists with the same code, we can therefore skip generating a new
                // file.
                return (Some(file_index), result);
            }
            result |= self.invalidate_and_unload_file(file_index);
        }

        let file_index = if let Some(file_index) = in_mem_file {
            let file = new_file(file_index, &file_entry, code);
            let new_file_state = Box::pin(FileState::new_parsed(
                file_entry,
                path,
                file,
                result == InvalidationResult::InvalidatedDb,
            ));
            self.files.set(file_index.0 as usize, new_file_state);
            if std::cfg!(debug_assertions) {
                let new = self.file_state(file_index);
                debug_assert!(
                    new.file_entry.get_file_index().is_some(),
                    "for {}",
                    new.path.path
                );
            }
            file_index
        } else {
            let file_index =
                self.with_added_file(file_entry.clone(), path.clone(), false, |file_index| {
                    new_file(file_index, &file_entry, code)
                });
            self.in_memory_files
                .insert(path, InMemoryKind::File(file_index));
            file_index
        };
        if tracing::enabled!(Level::INFO)
            && let InvalidationDetail::Some(invs) = ensured.invalidations.iter()
        {
            for invalidation in &invs {
                let p = &self.file_state(*invalidation).path.path;
                let path = &self.file_state(file_index).path.path;
                tracing::info!("Invalidate {p} because we're loading {path}");
            }
        }
        result |= self.invalidate_files(Some(file_index), ensured.invalidations);
        (Some(file_index), result)
    }

    fn invalidate_and_unload_in_memory_file(
        &mut self,
        case_sensitive: bool,
        file_index: FileIndex,
    ) -> InvalidationResult {
        let file_state = &self.files[file_index.0 as usize];
        self.workspaces
            .unload_file(&*self.handler, case_sensitive, &file_state.path);
        self.invalidate_and_unload_file(file_index)
    }

    fn invalidate_and_unload_file(&mut self, file_index: FileIndex) -> InvalidationResult {
        let file_state = &mut self.files[file_index.0 as usize];
        file_state.unload();
        let invalidations = file_state.file_entry.invalidations.take();
        self.invalidate_files(Some(file_index), invalidations)
    }

    pub fn close_in_memory_file(
        &mut self,
        case_sensitive: bool,
        path: &PathWithScheme,
        to_file: impl FnOnce(&FileState<F>, FileIndex, Box<str>) -> F,
    ) -> Result<InvalidationResult, &'static str> {
        let Some(removed) = self.in_memory_files.remove(path) else {
            return Err("The path is not known to be an in memory file");
        };
        Ok(
            if let Some(on_file_system_code) = self.handler.read_and_watch_file(path) {
                match removed {
                    InMemoryKind::File(file_index) => {
                        let file_state = &self.files[file_index.0 as usize];
                        // In case the code matches the one already in the file, we don't have to do anything.
                        // This is the very typical case of closing a buffer after saving it and therefore
                        // unloading the file from memory and using the file from the file system.
                        if Some(on_file_system_code.as_str()) != file_state.code() {
                            self.update_file(file_index, on_file_system_code.into(), to_file)
                        } else {
                            InvalidationResult::InvalidatedFiles
                        }
                    }
                    InMemoryKind::Gitignore(gitignore) => {
                        gitignore.parent.with_entries(self, |entries| {
                            if let Some(mut entry) = entries.search_mut(".gitignore") {
                                *entry = DirectoryEntry::Gitignore(GitignoreFile::new(
                                    gitignore.parent.clone(),
                                    &*path.path,
                                    &on_file_system_code,
                                ))
                            }
                        });
                        InvalidationResult::InvalidatedFiles
                    }
                }
            } else {
                match removed {
                    InMemoryKind::File(file_index) => {
                        self.invalidate_and_unload_in_memory_file(case_sensitive, file_index)
                    }
                    InMemoryKind::Gitignore(gitignore) => {
                        gitignore.parent.with_entries(self, |entries| {
                            entries.remove_name(".gitignore");
                        });
                        InvalidationResult::InvalidatedFiles
                    }
                }
            },
        )
    }

    pub fn delete_in_memory_files_directory(
        &mut self,
        case_sensitive: bool,
        dir_path: &PathWithScheme,
        to_file: impl Fn(&FileState<F>, FileIndex, Box<str>) -> F,
    ) -> Result<InvalidationResult, String> {
        // TODO this method feels weird and currently only used in tests

        let in_mem_paths: Vec<PathWithScheme> = self
            .in_memory_files
            .iter()
            .filter_map(|(path, _)| {
                if path.scheme != dir_path.scheme {
                    return None;
                }
                let after_dir = path.path.strip_prefix(&***dir_path.path)?;
                self.handler.strip_separator_prefix(after_dir)?;
                Some(path.clone())
            })
            .collect();
        let mut invalidation_result = InvalidationResult::InvalidatedFiles;
        for path in in_mem_paths {
            invalidation_result |= self
                .close_in_memory_file(case_sensitive, &path, &to_file)
                .unwrap();
        }
        self.workspaces
            .delete_directory(&*self.handler, case_sensitive, dir_path)?;
        Ok(invalidation_result)
    }

    pub fn invalidate_path(&mut self, case_sensitive: bool, path: &AbsPath) -> InvalidationResult {
        let _span = tracing::debug_span!("invalidate_path").entered();
        let in_mem_path = PathWithScheme {
            path: self.handler.normalize_path(path).into_owned(),
            scheme: file_scheme(),
        };
        if self.in_memory_files.contains_key(&in_mem_path) {
            // In memory files override all file system events
            tracing::debug!("Ignored invalidation, because the file is in-memory");
            return InvalidationResult::InvalidatedFiles;
        }
        let mut invalidates_db = false;
        let mut all_unloads = FastHashSet::default();
        let mut all_invalidations = FastHashSet::<FileIndex>::default();
        let mut ensure_unloaded_in_memory_paths = vec![];

        #[allow(unused_variables)]
        if let Some((workspace, parent, replace_name)) = self
            .workspaces
            .search_potential_parent_for_invalidation(&*self.handler, case_sensitive, path)
        {
            #[cfg(any(target_os = "macos", target_os = "windows", target_os = "ios"))]
            {
                // I'm not sure if this also affects Mac, but on Windows the paths are reported
                // depending on how the watch was created.
                if workspace.canonicalized_path != workspace.root_path {
                    if let Ok(after) = path.as_ref().strip_prefix(&**workspace.canonicalized_path) {
                        if let Some(after) = after.to_str() {
                            let new = format!(
                                "{}{}{after}",
                                workspace.root_path,
                                self.handler.separator()
                            );
                            let normalized =
                                NormalizedPath::new_arc(self.handler.unchecked_abs_path(&new));
                            let non_canonicalized_path =
                                PathWithScheme::with_file_scheme(normalized);
                            if self.in_memory_files.contains_key(&non_canonicalized_path) {
                                tracing::debug!(
                                    "Ignored invalidation, because the file is in-memory (via canonicalized path)"
                                );
                                return InvalidationResult::InvalidatedFiles;
                            }
                        }
                    }
                }
            }

            tracing::debug!(
                "Using dir {} to invalidate {replace_name}",
                parent.absolute_path(&*self.handler).path()
            );
            // TODO handle path == workspace path

            let mut check_invalidations_for_dir_entry = |e: &DirectoryEntry| {
                e.walk_entries(self, &mut |entry| {
                    match entry {
                        DirectoryEntry::File(f) => {
                            if let Some(file_index) = f.get_file_index() {
                                for (path, in_memory) in self.in_memory_files.iter() {
                                    if let InMemoryKind::File(in_memory_index) = in_memory
                                        && file_index == *in_memory_index
                                    {
                                        ensure_unloaded_in_memory_paths
                                            .push((path.clone(), *in_memory_index));
                                        all_invalidations.insert(file_index);
                                        return true;
                                    }
                                }
                                all_unloads.insert(file_index);
                            }
                        }
                        DirectoryEntry::MissingEntry(missing) => match missing.invalidations.iter()
                        {
                            InvalidationDetail::InvalidatesDb => invalidates_db = true,
                            InvalidationDetail::Some(invs) => all_invalidations.extend(&invs),
                        },
                        // TODO gitignore invalidation
                        DirectoryEntry::Directory(_) | DirectoryEntry::Gitignore(_) => (),
                    };
                    true
                });
            };
            parent.with_entries(self, |in_dir| {
                if self
                    .handler
                    .is_unnecessary_invalidation(path, in_dir.search(replace_name).as_deref())
                {
                    tracing::debug!(
                        "Ignored invalidation for {path}, because it is an unnecessary invalidation"
                    );
                    return;
                }
                let new_entry = self.handler.read_and_watch_entry(
                    &*self.workspaces.items.read().unwrap(),
                    path,
                    parent.clone(),
                    replace_name,
                );
                match new_entry {
                    Some(new_entry) => {
                        if let Some(mut to_replace) = in_dir.search_mut(replace_name) {
                            if self.matches_current_dir_entry(&to_replace, &new_entry) {
                                tracing::debug!(
                                    "Decided to replace nothing in VFS, because nothing changed"
                                );
                            } else {
                                tracing::debug!("Decided to replace {replace_name} in VFS");
                                to_replace.walk_entries(self, &mut |e| {
                                    check_invalidations_for_dir_entry(e);
                                    true
                                });
                                *to_replace = new_entry;
                            }
                        } else {
                            tracing::debug!("Decided to add {replace_name} to VFS");
                            in_dir.borrow_mut().push(new_entry);
                        }
                    }
                    None => {
                        if in_dir
                            .search(replace_name)
                            .is_some_and(|entry| matches!(*entry, DirectoryEntry::MissingEntry(_)))
                        {
                            tracing::debug!("Missing entry is still missing, no changes needed");
                        } else {
                            tracing::debug!("Decided to remove {replace_name} from VFS");
                            if let Some(r) = in_dir.remove_name(replace_name) {
                                check_invalidations_for_dir_entry(&r)
                            }
                        }
                    }
                }
            })
        }

        let invalidation_len = all_invalidations.len();
        let unload_len = all_unloads.len();
        if invalidates_db {
            tracing::debug!("caused an invalidated db");
            return InvalidationResult::InvalidatedDb;
        }
        for inv in all_unloads.into_iter() {
            if self.invalidate_and_unload_file(inv) == InvalidationResult::InvalidatedDb {
                tracing::debug!("caused an invalidated db");
                return InvalidationResult::InvalidatedDb;
            }
        }
        for inv in all_invalidations.into_iter() {
            if self.invalidate_file_by_index(None, inv) == InvalidationResult::InvalidatedDb {
                return InvalidationResult::InvalidatedDb;
            }
        }
        // After unloading in memory files (especially it they are within unloaded directories need
        // to be ensured).
        for (path, file_index) in ensure_unloaded_in_memory_paths {
            let ensured = self
                .workspaces
                .ensure_file(&*self.handler, case_sensitive, &path, "");
            debug_assert!(ensured.invalidations.is_empty());
            match ensured.kind {
                AddedKind::FileEntry(file_entry) => {
                    file_entry.with_set_file_index(|| file_index);
                    self.handler.on_invalidated_in_memory_file(path);
                }
                AddedKind::Gitignore(_) => {
                    // TODO Simply creating the file again is good enough, but this is not done
                    // yet.
                }
            }
        }
        tracing::debug!("Caused {unload_len} unloads and {invalidation_len} direct invalidations");
        InvalidationResult::InvalidatedFiles
    }

    fn matches_current_dir_entry(&self, old: &DirectoryEntry, new: &DirectoryEntry) -> bool {
        match (old, new) {
            (DirectoryEntry::File(old), DirectoryEntry::File(_)) => {
                if let Some(file_index) = old.get_file_index() {
                    let file_state = self.file_state(file_index);
                    if let Some(old_code) = file_state.code()
                        && let Some(new_code) = self.handler.read_and_watch_file(&file_state.path)
                    {
                        return old_code == new_code;
                    }
                }
                false
            }
            // TODO we don't have to invalidate the whole tree when the directories match
            _ => false,
        }
    }

    fn update_file(
        &mut self,
        file_index: FileIndex,
        new_code: Box<str>,
        to_file: impl FnOnce(&FileState<F>, FileIndex, Box<str>) -> F,
    ) -> InvalidationResult {
        let result = self.invalidate_and_unload_file(file_index);
        let file_state = self.file_state_mut(file_index);
        let new_file = to_file(file_state, file_index, new_code);
        file_state.update(new_file);
        result
    }

    #[inline]
    fn add_uninitialized_file_state(
        &self,
        file_entry: Arc<FileEntry>,
        path: PathWithScheme,
        invalidates_db: bool,
    ) -> (&FileState<F>, FileIndex) {
        let mut file_state = None;
        let file_index = file_entry.with_set_file_index(|| {
            let (fs, file_index) = self.add_uninitialized_file_state_without_setting_file_index(
                file_entry.clone(),
                path,
                invalidates_db,
            );
            file_state = Some(fs);
            file_index
        });
        if let Some(file_state) = file_state {
            (file_state, file_index)
        } else {
            // This is a race condition where with_set_file_index did enter concurrently and only
            // one got to complete.
            (self.file_state(file_index), file_index)
        }
    }

    fn add_uninitialized_file_state_without_setting_file_index(
        &self,
        file_entry: Arc<FileEntry>,
        path: PathWithScheme,
        invalidates_db: bool,
    ) -> (&FileState<F>, FileIndex) {
        let (file_state, file_index) = self.files.push(Box::pin(FileState::new_uninitialized(
            file_entry,
            path,
            invalidates_db,
        )));
        (file_state, FileIndex(file_index as u32))
    }

    fn with_added_file(
        &self,
        file_entry: Arc<FileEntry>,
        path: PathWithScheme,
        invalidates_db: bool,
        new_file: impl FnOnce(FileIndex) -> F,
    ) -> FileIndex {
        let (file_state, file_index) =
            self.add_uninitialized_file_state(file_entry, path, invalidates_db);
        file_state.update(new_file(file_index));
        file_index
    }

    pub fn create_sub_file(
        &self,
        super_file_index: FileIndex,
        add: impl FnOnce(FileIndex) -> F,
    ) -> FileIndex {
        let file_entry = self.file_state(super_file_index).file_entry.clone();
        let invalidates_db = file_entry.invalidations.invalidates_db();
        let (file_state, file_index) = self
            .add_uninitialized_file_state_without_setting_file_index(
                file_entry,
                PathWithScheme::new_sub_file(),
                invalidates_db,
            );
        file_state.update(add(file_index));
        file_index
    }
}

#[must_use]
#[derive(PartialEq)]
pub enum InvalidationResult {
    InvalidatedFiles,
    InvalidatedDb,
}

impl BitOrAssign for InvalidationResult {
    fn bitor_assign(&mut self, rhs: Self) {
        if *self == InvalidationResult::InvalidatedFiles {
            *self = rhs;
        }
    }
}

#[derive(Debug, Clone)]
pub struct FileState<F> {
    path: PathWithScheme,
    file_entry: Arc<FileEntry>,
    file: OnceLock<F>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct PathWithScheme {
    pub(crate) path: Arc<NormalizedPath>,
    pub(crate) scheme: Scheme,
}

impl PathWithScheme {
    fn new_sub_file() -> Self {
        thread_local! {
            static EMPTY_SCHEME: Arc<Box<str>> = Arc::new("".into());
            static EMPTY_PATH: Arc<NormalizedPath> = NormalizedPath::new_arc(AbsPath::new_arc("".into()));
        }

        EMPTY_PATH.with(|empty_path| {
            EMPTY_SCHEME.with(|scheme| Self {
                scheme: scheme.clone(),
                path: empty_path.clone(),
            })
        })
    }

    pub fn new(scheme: Scheme, path: Arc<NormalizedPath>) -> Self {
        Self { path, scheme }
    }

    pub fn with_file_scheme(path: Arc<NormalizedPath>) -> Self {
        Self {
            path,
            scheme: file_scheme(),
        }
    }

    fn is_subfile(&self) -> bool {
        // Setting an empty scheme is currently used for subfiles
        self.scheme.is_empty()
    }

    pub fn path(&self) -> &NormalizedPath {
        &self.path
    }

    pub fn as_uri(&self) -> String {
        if cfg!(windows) && **self.scheme == *"file" {
            let replaced = self
                .path
                .strip_prefix(r"\\?")
                .unwrap_or(&self.path)
                .replace('\\', "/");
            return format!("{}:///{replaced}", self.scheme);
        }
        format!("{}://{}", self.scheme, self.path)
    }
}

impl<F: VfsFile> FileState<F> {
    fn new_parsed(
        file_entry: Arc<FileEntry>,
        path: PathWithScheme,
        file: F,
        invalidates_db: bool,
    ) -> Self {
        if invalidates_db {
            file_entry.invalidations.set_invalidates_db();
        }
        Self {
            file_entry,
            path,
            file: OnceLock::from(file),
        }
    }

    fn new_uninitialized(
        file_entry: Arc<FileEntry>,
        path: PathWithScheme,
        invalidates_db: bool,
    ) -> Self {
        if invalidates_db {
            file_entry.invalidations.set_invalidates_db();
        }
        Self {
            file_entry,
            path,
            file: OnceLock::new(),
        }
    }

    fn update(&self, file: F) {
        let _maybe_err = self.file.set(file);
        /*
         * TODO in the future we want to ensure this again, but for now it's known that this is an
         * issue
        if std::cfg!(debug_assertions) {
            debug_assert!(maybe_err.is_ok());
        }
        */
    }

    pub fn file(&self) -> Option<&F> {
        self.file.get()
    }

    pub fn file_mut(&mut self) -> Option<&mut F> {
        self.file.get_mut()
    }

    fn code(&self) -> Option<&str> {
        Some(self.file()?.code())
    }

    pub fn file_entry(&self) -> &Arc<FileEntry> {
        &self.file_entry
    }

    pub fn unload(&mut self) {
        self.file.take();
    }

    fn invalidate_references_to(&mut self, file_index: Option<FileIndex>) {
        if let Some(f) = self.file_mut() {
            f.invalidate_references_to(file_index)
        }
    }
}

impl<F: Clone> FileState<F> {
    pub fn clone_box(&self, new_file_entry: Arc<FileEntry>) -> Pin<Box<Self>> {
        let mut new = self.clone();
        new.file_entry = new_file_entry;
        Box::pin(new)
    }
}
