use std::{
    ops::Deref,
    sync::{Arc, RwLock},
};

use utils::{OwnedMappedReadGuard, match_case};

use crate::{
    AbsPath, DirOrFile, Directory, DirectoryEntry, NormalizedPath, Parent, PathWithScheme,
    VfsHandler,
    tree::{AddedFile, DirEntries, Entries},
    vfs::Scheme,
};

#[derive(Debug, PartialEq, Copy, Clone)]
pub enum WorkspaceKind {
    TypeChecking,
    // Used as a fallback if files outside of workspaces are added to Workspaces
    Fallback,
    SitePackages,
    Typeshed,
    // This is not really relevant for type checking, because it's covered by Typeshed
    PythonStdLib,
}

#[derive(Debug, Default)]
pub struct Workspaces {
    pub(crate) items: RwLock<Vec<Arc<Workspace>>>,
}

impl Workspaces {
    pub(crate) fn add(
        &self,
        vfs: &dyn VfsHandler,
        scheme: Scheme,
        root: Arc<NormalizedPath>,
        kind: WorkspaceKind,
    ) -> bool {
        let mut items = self.items.write().unwrap();
        if items.iter().any(|item| item.root_path == root) {
            // The path is already in there
            return false;
        }
        let workspace = Workspace::new(vfs, &*items, scheme, root, kind);
        items.push(workspace);
        true
    }

    pub(crate) fn add_at_start(
        &mut self,
        vfs: &dyn VfsHandler,
        scheme: Scheme,
        root: Arc<NormalizedPath>,
        kind: WorkspaceKind,
    ) {
        let items = self.inner_items_mut();
        if items.iter().any(|item| item.root_path == root) {
            // The path is already in there
            return;
        }
        items.insert(0, Workspace::new(vfs, items, scheme, root, kind))
    }

    fn inner_items_mut(&mut self) -> &mut Vec<Arc<Workspace>> {
        self.items.get_mut().unwrap()
    }

    fn strip_short_path_in_workspace<'path>(
        &self,
        vfs: &dyn VfsHandler,
        case_sensitive: bool,
        path: &'path PathWithScheme,
    ) -> Option<(Arc<Workspace>, &'path str)> {
        let mut shortest: Option<(Arc<Workspace>, &'path str)> = None;
        for workspace in self.items.read().unwrap().iter() {
            if let Some(p) = workspace.strip_path_prefix(vfs, case_sensitive, path) {
                if shortest
                    .as_ref()
                    .is_none_or(|(_, shortest)| shortest.len() > p.len())
                {
                    shortest = Some((workspace.clone(), p))
                }
            }
        }
        shortest
    }

    pub fn iter(&self) -> impl DoubleEndedIterator<Item = &Workspace> {
        OwnedMappedReadGuard::map_owned(self.items.read().unwrap(), |workspaces| {
            workspaces.iter().map(|w| w.as_ref())
        })
    }

    pub fn iter_not_type_checked(&self) -> impl Iterator<Item = &Workspace> {
        self.iter().filter(|x| !x.is_type_checked())
    }

    pub fn entries_to_type_check(&self) -> impl Iterator<Item = &Entries> {
        self.iter()
            .filter(|x| x.is_type_checked())
            .map(|x| &x.entries)
    }

    pub(crate) fn search_path(
        &self,
        vfs: &dyn VfsHandler,
        case_sensitive: bool,
        path: &PathWithScheme,
    ) -> Option<DirOrFile> {
        self.strip_short_path_in_workspace(vfs, case_sensitive, path)
            .and_then(|(workspace, rest)| workspace.entries.search_path(vfs, self, rest))
            .or_else(|| {
                self.iter().find_map(|workspace| {
                    if workspace.kind == WorkspaceKind::Fallback
                        && let Some(entry) = workspace.entries.search(&path.path)
                    {
                        let DirectoryEntry::File(f) = &*entry else {
                            unreachable!("Why would this ever be {entry:?} as a fallback?");
                        };
                        return Some(DirOrFile::File(f.clone()));
                    };
                    None
                })
            })
    }

    pub(crate) fn search_potential_parent_for_invalidation<'path>(
        &self,
        vfs: &dyn VfsHandler,
        case_sensitive: bool,
        path: &'path AbsPath,
    ) -> Option<(Arc<Workspace>, Parent, &'path str)> {
        self.items.read().unwrap().iter().find_map(|workspace| {
            if **workspace.scheme != *"file" {
                // TODO for now only file schemes are allowed
                return None;
            }
            #[allow(unused_mut)]
            let mut rest = strip_path_prefix(vfs, case_sensitive, path, workspace.root_path());
            #[cfg(any(target_os = "macos", target_os = "windows", target_os = "ios"))]
            {
                rest = rest.or_else(|| {
                    strip_path_prefix(vfs, case_sensitive, path, &workspace.canonicalized_path)
                });
            }
            let mut rest = rest?;
            let mut current_dir: Option<Arc<Directory>> = None;
            loop {
                let (name, new_rest) = vfs.split_off_first_item(rest);
                if let Some(new_rest) = new_rest {
                    // We generally return None in all cases where the nesting of the path is
                    // deeper than the current VFS. This is fine for invalidation, since
                    // directories themselves should be monitored. I'm not even sure all of these
                    // paths are reachable.
                    rest = new_rest;
                    let entries = if let Some(dir) = current_dir.as_ref() {
                        dir.entries.get()?.expect()
                    } else {
                        &workspace.entries
                    };
                    let found = entries.search(name)?;
                    match &*found {
                        DirectoryEntry::Directory(d) => {
                            let x = d.clone();
                            drop(found);
                            current_dir = Some(x);
                        }
                        _ => return None,
                    }
                } else {
                    // Return dir
                    return Some((
                        workspace.clone(),
                        match current_dir {
                            Some(dir) => Parent::Directory(Arc::downgrade(&dir)),
                            None => Parent::Workspace(Arc::downgrade(workspace)),
                        },
                        name,
                    ));
                }
            }
        })
    }

    pub(crate) fn ensure_file(
        &mut self,
        vfs: &dyn VfsHandler,
        case_sensitive: bool,
        path: &PathWithScheme,
        code: &str,
    ) -> AddedFile {
        if let Some((workspace, rest)) =
            self.strip_short_path_in_workspace(vfs, case_sensitive, path)
        {
            return ensure_dirs_and_file(
                Parent::Workspace(Arc::downgrade(&workspace)),
                &workspace.entries,
                vfs,
                self,
                rest,
                code,
            );
        }
        for workspace in self.inner_items_mut() {
            if workspace.kind == WorkspaceKind::Fallback {
                return workspace.entries.ensure_file(
                    vfs,
                    Parent::Workspace(Arc::downgrade(workspace)),
                    &path.path,
                    code,
                );
            }
        }
        unreachable!("Expected to be able to place the file {path:?}")
    }

    pub(crate) fn unload_file(
        &mut self,
        vfs: &dyn VfsHandler,
        case_sensitive: bool,
        path: &PathWithScheme,
    ) {
        // TODO for now we always unload, fix that.
        for workspace in self.inner_items_mut() {
            if let Some(p) = workspace.strip_path_prefix(vfs, case_sensitive, path) {
                workspace.entries.unload_file(vfs, p);
            }
        }
    }

    pub(crate) fn delete_directory(
        &mut self,
        vfs: &dyn VfsHandler,
        case_sensitive: bool,
        path: &PathWithScheme,
    ) -> Result<(), String> {
        for workspace in self.inner_items_mut() {
            if let Some(p) = workspace.strip_path_prefix(vfs, case_sensitive, path) {
                return workspace.entries.delete_directory(vfs, p);
            }
        }
        Err(format!("Workspace of path {} cannot be found", path.path))
    }

    // We intentionally use a &mut self here, because we want to avoid that the datastructures
    // inside are modified while we're cloning.
    pub(crate) fn clone_with_new_rcs(&mut self, vfs: &dyn VfsHandler) -> Self {
        fn clone_inner_rcs(
            vfs: &dyn VfsHandler,
            workspaces: &Workspaces,
            dir: Directory,
        ) -> Arc<Directory> {
            // TODO not all entries need to be recalculated if it's not yet calculated
            let dir = Arc::new(dir);
            for entry in Directory::entries_with_workspaces(vfs, workspaces, &dir)
                .borrow_mut()
                .iter_mut()
            {
                match entry {
                    DirectoryEntry::File(file) => {
                        let mut new_file = file.as_ref().clone();
                        new_file.parent = Parent::Directory(Arc::downgrade(&dir));
                        *file = Arc::new(new_file);
                    }
                    DirectoryEntry::MissingEntry { .. } => (),
                    DirectoryEntry::Directory(inner_dir) => {
                        let mut new = inner_dir.as_ref().clone();
                        new.parent = Parent::Directory(Arc::downgrade(&dir));
                        *inner_dir = clone_inner_rcs(vfs, workspaces, new);
                    }
                    DirectoryEntry::Gitignore(_) => (),
                }
            }
            dir
        }
        let mut new = self.inner_items_mut().clone();
        for workspace in &mut new {
            let new_workspace = Arc::new(workspace.as_ref().clone());
            for entry in new_workspace.entries.borrow_mut().iter_mut() {
                match entry {
                    DirectoryEntry::Directory(dir) => {
                        debug_assert!(matches!(dir.parent, Parent::Workspace(_)));
                        let mut new_dir = dir.as_ref().clone();
                        new_dir.parent = Parent::Workspace(Arc::downgrade(&new_workspace));
                        *dir = clone_inner_rcs(vfs, &Workspaces::default(), new_dir)
                    }
                    DirectoryEntry::File(file) => {
                        debug_assert!(matches!(file.parent, Parent::Workspace(_)));
                        let mut new_file = file.as_ref().clone();
                        new_file.parent = Parent::Workspace(Arc::downgrade(&new_workspace));
                        *file = Arc::new(new_file);
                    }
                    DirectoryEntry::MissingEntry { .. } => (), // has no RCs
                    DirectoryEntry::Gitignore { .. } => (),    // has no interior mutability
                }
            }
            *workspace = new_workspace
        }
        Self {
            items: RwLock::new(new),
        }
    }

    pub fn expect_last(&self) -> impl Deref<Target = &Workspace> {
        OwnedMappedReadGuard::map_owned(self.items.read().unwrap(), |workspaces| {
            workspaces
                .last()
                .expect("There should always be a workspace")
                .as_ref()
        })
    }
}

#[derive(Debug, Clone)]
pub struct Workspace {
    pub root_path: Arc<NormalizedPath>,
    // Mac sometimes needs a bit help with events that are reported for non-canonicalized paths
    // Without this check_rename_with_symlinks fails
    // On Windows this is also necessary since changing the watch logic. We canonicalize watched
    // paths to avoid adding multiple watches for the same files. Therefore we also need to
    // canonicalize the paths here.
    #[cfg(any(target_os = "macos", target_os = "windows", target_os = "ios"))]
    pub(crate) canonicalized_path: Arc<NormalizedPath>,
    pub(crate) scheme: Scheme,
    pub entries: Entries,
    pub kind: WorkspaceKind,
}

impl Workspace {
    fn new(
        vfs: &dyn VfsHandler,
        workspaces: &[Arc<Workspace>],
        scheme: Scheme,
        root_path: Arc<NormalizedPath>,
        kind: WorkspaceKind,
    ) -> Arc<Self> {
        tracing::debug!("Add workspace {root_path}");
        let workspace;
        #[cfg(any(target_os = "macos", target_os = "windows", target_os = "ios"))]
        {
            let canonicalized_path = match std::fs::canonicalize(&**root_path) {
                Ok(p) => match p.into_os_string().into_string() {
                    Ok(p) => {
                        if cfg!(target_os = "windows") {
                            if let Some(p) = p.strip_prefix(r#"\\?\"#) {
                                p.to_string()
                            } else {
                                p
                            }
                        } else {
                            p
                        }
                    }
                    Err(p) => {
                        tracing::error!(
                            "Canonicalized path for {root_path:?} is {p:?}, not valid unicode"
                        );
                        root_path.to_string()
                    }
                },
                Err(err) => {
                    if kind != WorkspaceKind::Fallback {
                        // The path might not exist
                        tracing::info!("Issue while canonicalizing workspace path: {err}");
                    }
                    root_path.to_string()
                }
            };
            workspace = Arc::new(Self {
                entries: Default::default(),
                scheme,
                root_path,
                canonicalized_path: vfs
                    .unchecked_normalized_path(vfs.unchecked_abs_path(&canonicalized_path)),
                kind,
            });
        };
        #[cfg(not(any(target_os = "macos", target_os = "windows", target_os = "ios")))]
        {
            workspace = Arc::new(Self {
                entries: Default::default(),
                scheme,
                root_path,
                kind,
            })
        }
        if kind == WorkspaceKind::Fallback {
            return workspace;
        }
        let new_entries = vfs.read_and_watch_dir(
            workspaces,
            &workspace.root_path,
            Parent::Workspace(Arc::downgrade(&workspace)),
        );
        *workspace.entries.borrow_mut() = std::mem::take(&mut new_entries.borrow_mut());

        // Workspaces are added as nested workspaces already for workspaces that are contained
        // within this one. But this workspace could be contained by another one, check for that
        // here.
        if !workspaces.is_empty()
            && let (Some(folder), name) = vfs.split_off_last_item(&workspace.root_path)
        {
            for old in workspaces {
                if ***old.root_path == *folder
                    && let Some(dir_entry) = old.entries.search(name)
                    && let DirectoryEntry::Directory(dir) = &*dir_entry
                {
                    let result = dir
                        .entries
                        .set(DirEntries::NestedWorkspace(Arc::downgrade(&workspace)));
                    debug_assert!(result.is_ok());
                }
            }
        }
        workspace
    }

    pub fn is_type_checked(&self) -> bool {
        matches!(
            self.kind,
            WorkspaceKind::TypeChecking | WorkspaceKind::Fallback
        )
    }

    pub fn part_of_site_packages(&self) -> bool {
        matches!(self.kind, WorkspaceKind::SitePackages)
    }

    fn strip_path_prefix<'x>(
        &self,
        vfs: &dyn VfsHandler,
        case_sensitive: bool,
        path: &'x PathWithScheme,
    ) -> Option<&'x str> {
        if path.scheme != self.scheme {
            return None;
        }
        strip_path_prefix(vfs, case_sensitive, &path.path, self.root_path())
    }

    pub fn root_path_starts_with(&self, path: &NormalizedPath) -> bool {
        let path = path.as_ref();
        #[cfg(any(target_os = "macos", target_os = "windows", target_os = "ios"))]
        {
            if self.canonicalized_path.as_ref().as_ref().starts_with(path) {
                return true;
            }
        }
        self.root_path().as_ref().starts_with(path)
    }

    pub fn root_path(&self) -> &AbsPath {
        &self.root_path
    }
}

fn ensure_dirs_and_file(
    parent: Parent,
    entries: &Entries,
    vfs: &dyn VfsHandler,
    workspaces: &Workspaces,
    path: &str,
    code: &str,
) -> AddedFile {
    let (name, rest) = vfs.split_off_first_item(path);
    if let Some(rest) = rest {
        let mut invs = Default::default();
        if let Some(x) = entries.search(name) {
            match &*x {
                DirectoryEntry::Directory(arc) => {
                    return ensure_dirs_and_file(
                        Parent::Directory(Arc::downgrade(arc)),
                        Directory::entries_with_workspaces(vfs, workspaces, arc),
                        vfs,
                        workspaces,
                        rest,
                        code,
                    );
                }
                DirectoryEntry::MissingEntry(missing) => {
                    invs = missing.invalidations.take();
                    drop(x);
                    entries.remove_name(name);
                }
                _ => unimplemented!("Dir overwrite of file; When does this happen?"),
            }
        };
        let dir2 = Directory::new(parent, Box::from(name));
        let mut result = ensure_dirs_and_file(
            Parent::Directory(Arc::downgrade(&dir2)),
            Directory::entries_with_workspaces(vfs, workspaces, &dir2),
            vfs,
            workspaces,
            rest,
            code,
        );
        entries.borrow_mut().push(DirectoryEntry::Directory(dir2));
        result.invalidations.extend(invs);
        result
    } else {
        entries.ensure_file(vfs, parent, name, code)
    }
}

fn strip_path_prefix<'x>(
    vfs: &dyn VfsHandler,
    case_sensitive: bool,
    mut path: &'x str,
    to_strip: &AbsPath,
) -> Option<&'x str> {
    let mut to_strip: &str = to_strip;
    loop {
        let (folder1, rest) = vfs.split_off_first_item(path);
        let (folder2, rest_to_strip) = vfs.split_off_first_item(to_strip);
        if !match_case(case_sensitive, folder1, folder2) {
            return None;
        }
        path = rest?;
        let Some(rest_to_strip) = rest_to_strip else {
            return Some(path);
        };
        to_strip = rest_to_strip
    }
}
