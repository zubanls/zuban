use std::rc::Rc;

use utils::match_case;

use crate::{
    tree::{AddedFile, Entries},
    vfs::Scheme,
    AbsPath, DirOrFile, Directory, DirectoryEntry, Parent, PathWithScheme, VfsHandler, NormalizedPath
};

#[derive(Debug, PartialEq, Copy, Clone)]
pub enum WorkspaceKind {
    TypeChecking,
    // Used as a fallback if files outside of workspaces are added to Workspaces
    Fallback,
    SitePackages,
    Typeshed,
}

#[derive(Debug, Default, Clone)]
pub struct Workspaces {
    items: Vec<Rc<Workspace>>,
}

impl Workspaces {
    pub(crate) fn add(
        &mut self,
        vfs: &dyn VfsHandler,
        scheme: Scheme,
        root: Rc<AbsPath>,
        kind: WorkspaceKind,
    ) {
        self.items.push(Workspace::new(vfs, scheme, root, kind))
    }

    pub(crate) fn add_at_start(
        &mut self,
        vfs: &dyn VfsHandler,
        scheme: Scheme,
        root: Rc<AbsPath>,
        kind: WorkspaceKind,
    ) {
        self.items
            .insert(0, Workspace::new(vfs, scheme, root, kind))
    }

    pub fn iter(&self) -> impl DoubleEndedIterator<Item = &Workspace> {
        self.items.iter().map(|w| w.as_ref())
    }

    pub fn iter_not_type_checked(&self) -> impl Iterator<Item = &Workspace> {
        self.iter().filter(|x| !x.is_type_checked())
    }

    pub fn entries_to_type_check(&self) -> impl Iterator<Item = &Entries> {
        self.iter()
            .filter(|x| x.is_type_checked())
            .map(|x| &x.entries)
    }

    pub fn search_path(
        &self,
        vfs: &dyn VfsHandler,
        case_sensitive: bool,
        path: &PathWithScheme,
    ) -> Option<DirOrFile> {
        self.iter()
            .find_map(|workspace| {
                let p = workspace.strip_path_prefix(vfs, case_sensitive, path)?;
                workspace.entries.search_path(vfs, p)
            })
            .or_else(|| {
                self.iter().find_map(|workspace| {
                    if workspace.kind == WorkspaceKind::Fallback {
                        if let Some(entry) = workspace.entries.search(&path.path) {
                            let DirectoryEntry::File(f) = &*entry else {
                                unreachable!("Why would this ever be {entry:?} as a fallback?");
                            };
                            return Some(DirOrFile::File(f.clone()));
                        };
                    }
                    None
                })
            })
    }

    pub(crate) fn search_potential_parent_for_invalidation<'path>(
        &self,
        vfs: &dyn VfsHandler,
        case_sensitive: bool,
        path: &'path AbsPath,
    ) -> Option<(&Workspace, Parent, &'path str)> {
        self.items.iter().find_map(|workspace| {
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
            let mut current_dir = None;
            loop {
                let (name, new_rest) = vfs.split_off_folder(rest);
                if let Some(new_rest) = new_rest {
                    // We generally return None in all cases where the nesting of the path is
                    // deeper than the current VFS. This is fine for invalidation, since
                    // directories themselves should be monitored. I'm not even sure all of these
                    // paths are reachable.
                    rest = new_rest;
                    let found = current_dir
                        .as_ref()
                        .map(|dir: &Rc<Directory>| Directory::entries(vfs, dir))
                        .unwrap_or(&workspace.entries)
                        .search(name)?;
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
                        workspace.as_ref(),
                        match current_dir {
                            Some(dir) => Parent::Directory(Rc::downgrade(&dir)),
                            None => Parent::Workspace(Rc::downgrade(workspace)),
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
    ) -> AddedFile {
        for workspace in &mut self.items {
            if let Some(p) = workspace.strip_path_prefix(vfs, case_sensitive, path) {
                return ensure_dirs_and_file(
                    Parent::Workspace(Rc::downgrade(workspace)),
                    &workspace.entries,
                    vfs,
                    p,
                );
            }
        }
        for workspace in &mut self.items {
            if workspace.kind == WorkspaceKind::Fallback {
                return workspace
                    .entries
                    .ensure_file(Parent::Workspace(Rc::downgrade(workspace)), &path.path);
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
        for workspace in &self.items {
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
        for workspace in &mut self.items {
            if let Some(p) = workspace.strip_path_prefix(vfs, case_sensitive, path) {
                return workspace.entries.delete_directory(vfs, p);
            }
        }
        Err(format!("Workspace of path {} cannot be found", path.path))
    }

    pub(crate) fn clone_with_new_rcs(&self, vfs: &dyn VfsHandler) -> Self {
        fn clone_inner_rcs(vfs: &dyn VfsHandler, dir: Directory) -> Rc<Directory> {
            // TODO not all entries need to be recalculated if it's not yet calculated
            let dir = Rc::new(dir);
            for entry in Directory::entries(vfs, &dir).borrow_mut().iter_mut() {
                match entry {
                    DirectoryEntry::File(file) => {
                        let mut new_file = file.as_ref().clone();
                        new_file.parent = Parent::Directory(Rc::downgrade(&dir));
                        *file = Rc::new(new_file);
                    }
                    DirectoryEntry::MissingEntry { .. } => (),
                    DirectoryEntry::Directory(dir) => {
                        let mut new = dir.as_ref().clone();
                        new.parent = Parent::Directory(Rc::downgrade(dir));
                        *dir = clone_inner_rcs(vfs, new);
                    }
                }
            }
            dir
        }
        let mut new = self.clone();
        for workspace in new.items.iter_mut() {
            let new_workspace = Rc::new(workspace.as_ref().clone());
            for entry in new_workspace.entries.borrow_mut().iter_mut() {
                match entry {
                    DirectoryEntry::Directory(dir) => {
                        debug_assert!(matches!(dir.parent, Parent::Workspace(_)));
                        let mut new_dir = dir.as_ref().clone();
                        new_dir.parent = Parent::Workspace(Rc::downgrade(&new_workspace));
                        *dir = clone_inner_rcs(vfs, new_dir)
                    }
                    DirectoryEntry::File(file) => {
                        debug_assert!(matches!(file.parent, Parent::Workspace(_)));
                        let mut new_file = file.as_ref().clone();
                        new_file.parent = Parent::Workspace(Rc::downgrade(&new_workspace));
                        *file = Rc::new(new_file);
                    }
                    DirectoryEntry::MissingEntry { .. } => (), // has no RCs
                }
            }
            *workspace = new_workspace
        }
        new
    }
}

#[derive(Debug, Clone)]
pub struct Workspace {
    pub(crate) root_path: Rc<AbsPath>,
    // Mac sometimes needs a bit help with events that are reported for non-canonicalized paths
    // Without this check_rename_with_symlinks fails
    // On Windows this is also necessary since changing the watch logic. We canonicalize watched
    // paths to avoid adding multiple watches for the same files. Therefore we also need to
    // canonicalize the paths here.
    #[cfg(any(target_os = "macos", target_os = "windows", target_os = "ios"))]
    pub(crate) canonicalized_path: Rc<AbsPath>,
    pub(crate) scheme: Scheme,
    pub entries: Entries,
    pub kind: WorkspaceKind,
}

impl Workspace {
    fn new(
        vfs: &dyn VfsHandler,
        scheme: Scheme,
        root_path: Rc<AbsPath>,
        kind: WorkspaceKind,
    ) -> Rc<Self> {
        tracing::debug!("Add workspace {root_path}");
        let root_path = Rc::<AbsPath>::from(root_path);

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
            workspace = Rc::new(Self {
                entries: Default::default(),
                scheme,
                root_path,
                canonicalized_path: vfs.unchecked_abs_path(&canonicalized_path),
                kind,
            });
        };
        #[cfg(not(any(target_os = "macos", target_os = "windows", target_os = "ios")))]
        {
            workspace = Rc::new(Self {
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
            &workspace.root_path,
            Parent::Workspace(Rc::downgrade(&workspace)),
        );
        *workspace.entries.borrow_mut() = std::mem::take(&mut new_entries.borrow_mut());
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
                return true
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
    path: &str,
) -> AddedFile {
    let (name, rest) = vfs.split_off_folder(path);
    if let Some(rest) = rest {
        let mut invs = Default::default();
        if let Some(x) = entries.search(name) {
            match &*x {
                DirectoryEntry::Directory(rc) => {
                    return ensure_dirs_and_file(
                        Parent::Directory(Rc::downgrade(rc)),
                        Directory::entries(vfs, rc),
                        vfs,
                        rest,
                    )
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
            Parent::Directory(Rc::downgrade(&dir2)),
            Directory::entries(vfs, &dir2),
            vfs,
            rest,
        );
        entries.borrow_mut().push(DirectoryEntry::Directory(dir2));
        result.invalidations.extend(invs);
        result
    } else {
        entries.ensure_file(parent, name)
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
        let (folder1, rest) = vfs.split_off_folder(path);
        let (folder2, rest_to_strip) = vfs.split_off_folder(to_strip);
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
