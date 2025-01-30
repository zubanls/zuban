use std::rc::Rc;

use utils::match_case;

use crate::{tree::AddedFile, Directory, DirectoryEntry, FileEntry, Parent, VfsHandler};

#[derive(Debug, PartialEq, Copy, Clone)]
pub enum WorkspaceKind {
    TypeChecking,
    SitePackages,
    Typeshed,
}

#[derive(Debug, Default, Clone)]
pub struct Workspaces(Vec<Workspace>);

impl Workspaces {
    pub(crate) fn add(&mut self, vfs: &dyn VfsHandler, root: String, kind: WorkspaceKind) {
        self.0.push(Workspace::new(vfs, root, kind))
    }

    pub(crate) fn add_at_start(&mut self, vfs: &dyn VfsHandler, root: String, kind: WorkspaceKind) {
        self.0.insert(0, Workspace::new(vfs, root, kind))
    }

    pub fn iter(&self) -> impl DoubleEndedIterator<Item = &Workspace> {
        self.0.iter()
    }

    pub fn directories_not_type_checked(&self) -> impl Iterator<Item = &Directory> {
        self.0
            .iter()
            .filter(|x| !matches!(x.kind, WorkspaceKind::TypeChecking))
            .map(|x| &x.directory)
    }

    pub fn directories_to_type_check(&self) -> impl Iterator<Item = &Directory> {
        self.0
            .iter()
            .filter(|x| matches!(x.kind, WorkspaceKind::TypeChecking))
            .map(|x| &x.directory)
    }

    pub fn search_path(
        &self,
        vfs: &dyn VfsHandler,
        case_sensitive: bool,
        path: &str,
    ) -> Option<Rc<FileEntry>> {
        self.0.iter().find_map(|workspace| {
            let p = strip_path_prefix(vfs, case_sensitive, path, workspace.root_path())?;
            workspace.directory.search_path(vfs, p)
        })
    }

    pub(crate) fn search_potential_parent_for_invalidation<'path>(
        &self,
        vfs: &dyn VfsHandler,
        case_sensitive: bool,
        path: &'path str,
    ) -> Option<(&Workspace, Parent, &'path str)> {
        self.0.iter().find_map(|workspace| {
            let mut rest = strip_path_prefix(vfs, case_sensitive, path, workspace.root_path());
            if cfg!(target_os = "macos") {
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
                        .as_deref()
                        .unwrap_or(&workspace.directory)
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
                        workspace,
                        match current_dir {
                            Some(dir) => Parent::Directory(Rc::downgrade(&dir)),
                            None => Parent::Workspace(workspace.root_path.clone()),
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
        path: &str,
    ) -> AddedFile {
        for workspace in &mut self.0 {
            let root_path = workspace.root_path();
            if let Some(p) = strip_path_prefix(vfs, case_sensitive, path, root_path) {
                return ensure_dirs_and_file(
                    Parent::Workspace(workspace.root_path.clone()),
                    &workspace.directory,
                    vfs,
                    p,
                );
            }
        }
        unreachable!()
    }

    pub(crate) fn unload_file(&mut self, vfs: &dyn VfsHandler, case_sensitive: bool, path: &str) {
        // TODO for now we always unload, fix that.
        for workspace in &self.0 {
            if let Some(p) = strip_path_prefix(vfs, case_sensitive, path, workspace.root_path()) {
                workspace.directory.unload_file(vfs, p);
            }
        }
    }

    pub(crate) fn delete_directory(
        &mut self,
        vfs: &dyn VfsHandler,
        case_sensitive: bool,
        path: &str,
    ) -> Result<(), String> {
        for workspace in &mut self.0 {
            if let Some(p) = strip_path_prefix(vfs, case_sensitive, path, workspace.root_path()) {
                return workspace.directory.delete_directory(vfs, p);
            }
        }
        Err(format!("Workspace of path {path} cannot be found"))
    }

    pub(crate) fn clone_with_new_rcs(&self) -> Self {
        fn clone_inner_rcs(dir: Directory) -> Rc<Directory> {
            let dir = Rc::new(dir);
            for entry in dir.entries.borrow_mut().iter_mut() {
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
                        *dir = clone_inner_rcs(new);
                    }
                }
            }
            dir
        }
        let mut new = self.clone();
        for workspace in new.0.iter_mut() {
            workspace.directory.entries = workspace.directory.entries.clone();
            for entry in workspace.directory.entries.borrow_mut().iter_mut() {
                match entry {
                    DirectoryEntry::Directory(dir) => {
                        debug_assert!(matches!(dir.parent, Parent::Workspace(_)));
                        *dir = clone_inner_rcs(dir.as_ref().clone())
                    }
                    DirectoryEntry::File(file) => {
                        *file = Rc::new(file.as_ref().clone());
                        debug_assert!(matches!(file.parent, Parent::Workspace(_)));
                    }
                    DirectoryEntry::MissingEntry { .. } => (), // has no RCs
                }
            }
        }
        new
    }
}

#[derive(Debug, Clone)]
pub struct Workspace {
    root_path: Rc<Box<str>>,
    // Mac sometimes needs a bit help with events that are reported for non-canonicalized paths
    // Without this check_rename_with_symlinks fails
    #[cfg(target_os = "macos")]
    canonicalized_path: Box<str>,
    pub directory: Directory,
    pub kind: WorkspaceKind,
}

impl Workspace {
    fn new(vfs: &dyn VfsHandler, mut root_path: String, kind: WorkspaceKind) -> Self {
        if let Some(new_root_path) = vfs.strip_separator_suffix(&root_path) {
            root_path.truncate(new_root_path.len());
        }
        tracing::debug!("Add workspace {root_path}");
        let root_path = Rc::<Box<str>>::new(root_path.into());

        let dir =
            match vfs.walk_and_watch_dirs(&root_path, Parent::Workspace(root_path.clone()), true) {
                DirectoryEntry::Directory(dir) => Rc::unwrap_or_clone(dir),
                e => Directory {
                    parent: Parent::Workspace(root_path.clone()),
                    name: e.name().into(),
                    entries: Default::default(),
                },
            };
        #[cfg(target_os = "macos")]
        {
            let canonicalized_path = match std::fs::canonicalize(&**root_path) {
                Ok(p) => match p.into_os_string().into_string() {
                    Ok(p) => p,
                    Err(p) => {
                        tracing::error!(
                            "Canonicalized path for {root_path:?} is {p:?}, not valid unicode"
                        );
                        root_path.to_string()
                    }
                },
                Err(err) => {
                    tracing::error!("Issue while canonicalizing workspace path: {err}");
                    root_path.to_string()
                }
            };
            return Self {
                directory: dir,
                root_path,
                canonicalized_path: canonicalized_path.into(),
                kind,
            };
        };
        #[cfg(not(target_os = "macos"))]
        {
            return Self {
                directory: dir,
                root_path,
                kind,
            };
        };
    }

    pub fn root_path(&self) -> &str {
        &self.root_path
    }
}

fn ensure_dirs_and_file(
    parent: Parent,
    dir: &Directory,
    vfs: &dyn VfsHandler,
    path: &str,
) -> AddedFile {
    let (name, rest) = vfs.split_off_folder(path);
    if let Some(rest) = rest {
        let mut invs = Default::default();
        if let Some(x) = dir.search(name) {
            match &*x {
                DirectoryEntry::Directory(rc) => {
                    return ensure_dirs_and_file(
                        Parent::Directory(Rc::downgrade(rc)),
                        rc,
                        vfs,
                        rest,
                    )
                }
                DirectoryEntry::MissingEntry(missing) => {
                    invs = missing.invalidations.take();
                    drop(x);
                    dir.remove_name(name);
                }
                _ => unimplemented!("Dir overwrite of file; When does this happen?"),
            }
        };
        let dir2 = Directory::new(parent, Box::from(name));
        let mut result =
            ensure_dirs_and_file(Parent::Directory(Rc::downgrade(&dir2)), &dir2, vfs, rest);
        dir.entries
            .borrow_mut()
            .push(DirectoryEntry::Directory(dir2));
        result.invalidations.extend(invs);
        result
    } else {
        dir.ensure_file(parent, name)
    }
}

fn strip_path_prefix<'x>(
    vfs: &dyn VfsHandler,
    case_sensitive: bool,
    mut path: &'x str,
    mut to_strip: &str,
) -> Option<&'x str> {
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
