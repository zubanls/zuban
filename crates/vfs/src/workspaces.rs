use std::{path::PathBuf, rc::Rc};

use utils::match_case;
use walkdir::WalkDir;

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
    pub fn add(&mut self, vfs: &dyn VfsHandler, root: String, kind: WorkspaceKind) {
        self.0.push(Workspace::new(vfs, root, kind))
    }

    pub fn add_at_start(&mut self, vfs: &dyn VfsHandler, root: String, kind: WorkspaceKind) {
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

    pub fn search_file(
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

    // TODO this should probably not be needed
    pub fn first(&self) -> &Workspace {
        self.0.first().unwrap()
    }

    pub fn clone_with_new_rcs(&self) -> Self {
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
    pub directory: Directory,
    pub kind: WorkspaceKind,
}

impl Workspace {
    fn new(vfs: &dyn VfsHandler, mut root_path: String, kind: WorkspaceKind) -> Self {
        let separator = vfs.separator();
        if root_path.ends_with(separator) {
            root_path.pop();
        }
        let root_path = Rc::<Box<str>>::new(root_path.into());

        let mut stack = vec![(
            PathBuf::from(&**root_path),
            Directory::new(Parent::Workspace(root_path.clone()), "".into()),
        )];
        let mut walk_dir = WalkDir::new(&**root_path).follow_links(true).into_iter();
        // The first entry needs to be ignored, because it's the directory itself.
        walk_dir.next();
        // TODO optimize if there are a lot of files
        for entry in walk_dir
            .filter_entry(|entry| {
                entry.file_name().to_str().is_some_and(|name| {
                    if name.ends_with(".py") || name.ends_with(".pyi") || name == "py.typed" {
                        return true;
                    }
                    if name == "__pycache__" {
                        return false;
                    }
                    const STUBS_SUFFIX: &str = "-stubs";
                    // Keep potential folders around
                    !name.contains('.') && (!name.contains('-') || name.ends_with(STUBS_SUFFIX))
                })
            })
            // TODO is it ok that we filter out all errors?
            .filter_map(|e| e.ok())
        {
            while !entry.path().starts_with(&stack.last().unwrap().0) {
                let n = stack.pop().unwrap().1;
                stack
                    .last_mut()
                    .unwrap()
                    .1
                    .entries
                    .borrow_mut()
                    .push(DirectoryEntry::Directory(n));
            }
            let name = entry.file_name();
            if let Some(name) = name.to_str() {
                match entry.metadata() {
                    Ok(m) => {
                        let parent = match stack.len() {
                            1 => Parent::Workspace(root_path.clone()),
                            _ => Parent::Directory(Rc::downgrade(&stack.last().unwrap().1)),
                        };
                        if m.is_dir() {
                            stack.push((
                                entry.path().to_owned(),
                                Directory::new(parent, name.into()),
                            ));
                        } else {
                            stack
                                .last_mut()
                                .unwrap()
                                .1
                                .entries
                                .borrow_mut()
                                .push(DirectoryEntry::File(FileEntry::new(parent, name.into())));
                        }
                    }
                    Err(_) => {
                        // Just ignore it for now
                        panic!("Need to investigate")
                    }
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
                return Self {
                    directory: Rc::unwrap_or_clone(current.1),
                    root_path,
                    kind,
                };
            }
        }
        unreachable!()
    }

    pub fn directory(&self) -> &Directory {
        &self.directory
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
    path: &'x str,
    to_strip: &str,
) -> Option<&'x str> {
    let path = if case_sensitive {
        path.strip_prefix(to_strip)?
    } else {
        let p = path.get(..to_strip.len())?;
        if !match_case(case_sensitive, to_strip, p) {
            return None;
        }
        path.get(to_strip.len()..)?
    };
    path.strip_prefix(vfs.separator())
}
