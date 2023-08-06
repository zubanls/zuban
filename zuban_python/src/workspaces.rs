use std::cell::{Cell, RefCell, RefMut};
use std::path::PathBuf;
use std::rc::{Rc, Weak};
use walkdir::WalkDir;

use crate::database::FileIndex;
use crate::file::{FileStateLoader, Vfs};
use crate::utils::{rc_unwrap_or_clone, VecRefWrapper};

#[derive(Debug, Default)]
pub struct Workspaces(Vec<Workspace>);

impl Workspaces {
    pub fn add(&mut self, loaders: &[Box<dyn FileStateLoader>], root: Box<str>) {
        self.0.push(Workspace::new(loaders, root))
    }

    pub fn directories(&self) -> impl Iterator<Item = (&str, &Directory)> {
        self.0.iter().map(|x| (x.root_path(), &x.directory))
    }

    pub fn ensure_file(&mut self, vfs: &dyn Vfs, path: &str) -> AddedFile {
        for workspace in &mut self.0 {
            if let Some(p) = path.strip_prefix(workspace.root_path()) {
                return ensure_dirs_and_file(
                    Parent::Workspace(workspace.root_path.clone()),
                    &workspace.directory,
                    vfs,
                    p,
                );
            }
        }
        todo!()
    }

    pub fn unload_file(&mut self, vfs: &dyn Vfs, path: &str) {
        // TODO for now we always unload, fix that.
        for workspace in &mut self.0 {
            if let Some(p) = path.strip_prefix(workspace.root_path()) {
                workspace.directory.unload_file(vfs, p);
            }
        }
    }

    pub fn delete_directory(&mut self, vfs: &dyn Vfs, path: &str) -> Result<(), String> {
        for workspace in &mut self.0 {
            if let Some(p) = path.strip_prefix(workspace.root_path()) {
                return workspace.directory.delete_directory(vfs, p);
            }
        }
        Err(format!("Workspace of path {path} cannot be found"))
    }

    pub fn last(&self) -> &Workspace {
        // TODO this should probably not be needed
        self.0.last().unwrap()
    }
}

#[derive(Debug, Clone)]
pub struct Workspace {
    root_path: Rc<Box<str>>,
    directory: Directory,
    //watcher: dyn notify::Watcher,
}

impl Workspace {
    fn new(loaders: &[Box<dyn FileStateLoader>], root_path: Box<str>) -> Self {
        let root_path = Rc::new(root_path);
        let mut stack = vec![(
            PathBuf::from(&**root_path),
            Directory::new(Parent::Workspace(root_path.clone()), "".into()),
        )];
        let mut first = true;
        // TODO optimize if there are a lot of files
        for entry in WalkDir::new(&**root_path)
            .follow_links(true)
            .into_iter()
            .filter_entry(|entry| {
                if first {
                    // The first entry needs to be passed, because it's the directory itself.
                    first = false;
                    return true;
                }
                entry.file_name().to_str().is_some_and(|name| {
                    !loaders.iter().any(|l| l.should_be_ignored(name))
                        && loaders.iter().any(|l| l.might_be_relevant(name))
                })
            })
            // TODO is it ok that we filter out all errors?
            .filter_map(|e| e.ok())
            .skip(1)
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
                                .push(DirectoryEntry::new_file(parent, name.into()));
                        }
                    }
                    Err(e) => {
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
                    directory: rc_unwrap_or_clone(current.1),
                    root_path,
                };
            }
        }
        unreachable!()
    }

    pub fn directory(&self) -> &Directory {
        &self.directory
    }

    fn root_path(&self) -> &str {
        &self.root_path
    }
}

#[derive(Debug, Clone)]
pub struct WorkspaceFileIndex(Cell<Option<FileIndex>>);

impl WorkspaceFileIndex {
    fn none() -> Self {
        Self(Cell::new(None))
    }

    pub fn set(&self, index: FileIndex) {
        self.0.set(Some(index));
    }

    pub fn get(&self) -> Option<FileIndex> {
        self.0.get()
    }
}

#[derive(Debug, Clone)]
pub enum Parent {
    Directory(Weak<Directory>),
    // This is not an Rc<str>, because that would make the enum 8 bytes bigger. It's used a lot, so
    // this is probably better.
    Workspace(Rc<Box<str>>),
}

impl Parent {
    pub fn maybe_dir(&self) -> Result<Rc<Directory>, &Rc<Box<str>>> {
        match self {
            Self::Directory(dir) => Ok(dir.upgrade().expect("THere should always be a parent")),
            Self::Workspace(w) => Err(w),
        }
    }
}

#[derive(Debug, Clone)]
pub struct FileEntry {
    pub name: Box<str>,
    pub file_index: WorkspaceFileIndex,
    pub parent: Parent,
}

fn ensure_dirs_and_file<'a>(
    parent: Parent,
    dir: &Directory,
    vfs: &dyn Vfs,
    path: &'a str,
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
                DirectoryEntry::MissingEntry { invalidations, .. } => {
                    invs = invalidations.take();
                    drop(x);
                    dir.remove_name(name);
                }
                _ => todo!(),
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
        Directory::ensure_file(parent, dir, vfs, name)
    }
}

#[derive(Debug, Clone)]
pub enum DirectoryEntry {
    File(Rc<FileEntry>),
    MissingEntry {
        name: Box<str>,
        invalidations: Invalidations,
    },
    Directory(Rc<Directory>),
}

impl DirectoryEntry {
    pub fn new_file(parent: Parent, name: Box<str>) -> Self {
        Self::File(Rc::new(FileEntry {
            name,
            file_index: WorkspaceFileIndex::none(),
            parent,
        }))
    }

    fn name(&self) -> &str {
        match self {
            DirectoryEntry::File(file) => &file.name,
            DirectoryEntry::Directory(dir) => &dir.name,
            DirectoryEntry::MissingEntry { name, .. } => name,
        }
    }

    pub fn for_each_file(&self, callable: &mut impl FnMut(FileIndex)) {
        match self {
            DirectoryEntry::File(file) => {
                if let Some(index) = file.file_index.get() {
                    callable(index)
                }
            }
            DirectoryEntry::Directory(dir) => dir.for_each_file(callable),
            DirectoryEntry::MissingEntry { .. } => (),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Directory {
    entries: RefCell<Vec<DirectoryEntry>>,
    pub parent: Parent,
    pub name: Box<str>,
}

#[derive(Debug)]
pub struct AddedFile {
    pub invalidations: Invalidations,
    pub file_entry: Rc<FileEntry>,
}

impl AddedFile {
    pub fn set_file_index(&self, index: FileIndex) {
        // Theoretically we could just search in the directory for the entry again, but I'm too
        // lazy for that and it's faster this way.
        debug_assert!(self.file_entry.file_index.get().is_none());
        self.file_entry.file_index.set(index);
    }
}

impl Directory {
    fn new(parent: Parent, name: Box<str>) -> Rc<Self> {
        Rc::new(Self {
            entries: Default::default(),
            parent,
            name,
        })
    }
    pub fn iter(&self) -> VecRefWrapper<DirectoryEntry> {
        VecRefWrapper(self.entries.borrow())
    }

    fn remove_name(&self, name: &str) {
        self.entries.borrow_mut().retain(|f| f.name() != name)
    }

    pub fn search(&self, name: &str) -> Option<RefMut<DirectoryEntry>> {
        let borrow = self.entries.borrow_mut();
        // We need to run this search twice, because Rust needs #![feature(cell_filter_map)]
        // https://github.com/rust-lang/rust/issues/81061
        borrow.iter().find(|entry| entry.name() == name)?;
        Some(RefMut::map(borrow, |dir| {
            dir.iter_mut().find(|entry| entry.name() == name).unwrap()
        }))
    }

    fn ensure_file(parent: Parent, directory: &Directory, vfs: &dyn Vfs, name: &str) -> AddedFile {
        let mut invalidations = Invalidations::default();
        let entry = if let Some(mut entry) = directory.search(name) {
            match &mut *entry {
                DirectoryEntry::File(file) => (),
                DirectoryEntry::MissingEntry {
                    invalidations: inv,
                    name,
                } => {
                    invalidations = inv.take();
                    *entry = DirectoryEntry::File(Rc::new(FileEntry {
                        parent,
                        name: name.clone(), //std::mem::replace(&mut mut_entry.name, Box::from("")),
                        file_index: WorkspaceFileIndex::none(),
                    }));
                }
                DirectoryEntry::Directory(..) => todo!(),
            }
            entry.clone()
        } else {
            let mut borrow = directory.entries.borrow_mut();
            let entry = DirectoryEntry::new_file(parent, name.into());
            borrow.push(entry.clone());
            entry
        };
        let DirectoryEntry::File(file_entry) = entry else {
            unreachable!()
        };
        AddedFile {
            invalidations,
            file_entry: file_entry.clone(),
        }
    }

    fn unload_file(&self, vfs: &dyn Vfs, path: &str) {
        let (name, rest) = vfs.split_off_folder(path);
        if let Some(entry) = self.search(name) {
            if let Some(rest) = rest {
                if let DirectoryEntry::Directory(dir) = &*entry {
                    dir.unload_file(vfs, rest);
                }
            } else if matches!(*entry, DirectoryEntry::File(_)) {
                drop(entry);
                self.remove_name(name);
            }
        }
    }

    pub fn add_missing_entry(&self, name: Box<str>, invalidates: FileIndex) {
        let mut vec = self.entries.borrow_mut();
        if let Some(pos) = vec.iter().position(|x| x.name() == name.as_ref()) {
            if let DirectoryEntry::MissingEntry { invalidations, .. } = &vec[pos] {
                invalidations.add(invalidates)
            } else {
                unreachable!("{:?}", &vec[pos])
            }
        } else {
            let invalidations = Invalidations::default();
            invalidations.add(invalidates);
            vec.push(DirectoryEntry::MissingEntry {
                invalidations,
                name,
            })
        }
    }

    fn delete_directory(&self, vfs: &dyn Vfs, path: &str) -> Result<(), String> {
        let (name, rest) = vfs.split_off_folder(path);
        if let Some(inner) = self.search(name) {
            match &*inner {
                DirectoryEntry::Directory(dir) => {
                    if let Some(rest) = rest {
                        dir.delete_directory(vfs, rest)
                    } else {
                        drop(inner);
                        self.remove_name(name);
                        Ok(())
                    }
                }
                DirectoryEntry::MissingEntry { .. } => {
                    Err(format!("Path {path} cannot be found (missing)"))
                }
                t => todo!("{t:?}"),
            }
        } else {
            Err(format!("Path {path} cannot be found"))
        }
    }

    pub fn for_each_file(&self, callable: &mut impl FnMut(FileIndex)) {
        for n in self.entries.borrow_mut().iter_mut() {
            n.for_each_file(callable)
        }
    }
}

#[derive(Debug, Default, Clone)]
pub struct Invalidations(RefCell<Vec<FileIndex>>);

impl Invalidations {
    pub fn add(&self, element: FileIndex) {
        if !self.0.borrow().contains(&element) {
            self.0.borrow_mut().push(element);
        }
    }

    pub fn extend(&mut self, other: Self) {
        self.0.get_mut().extend(other.0.into_inner())
    }

    pub fn take(&self) -> Self {
        Self(RefCell::new(self.0.take()))
    }

    pub fn iter(&self) -> VecRefWrapper<FileIndex> {
        VecRefWrapper(self.0.borrow())
    }

    pub fn into_iter(self) -> impl Iterator<Item = FileIndex> {
        self.0.into_inner().into_iter()
    }
}
