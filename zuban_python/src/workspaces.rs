use std::cell::{Cell, RefCell, RefMut};
use std::path::PathBuf;
use std::rc::{Rc, Weak};
use walkdir::WalkDir;

use crate::database::FileIndex;
use crate::file::{FileStateLoader, Vfs};
use crate::utils::VecRefWrapper;

#[derive(Debug, Default)]
pub struct Workspaces(Vec<Workspace>);

impl Workspaces {
    pub fn add(&mut self, loaders: &[Box<dyn FileStateLoader>], root: Box<str>) {
        self.0.push(Workspace::new(loaders, root))
    }

    pub fn directories(&self) -> impl Iterator<Item = (&str, &Rc<Directory>)> {
        self.0.iter().map(|x| (x.root_path(), &x.directory))
    }

    pub fn ensure_file(&mut self, vfs: &dyn Vfs, path: &str) -> AddedFile {
        for workspace in &mut self.0 {
            if let Some(p) = path.strip_prefix(workspace.root_path()) {
                return ensure_dirs_and_file(&workspace.directory, vfs, p);
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

    pub fn find_dir_content(&self, vfs: &dyn Vfs, path: &str) -> Option<Rc<Directory>> {
        for workspace in &self.0 {
            if let Some(p) = path.strip_prefix(workspace.root_path()) {
                if let Some(content) = workspace.directory.find_dir_content(vfs, p) {
                    return Some(content);
                }
            }
        }
        None
    }
}

#[derive(Debug, Clone)]
pub struct Workspace {
    root_path: Rc<Box<str>>,
    directory: Rc<Directory>,
    //watcher: dyn notify::Watcher,
}

impl Workspace {
    fn new(loaders: &[Box<dyn FileStateLoader>], path: Box<str>) -> Self {
        let mut stack = vec![(
            PathBuf::from(path.as_ref()),
            DirectoryEntry::new_dir("".into()),
        )];
        let mut first = true;
        // TODO optimize if there are a lot of files
        for entry in WalkDir::new(path.as_ref())
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
                    .expect_directory_entries()
                    .entries
                    .borrow_mut()
                    .push(n);
            }
            let name = entry.file_name();
            if let Some(name) = name.to_str() {
                match entry.metadata() {
                    Ok(m) => {
                        if m.is_dir() {
                            stack.push((
                                entry.path().to_owned(),
                                DirectoryEntry::new_dir(name.into()),
                            ));
                        } else {
                            stack
                                .last_mut()
                                .unwrap()
                                .1
                                .expect_directory_entries()
                                .entries
                                .borrow_mut()
                                .push(DirectoryEntry::new_file(name.into()));
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
                    .expect_directory_entries()
                    .entries
                    .borrow_mut()
                    .push(current.1)
            } else {
                return Self {
                    directory: current.1.expect_directory_entries().clone(),
                    root_path: Rc::new(path),
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

pub enum Parent {
    Directory(Weak<DirectoryEntry>),
    // This is not an Rc<str>, because that would make the enum 8 bytes bigger. It's used a lot, so
    // this is probably better.
    Workspace(Rc<Box<str>>),
}

#[derive(Debug, Clone)]
pub enum DirOrFile {
    File(Rc<FileEntry>),
    MissingEntry {
        name: Box<str>,
        invalidations: Invalidations,
    },
    Directory(Rc<Directory>),
}

#[derive(Debug, Clone)]
pub struct FileEntry {
    pub name: Box<str>,
    pub file_index: WorkspaceFileIndex,
}

fn ensure_dirs_and_file<'a>(rc: &Rc<Directory>, vfs: &dyn Vfs, path: &'a str) -> AddedFile {
    let (name, rest) = vfs.split_off_folder(path);
    if let Some(rest) = rest {
        let mut invs = Default::default();
        if let Some(x) = rc.search(name) {
            match &x.type_ {
                DirOrFile::Directory(rc) => return ensure_dirs_and_file(rc, vfs, rest),
                DirOrFile::MissingEntry { invalidations, .. } => {
                    invs = invalidations.take();
                    drop(x);
                    rc.remove_name(name);
                }
                _ => todo!(),
            }
        };
        let dir2 = Directory::new(Box::from(name));
        let mut result = ensure_dirs_and_file(&dir2, vfs, rest);
        rc.entries.borrow_mut().push(DirectoryEntry {
            type_: DirOrFile::Directory(dir2),
        });
        result.invalidations.extend(invs);
        result
    } else {
        Directory::ensure_file(rc.clone(), vfs, name)
    }
}

#[derive(Debug, Clone)]
pub struct DirectoryEntry {
    pub type_: DirOrFile,
}

impl DirectoryEntry {
    pub fn new_dir(name: Box<str>) -> Self {
        Self {
            type_: DirOrFile::Directory(Directory::new(Box::from(name))),
        }
    }

    pub fn new_file(name: Box<str>) -> Self {
        Self {
            type_: DirOrFile::File(Rc::new(FileEntry {
                name,
                file_index: WorkspaceFileIndex::none(),
            })),
        }
    }

    fn name(&self) -> &str {
        match &self.type_ {
            DirOrFile::File(file) => &file.name,
            DirOrFile::Directory(dir) => &dir.name,
            DirOrFile::MissingEntry { name, .. } => name,
        }
    }

    fn expect_directory_entries(&self) -> &Rc<Directory> {
        match &self.type_ {
            DirOrFile::Directory(dir) => dir,
            _ => unreachable!(),
        }
    }

    pub fn for_each_file(&self, callable: &mut impl FnMut(FileIndex)) {
        match &self.type_ {
            DirOrFile::File(file) => {
                if let Some(index) = file.file_index.get() {
                    callable(index)
                }
            }
            DirOrFile::Directory(dir) => dir.for_each_file(callable),
            DirOrFile::MissingEntry { .. } => (),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Directory {
    entries: RefCell<Vec<DirectoryEntry>>,
    pub name: Box<str>,
}

#[derive(Debug)]
pub struct AddedFile {
    pub invalidations: Invalidations,
    pub file_entry: Rc<FileEntry>,
    pub directory: Rc<Directory>,
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
    pub fn new(name: Box<str>) -> Rc<Self> {
        Rc::new(Self {
            entries: Default::default(),
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

    fn ensure_file(directory: Rc<Directory>, vfs: &dyn Vfs, name: &str) -> AddedFile {
        let mut invalidations = Invalidations::default();
        let entry = directory
            .search(name)
            .map(|mut entry| {
                match &mut entry.type_ {
                    DirOrFile::File(file) => (),
                    DirOrFile::MissingEntry {
                        invalidations: inv,
                        name,
                    } => {
                        invalidations = inv.take();
                        entry.type_ = DirOrFile::File(Rc::new(FileEntry {
                            name: name.clone(), //std::mem::replace(&mut mut_entry.name, Box::from("")),
                            file_index: WorkspaceFileIndex::none(),
                        }));
                    }
                    DirOrFile::Directory(..) => todo!(),
                }
                entry.clone()
            })
            .unwrap_or_else(|| {
                let mut borrow = directory.entries.borrow_mut();
                let entry = DirectoryEntry::new_file(name.into());
                borrow.push(entry.clone());
                entry
            });
        let DirOrFile::File(file_entry) = &entry.type_ else {
            unreachable!()
        };
        AddedFile {
            invalidations,
            directory,
            file_entry: file_entry.clone(),
        }
    }

    fn unload_file(&self, vfs: &dyn Vfs, path: &str) {
        let (name, rest) = vfs.split_off_folder(path);
        if let Some(entry) = self.search(name) {
            if let Some(rest) = rest {
                if let DirOrFile::Directory(dir) = &entry.type_ {
                    dir.unload_file(vfs, rest);
                }
            } else if matches!(entry.type_, DirOrFile::File(_)) {
                drop(entry);
                self.remove_name(name);
            }
        }
    }

    pub fn add_missing_entry(&self, name: Box<str>, invalidates: FileIndex) {
        let mut vec = self.entries.borrow_mut();
        if let Some(pos) = vec.iter().position(|x| x.name() == name.as_ref()) {
            if let DirOrFile::MissingEntry { invalidations, .. } = &vec[pos].type_ {
                invalidations.add(invalidates)
            } else {
                unreachable!("{:?}", &vec[pos].type_)
            }
        } else {
            let invalidations = Invalidations::default();
            invalidations.add(invalidates);
            vec.push(DirectoryEntry {
                type_: DirOrFile::MissingEntry {
                    invalidations,
                    name,
                },
            })
        }
    }

    fn delete_directory(&self, vfs: &dyn Vfs, path: &str) -> Result<(), String> {
        let (name, rest) = vfs.split_off_folder(path);
        if let Some(inner) = self.search(name) {
            match &inner.type_ {
                DirOrFile::Directory(dir) => {
                    if let Some(rest) = rest {
                        dir.delete_directory(vfs, rest)
                    } else {
                        drop(inner);
                        self.remove_name(name);
                        Ok(())
                    }
                }
                DirOrFile::MissingEntry { .. } => {
                    Err(format!("Path {path} cannot be found (missing)"))
                }
                t => todo!("{t:?}"),
            }
        } else {
            Err(format!("Path {path} cannot be found"))
        }
    }

    fn find_dir_content(&self, vfs: &dyn Vfs, path: &str) -> Option<Rc<Directory>> {
        let (name, rest) = vfs.split_off_folder(path);
        for n in self.entries.borrow().iter() {
            if name == n.name() {
                match &n.type_ {
                    DirOrFile::Directory(files) => {
                        return match rest {
                            Some(rest) => files.find_dir_content(vfs, rest),
                            None => Some(files.clone()),
                        };
                    }
                    DirOrFile::File(_) => unreachable!(),
                    DirOrFile::MissingEntry { .. } => unreachable!(),
                }
            }
        }
        None
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
