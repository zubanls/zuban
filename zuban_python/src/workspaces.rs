use std::cell::{Cell, Ref, RefCell, RefMut};
use std::path::PathBuf;
use std::rc::Rc;
use walkdir::WalkDir;

use crate::database::FileIndex;
use crate::file::{FileStateLoader, Vfs};
use crate::utils::Invalidations;

#[derive(Debug, Default)]
pub struct Workspaces(Vec<Workspace>);

impl Workspaces {
    pub fn add(&mut self, loaders: &[Box<dyn FileStateLoader>], root: String) {
        self.0.push(Workspace::new(loaders, root))
    }

    pub fn directories(&self) -> impl Iterator<Item = (&str, &Rc<DirContent>)> {
        self.0.iter().map(|x| {
            (
                x.root().name.as_str(),
                x.root().directory_entries().unwrap(),
            )
        })
    }

    pub fn ensure_file(&mut self, vfs: &dyn Vfs, path: &str) -> AddedFile {
        for workspace in &mut self.0 {
            if path.starts_with(&workspace.root.name) {
                if let DirOrFile::Directory(files) = &mut workspace.root.type_ {
                    let (dir, name) = DirContent::ensure_dir_and_return_name(
                        files,
                        vfs,
                        &path[workspace.root.name.len()..],
                    );
                    return DirContent::ensure_file(&dir, vfs, name);
                }
            }
        }
        todo!()
    }

    pub fn unload_if_not_available(&mut self, vfs: &dyn Vfs, path: &str) {
        // TODO for now we always unload, fix that.
        for workspace in &mut self.0 {
            if let DirOrFile::Directory(files) = &mut workspace.root.type_ {
                if path.starts_with(&workspace.root.name) {
                    let path = &path[workspace.root.name.len()..];
                    workspace.root.unload_if_not_available(vfs, path);
                }
            }
        }
    }

    pub fn delete_directory(&mut self, vfs: &dyn Vfs, path: &str) -> Result<(), String> {
        for workspace in &mut self.0 {
            if let DirOrFile::Directory(files) = &mut workspace.root.type_ {
                if path.starts_with(&workspace.root.name) {
                    let (dir, name) = DirContent::ensure_dir_and_return_name(
                        files,
                        vfs,
                        &path[workspace.root.name.len()..],
                    );
                    todo!() //return DirContent::delete_directory(&dir, vfs, name);
                }
            }
        }
        Err(format!("Path {path} cannot be found"))
    }

    pub fn last(&self) -> &Workspace {
        // TODO this should probably not be needed
        self.0.last().unwrap()
    }

    pub fn find_dir_content(&self, vfs: &dyn Vfs, path: &str) -> Option<Rc<DirContent>> {
        for workspace in &self.0 {
            if path.starts_with(&workspace.root.name) {
                let path = &path[workspace.root.name.len()..];
                if let Some(content) = workspace.root.find_dir_content(vfs, path) {
                    return Some(content);
                }
            }
        }
        None
    }
}

#[derive(Debug)]
pub struct Workspace {
    root: DirEntry,
    //watcher: dyn notify::Watcher,
}

impl Workspace {
    fn new(loaders: &[Box<dyn FileStateLoader>], root: String) -> Self {
        let mut stack = vec![(PathBuf::from(&root), DirEntry::new_dir(root))];
        // TODO optimize if there are a lot of files
        for entry in WalkDir::new(&stack[0].1.name)
            .follow_links(true)
            .into_iter()
            .filter_entry(|entry| {
                entry.file_name().to_str().is_some_and(|name| {
                    !loaders.iter().any(|l| l.should_be_ignored(name))
                        && loaders.iter().any(|l| l.might_be_relevant(name))
                })
            })
            .filter_map(|e| e.ok())
            .skip(1)
        {
            while !entry.path().starts_with(&stack.last().unwrap().0) {
                let n = stack.pop().unwrap().1;
                stack
                    .last_mut()
                    .unwrap()
                    .1
                    .directory_entries()
                    .unwrap()
                    .0
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
                                DirEntry::new_dir(name.to_owned()),
                            ));
                        } else {
                            stack
                                .last_mut()
                                .unwrap()
                                .1
                                .directory_entries()
                                .unwrap()
                                .0
                                .borrow_mut()
                                .push(DirEntry::new_file(name.to_owned()));
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
                    .directory_entries()
                    .unwrap()
                    .0
                    .borrow_mut()
                    .push(current.1)
            } else {
                return Self { root: current.1 };
            }
        }
        unreachable!()
    }

    pub fn root(&self) -> &DirEntry {
        &self.root
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
pub enum DirOrFile {
    File(WorkspaceFileIndex),
    MissingEntry(Invalidations),
    Directory(Rc<DirContent>),
}

#[derive(Debug, Clone)]
pub struct DirEntry {
    pub name: String,
    pub type_: DirOrFile,
}

impl DirEntry {
    pub fn new_dir(name: String) -> Self {
        Self {
            name,
            type_: DirOrFile::Directory(Default::default()),
        }
    }

    pub fn new_file(name: String) -> Self {
        Self {
            name,
            type_: DirOrFile::File(WorkspaceFileIndex::none()),
        }
    }

    pub fn directory_entries(&self) -> Option<&Rc<DirContent>> {
        match &self.type_ {
            DirOrFile::Directory(entries) => Some(entries),
            _ => None,
        }
    }

    pub fn unload_if_not_available(&mut self, vfs: &dyn Vfs, path: &str) {
        if let DirOrFile::Directory(files) = &self.type_ {
            let (name, rest) = vfs.split_off_folder(path);
            if let Some(mut entry) = files.search(name) {
                if matches!(&entry.type_, DirOrFile::Directory(_)) {
                    entry.unload_if_not_available(vfs, rest.unwrap());
                    match &mut entry.type_ {
                        DirOrFile::Directory(f) => {
                            if f.is_empty() {
                                // TODO check if dir still exists
                                f.remove_name(name);
                            }
                        }
                        _ => unreachable!(),
                    }
                } else {
                    drop(entry);
                    files.remove_name(name);
                }
            }
        }
    }

    pub fn for_each_file(&mut self, callable: &mut impl FnMut(FileIndex)) {
        match &self.type_ {
            DirOrFile::File(index) => {
                if let Some(index) = index.get() {
                    callable(index)
                }
            }
            DirOrFile::Directory(files) => {
                for n in files.0.borrow_mut().iter_mut() {
                    n.for_each_file(callable)
                }
            }
            DirOrFile::MissingEntry(_) => (),
        }
    }

    fn expect_workspace_index(&mut self) -> &mut WorkspaceFileIndex {
        match &mut self.type_ {
            DirOrFile::File(index) => index,
            _ => unreachable!(),
        }
    }

    fn find_dir_content(&self, vfs: &dyn Vfs, path: &str) -> Option<Rc<DirContent>> {
        let (name, rest) = vfs.split_off_folder(path);
        match &self.type_ {
            DirOrFile::Directory(files) => {
                for n in files.0.borrow().iter() {
                    if name == n.name {
                        return match rest {
                            Some(rest) => n.find_dir_content(vfs, rest),
                            None => Some(n.directory_entries().unwrap().clone()),
                        };
                    }
                }
            }
            DirOrFile::File(_) => unreachable!(),
            DirOrFile::MissingEntry(_) => unreachable!(),
        }
        None
    }
}

#[derive(Debug, Default, Clone)]
pub struct DirContent(RefCell<Vec<DirEntry>>);

#[derive(Debug)]
pub struct AddedFile {
    pub invalidations: Invalidations,
    pub directory: Rc<DirContent>,
    pub workspace_file_index: *mut WorkspaceFileIndex,
}

impl AddedFile {
    pub fn set_file_index(&self, index: FileIndex) {
        // Theoretically we could just search in the directory for the entry again, but I'm too
        // lazy for that and it's faster this way.
        unsafe { &mut *self.workspace_file_index }.set(index);
    }
}

impl DirContent {
    pub fn iter(&self) -> DirContentIter {
        DirContentIter {
            inner: Some(Ref::map(self.0.borrow(), |v| &v[..])),
        }
    }

    fn remove_name(&self, name: &str) {
        self.0.borrow_mut().retain(|f| f.name != name)
    }

    fn is_empty(&self) -> bool {
        self.0.borrow().is_empty()
    }

    pub fn search(&self, name: &str) -> Option<RefMut<DirEntry>> {
        let borrow = self.0.borrow_mut();
        // We need to run this search twice, because Rust needs #![feature(cell_filter_map)]
        // https://github.com/rust-lang/rust/issues/81061
        borrow.iter().find(|entry| entry.name == name)?;
        Some(RefMut::map(borrow, |dir| {
            dir.iter_mut().find(|entry| entry.name == name).unwrap()
        }))
    }

    fn ensure_dir_and_return_name<'a>(
        dir: &Rc<DirContent>,
        vfs: &dyn Vfs,
        path: &'a str,
    ) -> (Rc<DirContent>, &'a str) {
        let (name, rest) = vfs.split_off_folder(path);
        if let Some(rest) = rest {
            dir.search(name)
                .map(|x| match &x.type_ {
                    DirOrFile::Directory(rc) => Self::ensure_dir_and_return_name(rc, vfs, rest),
                    _ => todo!(),
                })
                .unwrap_or_else(|| {
                    let new_rc = Default::default();
                    let result = Self::ensure_dir_and_return_name(&new_rc, vfs, rest);
                    dir.0.borrow_mut().push(DirEntry {
                        name: name.to_owned(),
                        type_: DirOrFile::Directory(new_rc),
                    });
                    result
                })
        } else {
            (dir.clone(), name)
        }
    }

    fn ensure_file(dir: &Rc<DirContent>, vfs: &dyn Vfs, name: &str) -> AddedFile {
        let mut invalidations = Invalidations::default();
        let workspace_file_index = dir
            .search(name)
            .map(|mut entry| match &mut entry.type_ {
                DirOrFile::File(index) => index as *mut WorkspaceFileIndex,
                DirOrFile::MissingEntry(inv) => {
                    invalidations = std::mem::take(inv);
                    entry.type_ = DirOrFile::File(WorkspaceFileIndex::none());
                    entry.expect_workspace_index()
                }
                DirOrFile::Directory(_) => todo!(),
            })
            .unwrap_or_else(|| {
                let mut borrow = dir.0.borrow_mut();
                borrow.push(DirEntry::new_file(name.to_owned()));
                borrow.last_mut().unwrap().expect_workspace_index()
            });
        AddedFile {
            invalidations,
            directory: dir.clone(),
            workspace_file_index,
        }
    }

    pub fn add_missing_entry(&self, name: String, invalidates: FileIndex) {
        let mut vec = self.0.borrow_mut();
        if let Some(pos) = vec.iter().position(|x| x.name == name) {
            if let DirOrFile::MissingEntry(invalidations) = &vec[pos].type_ {
                invalidations.add(invalidates)
            } else {
                unreachable!()
            }
        } else {
            let invalidations = Invalidations::default();
            invalidations.add(invalidates);
            vec.push(DirEntry {
                name,
                type_: DirOrFile::MissingEntry(invalidations),
            })
        }
    }
}

pub struct DirContentIter<'a> {
    inner: Option<Ref<'a, [DirEntry]>>,
}

impl<'a> Iterator for DirContentIter<'a> {
    type Item = Ref<'a, DirEntry>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.inner.take() {
            Some(borrow) => match *borrow {
                [] => None,
                [_, ..] => {
                    let (head, tail) = Ref::map_split(borrow, |slice| (&slice[0], &slice[1..]));
                    self.inner.replace(tail);
                    Some(head)
                }
            },
            None => None,
        }
    }
}
