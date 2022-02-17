use std::cell::{Cell, Ref, RefCell};
use std::path::PathBuf;
use std::rc::Rc;
use walkdir::WalkDir;

use crate::database::FileIndex;
use crate::file_state::{FileStateLoader, Vfs};
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

    pub fn add_file(&mut self, vfs: &dyn Vfs, path: &str) -> AddedFile {
        for workspace in &mut self.0 {
            dbg!(&workspace.root);
            if path.starts_with(&workspace.root.name) {
                if let DirOrFile::Directory(files) = &mut workspace.root.type_ {
                    // TODO this is obviously wrong, nested files are not cared for
                    return DirContent::add_file(files, vfs, &path[workspace.root.name.len()..]);
                }
            }
        }
        todo!()
    }

    pub fn unload_if_not_available(&mut self, path: &str) {
        // TODO for now we always unload, fix that.
        for workspace in &mut self.0 {
            if let DirOrFile::Directory(files) = &mut workspace.root.type_ {
                if path.starts_with(&workspace.root.name) {
                    // TODO this is obviously wrong, nested files are not cared for
                    let name = &path[workspace.root.name.len()..];
                    files.remove_name(name);
                }
            }
        }
    }

    pub fn last(&self) -> &Workspace {
        // TODO this should probably not be needed
        self.0.last().unwrap()
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
                entry
                    .file_name()
                    .to_str()
                    .map(|name| {
                        !loaders.iter().any(|l| l.should_be_ignored(name))
                            && loaders.iter().any(|l| l.might_be_relevant(name))
                    })
                    .unwrap_or(false)
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

    fn some(file_index: FileIndex) -> Self {
        Self(Cell::new(Some(file_index)))
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

    pub fn for_each_file(&mut self, callable: &mut impl FnMut(FileIndex)) {
        match &self.type_ {
            DirOrFile::File(index) => {
                if let Some(index) = index.get() {
                    callable(index)
                }
            }
            DirOrFile::Directory(nodes) => {
                for n in nodes.0.borrow_mut().iter_mut() {
                    n.for_each_file(callable)
                }
            }
            DirOrFile::MissingEntry(_) => (),
        }
    }
}

#[derive(Debug, Default, Clone)]
pub struct DirContent(RefCell<Vec<DirEntry>>);

pub struct AddedFile {
    pub invalidations: Invalidations,
    pub directory: Rc<DirContent>,
    pub workspace_file_index: *const WorkspaceFileIndex,
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

    fn add_file(dir: &Rc<DirContent>, vfs: &dyn Vfs, name: &str) -> AddedFile {
        let (name, rest) = vfs.split_off_folder(name);
        let new = |entry: &mut DirOrFile| {
            if let Some(rest) = rest {
                let content = Rc::new(Self::default());
                let result = Self::add_file(&content, vfs, rest);
                *entry = DirOrFile::Directory(content);
                return result;
            }

            *entry = DirOrFile::File(WorkspaceFileIndex::none());
            AddedFile {
                invalidations: Invalidations::default(),
                directory: dir.clone(),
                workspace_file_index: match entry {
                    DirOrFile::File(w) => w,
                    _ => unreachable!(),
                },
            }
        };

        for entry in dir.0.borrow_mut().iter_mut() {
            if entry.name == name {
                match &entry.type_ {
                    DirOrFile::Directory(content) => {
                        return Self::add_file(content, vfs, rest.unwrap());
                    }
                    DirOrFile::MissingEntry(_) => {
                        // Just initialize it somehow to overwrite it later
                        let old = std::mem::replace(
                            &mut entry.type_,
                            DirOrFile::File(WorkspaceFileIndex::none()),
                        );
                        if let DirOrFile::MissingEntry(mut invalidations) = old {
                            let mut result = new(&mut entry.type_);
                            // TODO add invalidations
                            result
                                .invalidations
                                .get_mut()
                                .append(invalidations.get_mut());
                            return result;
                        } else {
                            unreachable!()
                        }
                    }
                    // If this is not unreachable, we should probably not have a new file_index here
                    _ => unreachable!(),
                }
            }
        }
        let mut d = dir.0.borrow_mut();
        d.push(DirEntry {
            name: name.to_owned(),
            type_: DirOrFile::File(WorkspaceFileIndex::none()),
        });
        new(&mut d.last_mut().unwrap().type_)
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
