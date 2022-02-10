use std::cell::{Cell, Ref, RefCell};
use std::path::PathBuf;
use walkdir::WalkDir;

use crate::database::FileIndex;
use crate::file_state::FileStateLoader;
use crate::utils::Invalidations;

#[derive(Debug, Default)]
pub struct Workspaces(Vec<Workspace>);

impl Workspaces {
    pub fn add(&mut self, loaders: &[Box<dyn FileStateLoader>], root: String) {
        self.0.push(Workspace::new(loaders, root))
    }

    pub fn directories(&self) -> impl Iterator<Item = (&str, &DirContent)> {
        self.0
            .iter()
            .map(|x| (x.root().name(), x.root().directory_entries().unwrap()))
    }

    pub fn add_file(&mut self, path: &str, file_index: FileIndex) {
        for workspace in &mut self.0 {
            if path.starts_with(workspace.root.name()) {
                if let DirectoryOrFile::Directory(name, files) = &mut workspace.root {
                    // TODO this is obviously wrong, nested files are not cared for
                    files.add_file(path[name.len()..].to_owned(), file_index)
                }
            }
        }
    }

    pub fn unload_if_not_available(&mut self, path: &str) {
        // TODO for now we always unload, fix that.
        for workspace in &mut self.0 {
            if let DirectoryOrFile::Directory(ref dir_name, files) = &mut workspace.root {
                if path.starts_with(dir_name) {
                    // TODO this is obviously wrong, nested files are not cared for
                    let name = &path[dir_name.len()..];
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
    root: DirectoryOrFile,
    //watcher: dyn notify::Watcher,
}

impl Workspace {
    fn new(loaders: &[Box<dyn FileStateLoader>], root: String) -> Self {
        let mut stack = vec![(
            PathBuf::from(&root),
            DirectoryOrFile::Directory(root, Default::default()),
        )];
        // TODO optimize if there are a lot of files
        for entry in WalkDir::new(&stack[0].1.name())
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
                                DirectoryOrFile::Directory(name.to_owned(), Default::default()),
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
                                .push(DirectoryOrFile::File(
                                    name.to_owned(),
                                    WorkspaceFileIndex::none(),
                                ));
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

    pub fn root(&self) -> &DirectoryOrFile {
        &self.root
    }

    pub fn root_mut(&mut self) -> &mut DirectoryOrFile {
        &mut self.root
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

#[derive(Debug)]
pub enum DirectoryOrFile {
    File(String, WorkspaceFileIndex),
    MissingEntry(String, Invalidations),
    Directory(String, DirContent),
}

impl DirectoryOrFile {
    pub fn name(&self) -> &str {
        match self {
            Self::Directory(name, _) => name,
            Self::File(name, _) => name,
            Self::MissingEntry(name, _) => name,
        }
    }

    pub fn directory_entries(&self) -> Option<&DirContent> {
        match self {
            DirectoryOrFile::Directory(_, entries) => Some(entries),
            _ => None,
        }
    }

    pub fn for_each_file(&self, callable: &mut impl FnMut(FileIndex)) {
        match self {
            Self::File(_, index) => {
                if let Some(index) = index.get() {
                    callable(index)
                }
            }
            Self::Directory(_, nodes) => {
                for n in nodes.0.borrow().iter() {
                    n.for_each_file(callable)
                }
            }
            Self::MissingEntry(name, _) => (),
        }
    }
}

#[derive(Debug, Default)]
pub struct DirContent(RefCell<Vec<DirectoryOrFile>>);

impl DirContent {
    pub fn iter(&self) -> DirContentIter {
        DirContentIter {
            inner: Some(Ref::map(self.0.borrow(), |v| &v[..])),
        }
    }

    fn remove_name(&mut self, name: &str) {
        self.0.get_mut().retain(|f| f.name() != name);
    }

    fn add_file(&mut self, name: String, file_index: FileIndex) {
        self.0.get_mut().push(DirectoryOrFile::File(
            name,
            WorkspaceFileIndex::some(file_index),
        ))
    }

    pub fn add_missing_entry(&self, name: &str, invalidates: FileIndex) {
        todo!()
    }
}

pub struct DirContentIter<'a> {
    inner: Option<Ref<'a, [DirectoryOrFile]>>,
}

impl<'a> Iterator for DirContentIter<'a> {
    type Item = Ref<'a, DirectoryOrFile>;

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
