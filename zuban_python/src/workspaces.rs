use std::cell::Cell;
use std::path::PathBuf;
use walkdir::WalkDir;

use crate::database::FileIndex;
use crate::file_state::FileStateLoader;

#[derive(Debug, Default)]
pub struct Workspaces(Vec<Workspace>);

impl Workspaces {
    pub fn add(&mut self, loaders: &[Box<dyn FileStateLoader>], root: String) {
        self.0.push(Workspace::new(loaders, root))
    }

    pub fn directories(&self) -> impl Iterator<Item = (&str, &[DirectoryOrFile])> {
        self.0
            .iter()
            .map(|x| (x.root().name(), x.root().directory_entries().unwrap()))
    }

    pub fn add_in_memory_file(&mut self, path: &str, file_index: FileIndex) {
        for workspace in &mut self.0 {
            if path.starts_with(workspace.root.name()) {
                if let DirectoryOrFile::Directory(name, files) = &mut workspace.root {
                    // TODO this is obviously wrong, nested files are not cared for
                    files.push(DirectoryOrFile::File(
                        path[name.len()..].to_owned(),
                        WorkspaceFileIndex::some(file_index),
                    ))
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
                    files.retain(|f| f.name() != name);
                }
            }
        }
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
            DirectoryOrFile::Directory(root, vec![]),
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
                    .directory_entries_mut()
                    .unwrap()
                    .push(n);
            }
            let name = entry.file_name();
            if let Some(name) = name.to_str() {
                match entry.metadata() {
                    Ok(m) => {
                        if m.is_dir() {
                            stack.push((
                                entry.path().to_owned(),
                                DirectoryOrFile::Directory(name.to_owned(), vec![]),
                            ));
                        } else {
                            stack
                                .last_mut()
                                .unwrap()
                                .1
                                .directory_entries_mut()
                                .unwrap()
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
                parent.1.directory_entries_mut().unwrap().push(current.1)
            } else {
                return Self { root: current.1 };
            }
        }
        unreachable!()
    }

    pub fn root(&self) -> &DirectoryOrFile {
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

#[derive(Debug)]
pub enum DirectoryOrFile {
    File(String, WorkspaceFileIndex),
    Directory(String, Vec<DirectoryOrFile>),
}

impl DirectoryOrFile {
    pub fn name(&self) -> &str {
        match self {
            Self::Directory(name, _) => name,
            Self::File(name, _) => name,
        }
    }

    pub fn directory_entries(&self) -> Option<&[DirectoryOrFile]> {
        match self {
            DirectoryOrFile::Directory(_, entries) => Some(entries),
            _ => None,
        }
    }

    pub fn directory_entries_mut(&mut self) -> Option<&mut Vec<DirectoryOrFile>> {
        match self {
            DirectoryOrFile::Directory(_, entries) => Some(entries),
            _ => None,
        }
    }
}
