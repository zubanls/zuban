use std::sync::{Arc, Mutex, OnceLock, RwLock, RwLockReadGuard, RwLockWriteGuard, Weak};

use utils::{MappedReadGuard, MappedWriteGuard, VecRwLockWrapper};

use crate::{NormalizedPath, PathWithScheme, VfsHandler, Workspace};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FileIndex(pub u32);

impl std::fmt::Display for FileIndex {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Debug, Clone)]
pub enum Parent {
    Directory(Weak<Directory>),
    Workspace(Weak<Workspace>),
}

impl Parent {
    pub(crate) fn with_dir<T>(
        &self,
        vfs: &dyn VfsHandler,
        callable: impl FnOnce(&Entries) -> T,
    ) -> T {
        match self {
            Self::Directory(dir) => callable(Directory::entries(vfs, &dir.upgrade().unwrap())),
            Self::Workspace(w) => callable(&w.upgrade().unwrap().entries),
        }
    }

    pub fn maybe_dir(&self) -> Result<Arc<Directory>, &Weak<Workspace>> {
        match self {
            Self::Directory(dir) => Ok(dir.upgrade().unwrap()),
            Self::Workspace(w) => Err(w),
        }
    }

    pub fn most_outer_dir(&self) -> Option<Arc<Directory>> {
        match self {
            Self::Directory(dir) => {
                let d = dir.upgrade().unwrap();
                d.parent.most_outer_dir().or_else(|| Some(d))
            }
            Self::Workspace(_) => None,
        }
    }

    pub(crate) fn absolute_path(&self, vfs: &dyn VfsHandler) -> PathWithScheme {
        match self {
            Self::Directory(dir) => dir.upgrade().unwrap().absolute_path(vfs),
            Self::Workspace(workspace) => {
                let workspace = workspace.upgrade().unwrap();
                PathWithScheme {
                    // This should be normalized, because it's joined
                    path: workspace.root_path.clone(),
                    scheme: workspace.scheme.clone(),
                }
            }
        }
    }

    fn relative_path(&self, vfs: &dyn VfsHandler) -> String {
        match self {
            Self::Directory(dir) => dir.upgrade().unwrap().relative_path(vfs),
            Self::Workspace(_) => String::new(),
        }
    }

    pub fn workspace_path(&self) -> Arc<NormalizedPath> {
        match self {
            Self::Directory(dir) => dir.upgrade().unwrap().parent.workspace_path(),
            Self::Workspace(workspace) => workspace.upgrade().unwrap().root_path.clone(),
        }
    }

    pub fn with_entries<T>(&self, vfs: &dyn VfsHandler, callback: impl FnOnce(&Entries) -> T) -> T {
        match self {
            Self::Directory(dir) => callback(Directory::entries(vfs, &dir.upgrade().unwrap())),
            Self::Workspace(workspace) => callback(&workspace.upgrade().unwrap().entries),
        }
    }
}

#[derive(Debug)]
pub struct FileEntry {
    pub name: Box<str>,
    file_index: Mutex<Option<FileIndex>>,
    pub(crate) invalidations: Invalidations,
    pub parent: Parent,
}

impl Clone for FileEntry {
    fn clone(&self) -> Self {
        Self {
            name: self.name.clone(),
            file_index: Mutex::new(*self.file_index.lock().unwrap()),
            invalidations: self.invalidations.clone(),
            parent: self.parent.clone(),
        }
    }
}

impl FileEntry {
    pub(crate) fn new(parent: Parent, name: Box<str>) -> Arc<Self> {
        Arc::new(Self {
            name,
            file_index: Default::default(),
            invalidations: Default::default(),
            parent,
        })
    }

    pub fn absolute_path(&self, vfs: &dyn VfsHandler) -> PathWithScheme {
        let parent = self.parent.absolute_path(vfs);
        PathWithScheme {
            // This should be normalized, because it's joined
            path: NormalizedPath::new_arc(vfs.join(&parent.path, &self.name)),
            scheme: parent.scheme,
        }
    }

    pub fn relative_path(&self, vfs: &dyn VfsHandler) -> String {
        let mut path = self.parent.relative_path(vfs);
        if path.is_empty() {
            return self.name.clone().into();
        }
        path.push(vfs.separator());
        path + &self.name
    }

    pub fn add_invalidation(&self, element: FileIndex) {
        self.invalidations.add(element)
    }

    pub fn get_file_index(&self) -> Option<FileIndex> {
        *self.file_index.lock().unwrap()
    }

    pub(crate) fn with_set_file_index(&self, callback: impl FnOnce() -> FileIndex) -> FileIndex {
        let mut guard = self.file_index.lock().unwrap();
        if let Some(file_index) = *guard {
            return file_index;
        }
        let file_index = callback();
        debug_assert_eq!(*guard, None);
        *guard = Some(file_index);
        file_index
    }
}

#[derive(Debug, Clone)]
pub struct MissingEntry {
    pub(crate) name: Box<str>,
    pub(crate) invalidations: Invalidations,
}

#[derive(Debug, Clone)]
pub enum DirectoryEntry {
    File(Arc<FileEntry>),
    MissingEntry(MissingEntry),
    Directory(Arc<Directory>),
}

impl DirectoryEntry {
    pub fn name(&self) -> &str {
        match self {
            DirectoryEntry::File(file) => &file.name,
            DirectoryEntry::Directory(dir) => &dir.name,
            DirectoryEntry::MissingEntry(MissingEntry { name, .. }) => name,
        }
    }

    pub(crate) fn walk_entries(
        &self,
        vfs: &dyn VfsHandler,
        callable: &mut impl FnMut(&Self) -> bool,
    ) {
        if !callable(self) {
            return;
        };
        self.walk_internal(vfs, &mut |_, entry| callable(entry))
    }

    fn walk_internal(
        &self,
        vfs: &dyn VfsHandler,
        callable: &mut impl FnMut(&Entries, &Self) -> bool,
    ) {
        if let DirectoryEntry::Directory(dir) = self {
            let entries = Directory::entries(vfs, dir);
            for entry in entries.borrow().iter() {
                if callable(entries, entry) {
                    entry.walk_internal(vfs, callable);
                };
            }
        }
    }
}

#[derive(Debug, Default)]
pub struct Entries(RwLock<Vec<DirectoryEntry>>);

impl Clone for Entries {
    fn clone(&self) -> Self {
        Self(RwLock::new(self.0.read().unwrap().clone()))
    }
}

#[derive(Debug, Clone)]
pub struct Directory {
    entries: OnceLock<Entries>,
    pub parent: Parent,
    pub name: Box<str>,
}

#[derive(Debug)]
pub(crate) struct AddedFile {
    pub(crate) invalidations: Invalidations,
    pub(crate) file_entry: Arc<FileEntry>,
}

impl Directory {
    pub(crate) fn new(parent: Parent, name: Box<str>) -> Arc<Self> {
        Arc::new(Self {
            entries: Default::default(),
            parent,
            name,
        })
    }

    pub fn absolute_path(&self, vfs: &dyn VfsHandler) -> PathWithScheme {
        let parent = self.parent.absolute_path(vfs);
        PathWithScheme {
            // This should be normalized, because it's joined
            path: NormalizedPath::new_arc(vfs.join(&parent.path, &self.name)),
            scheme: parent.scheme,
        }
    }

    pub fn relative_path(&self, vfs: &dyn VfsHandler) -> String {
        let mut path = self.parent.relative_path(vfs);
        if path.is_empty() {
            return self.name.clone().into();
        }
        path.push(vfs.separator());
        path + &self.name
    }

    pub fn entries<'x>(vfs: &dyn VfsHandler, dir: &'x Arc<Directory>) -> &'x Entries {
        dir.entries.get_or_init(|| {
            vfs.read_and_watch_dir(
                &dir.absolute_path(vfs).path,
                Parent::Directory(Arc::downgrade(dir)),
            )
        })
    }
}

impl Entries {
    pub fn from_vec(vec: Vec<DirectoryEntry>) -> Self {
        Self(RwLock::from(vec))
    }

    fn borrow(&self) -> RwLockReadGuard<'_, Vec<DirectoryEntry>> {
        self.0.read().unwrap()
    }

    pub(crate) fn borrow_mut(&self) -> RwLockWriteGuard<'_, Vec<DirectoryEntry>> {
        self.0.write().unwrap()
    }

    pub fn iter(&self) -> VecRwLockWrapper<'_, Vec<DirectoryEntry>, DirectoryEntry> {
        VecRwLockWrapper::new(MappedReadGuard::map(self.borrow(), |x| x))
    }

    pub(crate) fn remove_name(&self, name: &str) -> Option<DirectoryEntry> {
        let mut entries = self.borrow_mut();
        let pos = entries.iter().position(|f| f.name() == name)?;
        Some(entries.swap_remove(pos))
    }

    pub fn search(
        &self,
        name: &str,
    ) -> Option<MappedReadGuard<'_, Vec<DirectoryEntry>, DirectoryEntry>> {
        let borrow = self.borrow();
        // We need to do this indirectly, because Rust needs #![feature(cell_filter_map)]
        // https://github.com/rust-lang/rust/issues/81061
        let pos = borrow.iter().position(|entry| entry.name() == name)?;
        Some(MappedReadGuard::map(borrow, |dir| &dir[pos]))
    }

    pub(crate) fn search_path(&self, vfs: &dyn VfsHandler, path: &str) -> Option<DirOrFile> {
        let (name, rest) = vfs.split_off_folder(path);
        if let Some(entry) = self.search(name) {
            if let Some(rest) = rest {
                if let DirectoryEntry::Directory(dir) = &*entry {
                    return Directory::entries(vfs, dir).search_path(vfs, rest);
                }
            } else {
                return match &*entry {
                    DirectoryEntry::File(f) => Some(DirOrFile::File(f.clone())),
                    DirectoryEntry::MissingEntry(_) => None,
                    DirectoryEntry::Directory(d) => Some(DirOrFile::Dir(d.clone())),
                };
            }
        }
        None
    }

    pub fn search_mut(
        &self,
        name: &str,
    ) -> Option<MappedWriteGuard<'_, Vec<DirectoryEntry>, DirectoryEntry>> {
        let borrow = self.borrow_mut();
        // We need to run this search twice, because Rust needs #![feature(cell_filter_map)]
        // https://github.com/rust-lang/rust/issues/81061
        borrow.iter().find(|entry| entry.name() == name)?;
        Some(MappedWriteGuard::map(borrow, |dir| {
            dir.iter_mut().find(|entry| entry.name() == name).unwrap()
        }))
    }

    pub(crate) fn ensure_file(&self, parent: Parent, name: &str) -> AddedFile {
        let mut invalidations = Invalidations::default();
        let file_entry = if let Some(mut entry) = self.search_mut(name) {
            match &mut *entry {
                DirectoryEntry::File(file_entry) => file_entry.clone(),
                DirectoryEntry::MissingEntry(MissingEntry {
                    invalidations: inv,
                    name,
                }) => {
                    invalidations = inv.take();
                    let file_entry = FileEntry::new(parent, std::mem::take(name));
                    *entry = DirectoryEntry::File(file_entry.clone());
                    file_entry
                }
                DirectoryEntry::Directory(..) => unimplemented!(
                    "What happens when we want to write a file on top of a directory? When does this happen?"
                ),
            }
        } else {
            let mut borrow = self.borrow_mut();
            let entry = FileEntry::new(parent, name.into());
            borrow.push(DirectoryEntry::File(entry.clone()));
            entry
        };
        AddedFile {
            invalidations,
            file_entry,
        }
    }

    pub(crate) fn unload_file(&self, vfs: &dyn VfsHandler, path: &str) {
        let (name, rest) = vfs.split_off_folder(path);
        if let Some(entry) = self.search(name) {
            if let Some(rest) = rest {
                if let DirectoryEntry::Directory(dir) = &*entry {
                    Directory::entries(vfs, dir).unload_file(vfs, rest);
                }
            } else if matches!(*entry, DirectoryEntry::File(_)) {
                drop(entry);
                self.remove_name(name);
            }
        }
    }

    pub fn add_missing_entry(&self, name: &str, invalidates: FileIndex) {
        let mut vec = self.borrow_mut();
        if let Some(item) = vec.iter_mut().find(|x| x.name() == name) {
            match &item {
                DirectoryEntry::MissingEntry(missing) => missing.invalidations.add(invalidates),
                // Files might be named `pytest` and therefore not be a valid Python files, but
                // still exist in the tree.
                DirectoryEntry::File(file) => file.invalidations.add(invalidates),
                DirectoryEntry::Directory(_) => {
                    // TODO this probably happens with a directory called `foo.py`.
                    tracing::error!("Did not add invalidation for directory {}", name);
                }
            }
        } else {
            let invalidations = Invalidations::default();
            invalidations.add(invalidates);
            vec.push(DirectoryEntry::MissingEntry(MissingEntry {
                invalidations,
                name: name.to_string().into_boxed_str(),
            }))
        }
    }

    pub(crate) fn delete_directory(&self, vfs: &dyn VfsHandler, path: &str) -> Result<(), String> {
        let (name, rest) = vfs.split_off_folder(path);
        if let Some(inner) = self.search(name) {
            match &*inner {
                DirectoryEntry::Directory(dir) => {
                    if let Some(rest) = rest {
                        Directory::entries(vfs, dir).delete_directory(vfs, rest)
                    } else {
                        drop(inner);
                        self.remove_name(name);
                        Ok(())
                    }
                }
                DirectoryEntry::MissingEntry { .. } => {
                    Err(format!("Path {path} cannot be found (missing)"))
                }
                DirectoryEntry::File(_) => Err(format!(
                    "Path {path} is supposed to be a directory but is a file"
                )),
            }
        } else {
            Err(format!("Path {path} cannot be found"))
        }
    }

    /// Walks the entries and aborts descending if the callable returns false
    pub fn walk_entries(
        &self,
        vfs: &dyn VfsHandler,
        callable: &mut impl FnMut(&Self, &DirectoryEntry) -> bool,
    ) {
        for entry in self.borrow().iter() {
            if callable(self, entry) {
                entry.walk_internal(vfs, callable)
            }
        }
    }
}

#[derive(Debug)]
pub enum DirOrFile {
    Dir(Arc<Directory>),
    File(Arc<FileEntry>),
}

#[derive(Debug, Default)]
pub(crate) struct Invalidations(RwLock<InvalidationDetail<Vec<FileIndex>>>);

#[derive(Debug, Clone)]
pub(crate) enum InvalidationDetail<T> {
    InvalidatesDb,
    Some(T),
}

impl<T: Default> Default for InvalidationDetail<T> {
    fn default() -> Self {
        Self::Some(Default::default())
    }
}

impl<T> InvalidationDetail<T> {
    pub(crate) fn map<U, F>(self, f: F) -> InvalidationDetail<U>
    where
        F: FnOnce(T) -> U,
    {
        match self {
            InvalidationDetail::Some(x) => InvalidationDetail::Some(f(x)),
            InvalidationDetail::InvalidatesDb => InvalidationDetail::InvalidatesDb,
        }
    }
}

impl Invalidations {
    pub(crate) fn set_invalidates_db(&self) {
        *self.0.write().unwrap() = InvalidationDetail::InvalidatesDb;
    }

    pub(crate) fn invalidates_db(&self) -> bool {
        matches!(&*self.0.read().unwrap(), InvalidationDetail::InvalidatesDb)
    }

    pub(crate) fn add(&self, element: FileIndex) {
        if let InvalidationDetail::Some(invs) = &mut *self.0.write().unwrap() {
            if !invs.contains(&element) {
                invs.push(element);
            }
        }
    }

    pub(crate) fn extend(&mut self, other: Self) {
        match (self.0.get_mut().unwrap(), other.0.into_inner().unwrap()) {
            (InvalidationDetail::Some(invs), InvalidationDetail::Some(other)) => invs.extend(other),
            _ => self.0 = RwLock::new(InvalidationDetail::InvalidatesDb),
        }
    }

    pub(crate) fn take(&self) -> Self {
        if self.invalidates_db() {
            return self.clone();
        }
        Self(RwLock::new(std::mem::take(&mut self.0.write().unwrap())))
    }

    pub(crate) fn iter(
        &self,
    ) -> InvalidationDetail<VecRwLockWrapper<'_, InvalidationDetail<Vec<FileIndex>>, FileIndex>>
    {
        let r = self.0.read().unwrap();
        if let InvalidationDetail::InvalidatesDb = &*r {
            return InvalidationDetail::InvalidatesDb;
        }
        InvalidationDetail::Some(VecRwLockWrapper::new(MappedReadGuard::map(r, |r| {
            let InvalidationDetail::Some(vec) = r else {
                unreachable!()
            };
            vec
        })))
    }

    pub(crate) fn into_iter(self) -> InvalidationDetail<impl Iterator<Item = FileIndex>> {
        self.0.into_inner().unwrap().map(|invs| invs.into_iter())
    }

    pub(crate) fn is_empty(&self) -> bool {
        match &*self.0.read().unwrap() {
            InvalidationDetail::Some(file_indexes) => file_indexes.is_empty(),
            InvalidationDetail::InvalidatesDb => false,
        }
    }
}

impl Clone for Invalidations {
    fn clone(&self) -> Self {
        Self(RwLock::new(self.0.read().unwrap().clone()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_sizes() {
        // This would ideally be 8, but the Arc<AbsPath> causes 16 bytes
        assert_eq!(std::mem::size_of::<Parent>(), 16);
    }
}
