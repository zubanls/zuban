use std::{any::Any, fs, path::Path, pin::Pin, rc::Rc};

use config::DiagnosticConfig;
use parsa_python_cst::{CodeIndex, Keyword, NodeIndex};

use crate::{
    database::{Database, FileIndex},
    diagnostics::Diagnostic,
    file::PythonFile,
    imports::STUBS_SUFFIX,
    inferred::Inferred,
    name::{FilePosition, Name, Names},
    workspaces::{FileEntry, Invalidations},
    PythonProject,
};

pub trait Vfs {
    fn read_file(&self, path: &str) -> std::io::Result<String>;

    fn separator(&self) -> char {
        self.separator_u8().into()
    }

    fn separator_u8(&self) -> u8 {
        b'/'
    }

    fn split_off_folder<'a>(&self, path: &'a str) -> (&'a str, Option<&'a str>) {
        if let Some(pos) = path.find(self.separator()) {
            (&path[..pos], Some(&path[pos + 1..]))
        } else {
            (path, None)
        }
    }

    fn dir_path<'a>(&self, path: &'a str) -> Option<&'a str> {
        path.rfind(self.separator()).map(|index| &path[..index])
    }

    fn is_sub_file_of(&self, path: &str, maybe_parent: &str) -> bool {
        Path::new(path).starts_with(Path::new(maybe_parent))
    }
}

#[derive(Default)]
pub struct FileSystemReader {}

impl Vfs for FileSystemReader {
    fn read_file(&self, path: &str) -> std::io::Result<String> {
        tracing::debug!("Read from FS: {path}");
        fs::read_to_string(path)
    }
}

#[derive(Debug)]
pub enum Leaf<'db> {
    Name(Box<dyn Name<'db> + 'db>),
    String,
    Number,
    Keyword(Keyword<'db>),
    None,
}

pub trait FileStateLoader {
    fn responsible_for_file_endings(&self) -> Vec<&str>;

    fn might_be_relevant(&self, name: &str) -> bool;
    fn should_be_ignored(&self, name: &str) -> bool;

    fn load_parsed(
        &self,
        project: &PythonProject,
        file_index: FileIndex,
        file_entry: Rc<FileEntry>,
        path: Box<str>,
        code: Box<str>,
        invalidates_db: bool,
    ) -> Pin<Box<FileState>>;
}

#[derive(Default, Clone)]
pub struct PythonFileLoader {}

impl FileStateLoader for PythonFileLoader {
    fn responsible_for_file_endings(&self) -> Vec<&str> {
        vec!["py", "pyi"]
    }

    fn might_be_relevant(&self, name: &str) -> bool {
        if name.ends_with(".py") || name.ends_with(".pyi") {
            return true;
        }
        !name.contains('.') && (!name.contains('-') || name.ends_with(STUBS_SUFFIX))
            || name == "py.typed"
    }

    fn should_be_ignored(&self, name: &str) -> bool {
        name == "__pycache__" && !name.ends_with(".pyc")
    }

    fn load_parsed(
        &self,
        project: &PythonProject,
        file_index: FileIndex,
        file_entry: Rc<FileEntry>,
        path: Box<str>,
        code: Box<str>,
        invalidates_db: bool,
    ) -> Pin<Box<FileState>> {
        let file = PythonFile::from_path_and_code(project, file_index, &file_entry, &path, code);
        Box::pin(FileState::new_parsed(
            file_entry,
            path,
            file,
            invalidates_db,
        ))
    }
}

pub trait AsAny {
    fn as_any(&self) -> &dyn Any
    where
        Self: 'static;
}

impl<T> AsAny for T {
    fn as_any(&self) -> &dyn Any
    where
        Self: 'static,
    {
        self
    }
}

pub trait File: std::fmt::Debug + AsAny {
    // Called each time a file is loaded
    fn implementation<'db>(&self, _names: Names<'db>) -> Names<'db> {
        vec![]
    }
    fn leaf<'db>(&'db self, db: &'db Database, position: CodeIndex) -> Leaf<'db>;
    fn infer_operator_leaf<'db>(&'db self, db: &'db Database, keyword: Keyword<'db>) -> Inferred;
    fn file_index(&self) -> FileIndex;

    fn node_start_position(&self, n: NodeIndex) -> FilePosition;
    fn node_end_position(&self, n: NodeIndex) -> FilePosition;
    fn line_column_to_byte(&self, line: usize, column: usize) -> CodeIndex;
    fn byte_to_line_column(&self, byte: CodeIndex) -> (usize, usize);

    fn file_path<'db>(&self, db: &'db Database) -> &'db str {
        db.file_path(self.file_index())
    }
    fn code(&self) -> &str;

    fn diagnostics<'db>(
        &'db self,
        db: &'db Database,
        config: &DiagnosticConfig,
    ) -> Box<[Diagnostic<'db>]>;
    fn invalidate_references_to(&mut self, file_index: FileIndex);
    fn invalidate_full_db(&mut self, project: &PythonProject);
    fn has_super_file(&self) -> bool;
}

#[derive(Debug, Clone)]
pub struct FileState {
    path: Box<str>,
    pub file_entry: Rc<FileEntry>,
    state: InternalFileExistence,
    invalidates: Option<Invalidations>,
}

impl FileState {
    pub(crate) fn path(&self) -> &str {
        &self.path
    }

    pub(crate) fn file_entry(&self) -> &Rc<FileEntry> {
        &self.file_entry
    }

    pub(crate) fn code(&self) -> Option<&str> {
        Some(self.file()?.code())
    }

    pub(crate) fn unload_and_return_invalidations(&mut self) -> Invalidations {
        let invalidates = self.take_invalidations();
        self.state = InternalFileExistence::Unloaded;
        invalidates.expect("We don't support rebuilding/unloading after changing of typeshed, yet.")
    }

    pub(crate) fn take_invalidations(&mut self) -> Option<Invalidations> {
        self.invalidates.as_mut().map(std::mem::take)
    }

    pub(crate) fn add_invalidates(&self, file_index: FileIndex) {
        if let Some(invalidates) = &self.invalidates {
            invalidates.add(file_index)
        }
    }

    pub(crate) fn invalidate_invalidates_db(&self) -> bool {
        self.invalidates.is_none()
    }

    pub(crate) fn new_parsed(
        file_entry: Rc<FileEntry>,
        path: Box<str>,
        file: PythonFile,
        invalidates_db: bool,
    ) -> Self {
        Self {
            file_entry,
            path,
            state: InternalFileExistence::Parsed(file),
            invalidates: (!invalidates_db).then(Invalidations::default),
        }
    }

    pub(crate) fn update(&mut self, file: PythonFile) {
        debug_assert!(matches!(self.state, InternalFileExistence::Unloaded));
        self.state = InternalFileExistence::Parsed(file)
    }
    pub(crate) fn file(&self) -> Option<&(dyn File + 'static)> {
        match &self.state {
            InternalFileExistence::Unloaded => None,
            InternalFileExistence::Parsed(f) => Some(f),
        }
    }

    pub(crate) fn maybe_loaded_file_mut(&mut self) -> Option<&mut dyn File> {
        match &mut self.state {
            InternalFileExistence::Parsed(f) => Some(f),
            _ => None,
        }
    }

    pub(crate) fn clone_box(&self, new_file_entry: Rc<FileEntry>) -> Pin<Box<FileState>> {
        let mut new = self.clone();
        new.file_entry = new_file_entry;
        Box::pin(new)
    }
}

#[derive(Clone, Debug)]
enum InternalFileExistence {
    Unloaded,
    Parsed(PythonFile),
}
