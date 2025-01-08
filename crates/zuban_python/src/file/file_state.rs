use std::{any::Any, pin::Pin, rc::Rc};

use config::DiagnosticConfig;
use parsa_python_cst::{CodeIndex, Keyword, NodeIndex};
use vfs::{FileEntry, FileIndex, Invalidations};

use crate::{
    database::Database,
    diagnostics::Diagnostic,
    file::PythonFile,
    inferred::Inferred,
    name::{FilePosition, Name, Names},
    PythonProject,
};

#[derive(Debug)]
pub enum Leaf<'db> {
    Name(Box<dyn Name<'db> + 'db>),
    String,
    Number,
    Keyword(Keyword<'db>),
    None,
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
        self.state = InternalFileExistence::Unloaded;
        self.file_entry.invalidations.take()
    }

    pub(crate) fn new_parsed(
        file_entry: Rc<FileEntry>,
        path: Box<str>,
        file: PythonFile,
        invalidates_db: bool,
    ) -> Self {
        if invalidates_db {
            file_entry.invalidations.set_invalidates_db();
        }
        Self {
            file_entry,
            path,
            state: InternalFileExistence::Parsed(file),
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
