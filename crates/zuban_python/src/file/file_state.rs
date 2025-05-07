#![allow(unused_imports, dead_code)] // TODO remove this
use std::{any::Any, pin::Pin, rc::Rc};

use config::DiagnosticConfig;
use parsa_python_cst::{CodeIndex, Keyword, NodeIndex};
use vfs::FileIndex;

use crate::{
    database::Database,
    diagnostics::Diagnostic,
    file::PythonFile,
    inferred::Inferred,
    lines::PositionInfos,
    name::{Name, Names},
    PythonProject,
};

#[derive(Debug)]
pub(crate) enum Leaf<'db> {
    Name(Box<dyn Name<'db> + 'db>),
    String,
    Number,
    Keyword(Keyword<'db>),
    None,
}

pub trait File: std::fmt::Debug {
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
    fn byte_to_position_infos<'db>(
        &'db self,
        db: &'db Database,
        byte: CodeIndex,
    ) -> PositionInfos<'db>;

    fn file_path<'db>(&self, db: &'db Database) -> &'db str {
        db.file_path(self.file_index())
    }
    fn code(&self) -> &str;

    fn diagnostics<'db>(&'db self, db: &'db Database) -> Box<[Diagnostic<'db>]>;
    fn invalidate_full_db(&mut self, project: &PythonProject);
    fn has_super_file(&self) -> bool;
}

#[derive(Debug)]
pub(crate) struct FilePosition<'db> {
    file: &'db dyn File,
    position: CodeIndex,
}

impl<'db> FilePosition<'db> {
    pub(crate) fn new(file: &'db dyn File, position: CodeIndex) -> Self {
        Self { file, position }
    }

    pub(crate) fn wrap_sub_file(self, file: &'db dyn File, offset: CodeIndex) -> Self {
        Self {
            file,
            position: self.position,
        }
    }

    pub fn position_infos(&self, db: &'db Database) -> PositionInfos<'db> {
        self.file.byte_to_position_infos(db, self.position)
    }
}
