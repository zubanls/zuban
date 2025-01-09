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
    fn invalidate_full_db(&mut self, project: &PythonProject);
    fn has_super_file(&self) -> bool;
}
