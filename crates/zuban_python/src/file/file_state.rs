#![allow(unused_imports, dead_code)] // TODO remove this
use std::{any::Any, pin::Pin, rc::Rc};

use config::DiagnosticConfig;
use parsa_python_cst::{CodeIndex, Keyword, NodeIndex};
use vfs::{FileIndex, NormalizedPath};

use crate::{
    database::Database,
    diagnostics::Diagnostic,
    file::PythonFile,
    inferred::Inferred,
    lines::PositionInfos,
    name::{Name, Names},
    InputPosition, PythonProject,
};

pub trait File: std::fmt::Debug {
    fn file_index(&self) -> FileIndex;

    fn line_column_to_byte(&self, input: InputPosition) -> Result<CodeIndex, String>;
    fn byte_to_position_infos<'db>(
        &'db self,
        db: &'db Database,
        byte: CodeIndex,
    ) -> PositionInfos<'db>;

    fn file_path<'db>(&self, db: &'db Database) -> &'db NormalizedPath {
        db.file_path(self.file_index())
    }
    fn code(&self) -> &str;

    fn diagnostics<'db>(&'db self, db: &'db Database) -> Box<[Diagnostic<'db>]>;
    fn invalidate_full_db(&mut self, project: &PythonProject);
    fn has_super_file(&self) -> bool;
}
