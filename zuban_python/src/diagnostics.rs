use parsa_python_ast::NodeIndex;

use crate::database::{Database, Locality};
use crate::file_state::File;

#[derive(Debug)]
pub struct Issue {
    pub issue_id: u32,
    pub tree_node: NodeIndex,
    pub locality: Locality,
}

pub struct Diagnostic<'db> {
    db: &'db Database,
    file: &'db dyn File,
    issue: &'db Issue,
}

impl<'db> Diagnostic<'db> {
    pub fn new(db: &'db Database, file: &'db dyn File, issue: &'db Issue) -> Self {
        Self { db, file, issue }
    }

    pub fn as_string(&self) -> String {
        dbg!(self.file);
        format!("{}: TODO", self.db.file_path(self.file.file_index()))
    }
}

impl std::fmt::Debug for Diagnostic<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", &self.as_string())
    }
}
