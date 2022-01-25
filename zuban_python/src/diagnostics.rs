use parsa_python_ast::NodeIndex;

use crate::database::{Database, Locality};

#[derive(Debug)]
pub struct Issue {
    issue_id: u32,
    tree_node: NodeIndex,
    locality: Locality,
}

pub struct Diagnostic<'db> {
    db: &'db Database,
    issue: &'db Issue,
}

impl<'db> Diagnostic<'db> {
    pub fn new(db: &'db Database, issue: &'db Issue) -> Self {
        Self { db, issue }
    }

    pub fn as_string(&self) -> String {
        "TODO".to_owned()
    }
}

impl std::fmt::Debug for Diagnostic<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", &self.as_string())
    }
}
