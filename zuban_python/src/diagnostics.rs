use parsa_python_ast::NodeIndex;

use crate::database::Database;
use crate::file_state::File;
use crate::name::TreePosition;

#[derive(Debug)]
pub enum IssueType {
    AttributeError(String, String),
}

#[derive(Debug)]
pub struct Issue {
    pub type_: IssueType,
    pub node_index: NodeIndex,
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

    fn start_position(&self) -> TreePosition<'db> {
        self.file.node_start_position(self.issue.node_index)
    }

    fn end_position(&self) -> TreePosition<'db> {
        self.file.node_end_position(self.issue.node_index)
    }

    pub fn as_string(&self) -> String {
        let error = match &self.issue.type_ {
            IssueType::AttributeError(object, name) => {
                format!("{:?} has no attribute {:?}", object, name)
            }
        };
        format!(
            "{}:{}: error: {}",
            self.db.file_path(self.file.file_index()),
            self.start_position().line_and_column().0,
            error
        )
    }
}

impl std::fmt::Debug for Diagnostic<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", &self.as_string())
    }
}
