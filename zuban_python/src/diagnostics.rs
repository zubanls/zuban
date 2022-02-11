use parsa_python_ast::NodeIndex;

use crate::database::Database;
use crate::file_state::File;
use crate::name::TreePosition;

#[derive(Debug)]
pub enum IssueType {
    AttributeError(String, String),
    ArgumentIssue(String),
    ValidType(String),
    IncompatibleReturn(String, String),
    IncompatibleAssignment(String, String),
    ModuleNotFound(String),

    Note(String),
}

#[derive(Debug)]
pub struct Issue {
    pub type_: IssueType,
    pub node_index: NodeIndex,
}

pub struct Diagnostic<'db> {
    db: &'db Database,
    file: &'db dyn File,
    pub(in crate) issue: &'db Issue,
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
        let mut type_ = "error";
        let error = match &self.issue.type_ {
            IssueType::AttributeError(object, name) => {
                format!("{} has no attribute {:?}", object, name)
            }
            IssueType::IncompatibleReturn(got, expected) => {
                format!(
                    "Incompatible return value type (got {:?}, expected {:?})",
                    got, expected
                )
            }
            IssueType::IncompatibleAssignment(got, expected) => {
                format!(
                    "Incompatible types in assignment (expression has type {:?}, variable has type {:?})",
                    got, expected
                )
            }
            IssueType::ArgumentIssue(s) | IssueType::ValidType(s) => s.clone(),
            IssueType::ModuleNotFound(s) => format!(
                "Cannot find implementation or library stub for module named {:?}",
                s
            ),
            IssueType::Note(s) => {
                type_ = "note";
                s.clone()
            }
        };
        let string = String::new();
        format!(
            "{}:{}: {}: {}",
            // TODO REMOVE mypy removal
            self.db
                .file_path(self.file.file_index())
                .trim_start_matches("/mypylike/"),
            self.start_position().line_and_column().0,
            type_,
            error
        )
    }
}

impl std::fmt::Debug for Diagnostic<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", &self.as_string())
    }
}
