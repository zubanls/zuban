use parsa_python_ast::NodeIndex;

use crate::database::Database;
use crate::file::PythonFile;
use crate::file_state::File;
use crate::name::TreePosition;
use crate::node_ref::NodeRef;

#[derive(Debug)]
pub enum IssueType {
    AttributeError(String, String),
    NameError(String),
    ArgumentIssue(String),
    ValidType(String),
    IncompatibleReturn(String, String),
    IncompatibleAssignment(String, String),
    ModuleNotFound(String),
    TypeNotFound,
    TypeArgumentIssue(String, usize, usize),
    TypeAliasArgumentIssue(usize, usize),
    NotCallable(String),
    UnsupportedOperand(String, String, String),
    InvalidGetItem(String),
    NotIndexable(String),
    FunctionGetItem,

    MethodWithoutArguments,

    Note(String),
}

#[derive(Debug)]
pub struct Issue {
    pub type_: IssueType,
    pub node_index: NodeIndex,
}

pub struct Diagnostic<'db> {
    db: &'db Database,
    file: &'db PythonFile,
    pub(in crate) issue: &'db Issue,
}

impl<'db> Diagnostic<'db> {
    pub fn new(db: &'db Database, file: &'db PythonFile, issue: &'db Issue) -> Self {
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
        // TODO REMOVE mypy removal
        let path = self
            .db
            .file_path(self.file.file_index())
            .trim_start_matches("/mypylike/");
        let line = self.start_position().line_and_column().0;
        let error = match &self.issue.type_ {
            IssueType::AttributeError(object, name) => {
                format!("{} has no attribute {:?}", object, name)
            }
            IssueType::NameError(name) => {
                format!("Name {:?} is not defined", name)
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
            IssueType::TypeNotFound => {
                let primary = NodeRef::new(self.file, self.issue.node_index);
                format!("Name {:?} is not defined", primary.as_code())
            }
            IssueType::TypeArgumentIssue(class, expected, given) => {
                if *expected == 0 {
                    format!("{:?} expects no type arguments, but {} given", class, given)
                } else {
                    format!(
                        "{:?} expects {} type arguments, but {} given",
                        class, expected, given
                    )
                }
            }
            IssueType::TypeAliasArgumentIssue(expected, given) => {
                format!(
                    "Bad number of arguments for type alias, expected: {}, given: {}",
                    expected, given
                )
            }
            IssueType::ModuleNotFound(s) => format!(
                "Cannot find implementation or library stub for module named {:?}\n\
                 {}:{}: note: See https://mypy.readthedocs.io/en/stable/running_mypy.html#missing-imports",
                 s, path, line
            ),
            IssueType::NotCallable(s) => format!("{} not callable", s),
            IssueType::UnsupportedOperand(operand, left, right) => {
                format!(
                    "Unsupported operand types for {} ({:?} and {:?})",
                    operand, left, right
                )
            }
            IssueType::InvalidGetItem(s) => s.clone(),
            IssueType::NotIndexable(s) => format!("Value of type {:?} is not indexable", s),
            IssueType::MethodWithoutArguments => {
                "Method must have at least one argument".to_owned()
            }
            IssueType::FunctionGetItem => {
                "Type application is only supported for generic classes".to_owned()
            }
            IssueType::Note(s) => {
                type_ = "note";
                s.clone()
            }
        };
        let string = String::new();
        format!("{}:{}: {}: {}", path, line, type_, error)
    }
}

#[derive(Default)]
pub struct DiagnosticConfig {
    pub ignore_missing_imports: bool,
}

impl DiagnosticConfig {
    pub fn should_be_reported(&self, type_: &IssueType) -> bool {
        match type_ {
            IssueType::ModuleNotFound(_) => !self.ignore_missing_imports,
            _ => true,
        }
    }
}

impl std::fmt::Debug for Diagnostic<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", &self.as_string())
    }
}
