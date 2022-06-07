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
    UnsupportedLeftOperand(String, String, Option<String>),
    InvalidGetItem(String),
    NotIndexable(String),
    TooFewValuesToUnpack(usize, usize),
    OnlyClassTypeApplication,
    InvalidBaseClass,
    DuplicateTypeVar,
    IncompleteGenericOrProtocolTypeVars,

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
        let mut path = self
            .db
            .file_path(self.file.file_index())
            .trim_start_matches("/mypylike/");
        if path == "__main__" {
            path = "main";
        }
        let line = self.start_position().line_and_column().0;
        let error = match &self.issue.type_ {
            IssueType::AttributeError(object, name) => {
                format!("{object} has no attribute {name:?}")
            }
            IssueType::NameError(name) => {
                format!("Name {name:?} is not defined")
            }
            IssueType::IncompatibleReturn(got, expected) => {
                format!(
                    "Incompatible return value type (got {got:?}, expected {expected:?})",
                )
            }
            IssueType::IncompatibleAssignment(got, expected) => {
                format!(
                    "Incompatible types in assignment (expression has type {got:?}, variable has type {expected:?})",
                )
            }
            IssueType::ArgumentIssue(s) | IssueType::ValidType(s) => s.clone(),
            IssueType::TypeNotFound => {
                let primary = NodeRef::new(self.file, self.issue.node_index);
                format!("Name {:?} is not defined", primary.as_code())
            }
            IssueType::TypeArgumentIssue(class, expected, given) => {
                if *expected == 0 {
                    format!("{class:?} expects no type arguments, but {given} given")
                } else {
                    format!(
                        "{class:?} expects {expected} type arguments, but {given} given",
                    )
                }
            }
            IssueType::TypeAliasArgumentIssue(expected, given) => {
                format!(
                    "Bad number of arguments for type alias, expected: {expected}, given: {given}",
                )
            }
            IssueType::ModuleNotFound(s) => format!(
                "Cannot find implementation or library stub for module named {s:?}\n\
                 {path}:{line}: note: See https://mypy.readthedocs.io/en/stable/running_mypy.html#missing-imports",
            ),
            IssueType::NotCallable(s) => format!("{} not callable", s),
            IssueType::UnsupportedOperand(operand, left, right) => {
                format!(
                    "Unsupported operand types for {operand} ({left:?} and {right:?})",
                )
            }
            IssueType::UnsupportedLeftOperand(operand, left, note) => {
                let mut s = format!(
                    "Unsupported left operand type for {operand} ({left:?})",
                );
                if let Some(note) = note {
                    s += note;
                }
                s
            }
            IssueType::InvalidGetItem(s) => s.clone(),
            IssueType::NotIndexable(s) => format!("Value of type {s:?} is not indexable"),
            IssueType::MethodWithoutArguments => {
                "Method must have at least one argument".to_owned()
            }
            IssueType::OnlyClassTypeApplication => {
                "Type application is only supported for generic classes".to_owned()
            }
            IssueType::TooFewValuesToUnpack(actual, expected) => format!(
                "Need more than {actual} values to unpack ({expected} expected)"
            ),
            IssueType::InvalidBaseClass => {
                let primary = NodeRef::new(self.file, self.issue.node_index);
                format!("Invalid base class {:?}", primary.as_code())
            }
            IssueType::DuplicateTypeVar =>
                "Duplicate type variables in Generic[...] or Protocol[...]".to_owned(),
            IssueType::IncompleteGenericOrProtocolTypeVars =>
                "If Generic[...] or Protocol[...] is present it should list all type variables".to_owned(),
            IssueType::Note(s) => {
                type_ = "note";
                s.clone()
            }
        };
        let string = String::new();
        format!("{path}:{line}: {type_}: {error}")
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
