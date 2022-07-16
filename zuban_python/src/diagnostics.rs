use parsa_python_ast::{CodeIndex, NodeIndex};

use crate::database::{Database, TypeVar};
use crate::file::PythonFile;
use crate::file_state::File;
use crate::name::TreePosition;
use crate::node_ref::NodeRef;

#[derive(Debug)]
#[rustfmt::skip]  // This is way more readable if we are not auto-formatting this.
pub(crate) enum IssueType {
    AttributeError { object: String, name: String },
    ImportAttributeError { module_name: String, name: String },
    NameError { name: String },
    ArgumentIssue(String),
    InvalidType(String),
    IncompatibleReturn { got: String, expected: String },
    IncompatibleAssignment { got: String, expected: String },
    Redefinition { line: usize },
    ModuleNotFound { module_name: String },
    NoParentModule,
    TypeNotFound,
    InvalidTypeDeclaration,
    UnexpectedTypeDeclaration,
    OverloadMismatch { name: String, args: Box<[String]>, variants: Box<[String]> },
    TypeArgumentIssue { class: String, expected_count: usize, given_count: usize },
    TypeAliasArgumentIssue { expected_count: usize, given_count: usize },
    NotCallable { type_: String },
    NotIterable { type_: String },
    InvalidCallableParams,
    InvalidCallableArgCount,
    UnsupportedOperand { operand: String, left: String, right: String },
    UnsupportedLeftOperand { operand: String, left: String, note: Option<String> },
    InvalidGetItem { actual: String, type_: String, expected: String },
    NotIndexable { type_: String },
    TooFewValuesToUnpack { actual: usize, expected: usize },
    OnlyClassTypeApplication,
    InvalidBaseClass,
    CyclicDefinition { name: String },
    EnsureSingleGenericOrProtocol,

    DuplicateTypeVar,
    UnboundTypeVar { type_var: std::rc::Rc<TypeVar> },
    IncompleteGenericOrProtocolTypeVars,
    TypeVarExpected { class: &'static str },
    TypeVarBoundViolation { actual: String, executable: String, expected: String },
    InvalidTypeVarValue { type_var: String, func: String, actual: String },
    TypeVarCoAndContravariant,
    TypeVarValuesAndUpperBound,
    TypeVarOnlySingleRestriction,
    TypeVarUnexpectedArgument { argument_name: String },
    TypeVarTooFewArguments,
    TypeVarFirstArgMustBeString,
    TypeVarVarianceMustBeBool { argument: &'static str },
    TypeVarTypeExpected,
    TypeVarNameMismatch { string_name: String, variable_name: String },

    BaseExceptionExpected,
    UnsupportedClassScopedImport,

    StmtOutsideFunction { keyword: &'static str },

    OverloadImplementationNotLast,
    OverloadImplementationNeeded,

    MethodWithoutArguments,

    Note(String),
}

#[derive(Debug)]
pub struct Issue {
    pub(crate) type_: IssueType,
    pub node_index: NodeIndex,
}

struct SubFileOffset<'db> {
    file: &'db PythonFile,
    offset: CodeIndex,
}

pub struct Diagnostic<'db> {
    db: &'db Database,
    file: &'db PythonFile,
    in_sub_file: Option<SubFileOffset<'db>>,
    pub(crate) issue: &'db Issue,
}

impl<'db> Diagnostic<'db> {
    pub(crate) fn new(db: &'db Database, file: &'db PythonFile, issue: &'db Issue) -> Self {
        Self {
            db,
            file,
            issue,
            in_sub_file: None,
        }
    }

    pub(crate) fn wrap_subfile(self, file: &'db PythonFile, offset: CodeIndex) -> Self {
        Self {
            db: self.db,
            file,
            issue: self.issue,
            in_sub_file: Some(match self.in_sub_file {
                None => SubFileOffset {
                    file: self.file,
                    offset,
                },
                Some(f) => todo!(),
            }),
        }
    }

    fn account_for_sub_file(&self, pos: TreePosition<'db>) -> TreePosition<'db> {
        if let Some(s) = &self.in_sub_file {
            pos.wrap_sub_file(self.file, s.offset)
        } else {
            pos
        }
    }
    fn start_position(&self) -> TreePosition<'db> {
        self.account_for_sub_file(self.node_file().node_start_position(self.issue.node_index))
    }

    fn end_position(&self) -> TreePosition<'db> {
        self.account_for_sub_file(self.node_file().node_end_position(self.issue.node_index))
    }

    fn node_file(&self) -> &'db PythonFile {
        self.in_sub_file
            .as_ref()
            .map(|f| f.file)
            .unwrap_or(self.file)
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
            IssueType::AttributeError{object, name} => {
                format!("{object} has no attribute {name:?}")
            }
            IssueType::ImportAttributeError{module_name, name} => {
                format!("Module {module_name:?} has no attribute {name:?}")
            }
            IssueType::NameError{name} => {
                format!("Name {name:?} is not defined")
            }
            IssueType::IncompatibleReturn{got, expected} => {
                format!(
                    "Incompatible return value type (got {got:?}, expected {expected:?})",
                )
            }
            IssueType::IncompatibleAssignment{got, expected} => {
                format!(
                    "Incompatible types in assignment (expression has type {got:?}, variable has type {expected:?})",
                )
            }
            IssueType::Redefinition{line} => {
                let node_ref = NodeRef::new(self.node_file(), self.issue.node_index);
                format!("Name {:?} already defined line {line}", node_ref.as_code())
            }
            IssueType::ArgumentIssue(s) | IssueType::InvalidType(s) => s.clone(),
            IssueType::TypeNotFound => {
                let primary = NodeRef::new(self.node_file(), self.issue.node_index);
                format!("Name {:?} is not defined", primary.as_code())
            }
            IssueType::InvalidTypeDeclaration =>
                "Type cannot be declared in assignment to non-self attribute".to_owned(),
            IssueType::UnexpectedTypeDeclaration =>
                "Unexpected type declaration".to_owned(),
            IssueType::OverloadMismatch{name, args, variants} => {
                let arg_str = args.join(", ");
                let mut out = match args.len() {
                    0 => format!(
                        "All overload variants of {name} require at least one argument\n"
                    ),
                    1 => format!(
                        "No overload variant of {name} matches argument type \"{arg_str}\"\n",
                    ),
                    _ => format!(
                        "No overload variant of {name} matches argument types \"{arg_str}\"\n",
                    ),
                };
                out += &format!("{path}:{line}: note: Possible overload variants:\n");
                for variant in variants.iter() {
                    out += &format!("{path}:{line}: note:     {variant}\n");
                }
                out.pop(); // Pop the last newline
                out
            }
            IssueType::TypeArgumentIssue{class, expected_count, given_count} => {
                match expected_count {
                    0 => format!("{class:?} expects no type arguments, but {given_count} given"),
                    1 => format!("{class:?} expects {expected_count} type argument, but {given_count} given"),
                    _ => format!("{class:?} expects {expected_count} type arguments, but {given_count} given"),
                }
            }
            IssueType::TypeAliasArgumentIssue{expected_count, given_count} => {
                format!(
                    "Bad number of arguments for type alias, expected: {expected_count}, given: {given_count}",
                )
            }
            IssueType::ModuleNotFound{module_name} => format!(
                "Cannot find implementation or library stub for module named {module_name:?}",
            ),
            IssueType::NoParentModule => "No parent module -- cannot perform relative import".to_owned(),
            IssueType::NotCallable{type_} => format!("{type_} not callable"),
            IssueType::NotIterable{type_} => format!("{type_} object is not iterable"),
            IssueType::InvalidCallableParams => format!(
                "The first argument to Callable must be a list of types, parameter specification, or \"...\"\n\
                 {path}:{line}: note: See https://mypy.readthedocs.io/en/stable/kinds_of_types.html#callable-types-and-lambdas"
            ),
            IssueType::InvalidCallableArgCount => "Please use \"Callable[[<parameters>], <return type>]\" or \"Callable\"".to_owned(),
            IssueType::UnsupportedOperand{operand, left, right} => {
                format!(
                    "Unsupported operand types for {operand} ({left:?} and {right:?})",
                )
            }
            IssueType::UnsupportedLeftOperand{operand, left, note} => {
                let mut s = format!(
                    "Unsupported left operand type for {operand} ({left:?})",
                );
                if let Some(note) = note {
                    s += note;
                }
                s
            }
            IssueType::InvalidGetItem{actual, type_, expected} => format!(
                "Invalid index type {actual:?} for {type_:?}; expected type {expected:?}",
            ),
            IssueType::NotIndexable{type_} => format!("Value of type {type_:?} is not indexable"),
            IssueType::MethodWithoutArguments => {
                "Method must have at least one argument".to_owned()
            }
            IssueType::OnlyClassTypeApplication => {
                "Type application is only supported for generic classes".to_owned()
            }
            IssueType::TooFewValuesToUnpack{actual, expected} => format!(
                "Need more than {actual} values to unpack ({expected} expected)"
            ),
            IssueType::InvalidBaseClass => {
                let primary = NodeRef::new(self.node_file(), self.issue.node_index);
                format!("Invalid base class {:?}", primary.as_code())
            }
            IssueType::CyclicDefinition{name} =>
                format!("Cannot resolve name {name:?} (possible cyclic definition)"),
            IssueType::EnsureSingleGenericOrProtocol =>
                "Only single Generic[...] or Protocol[...] can be in bases".to_owned(),

            IssueType::DuplicateTypeVar =>
                "Duplicate type variables in Generic[...] or Protocol[...]".to_owned(),
            IssueType::UnboundTypeVar{type_var} => {
                let qualified = type_var.qualified_name(self.db);
                let name = type_var.name(self.db);
                format!(
                    "Type variable {qualified:?} is unbound\n\
                     {path}:{line}: note: (Hint: Use \"Generic[{name}]\" or \"Protocol[{name}]\" base class to bind \"{name}\" inside a class)\n\
                     {path}:{line}: note: (Hint: Use \"{name}\" in function signature to bind \"{name}\" inside a function)"
                )
            }
            IssueType::IncompleteGenericOrProtocolTypeVars =>
                "If Generic[...] or Protocol[...] is present it should list all type variables".to_owned(),
            IssueType::TypeVarExpected{class} => format!("Free type variable expected in {class}[...]"),
            IssueType::TypeVarBoundViolation{actual, executable, expected} => format!(
                "Type argument \"{actual}\" of \"{executable}\" must be a subtype of \"{expected}\"",
            ),
            IssueType::InvalidTypeVarValue{type_var, func, actual} =>
                format!("Value of type variable {type_var:?} of {func} cannot be {actual:?}"),
            IssueType::TypeVarCoAndContravariant =>
                "TypeVar cannot be both covariant and contravariant".to_owned(),
            IssueType::TypeVarValuesAndUpperBound =>
                "TypeVar cannot have both values and an upper bound".to_owned(),
            IssueType::TypeVarOnlySingleRestriction =>
                 "TypeVar cannot have only a single constraint".to_owned(),
            IssueType::TypeVarUnexpectedArgument{argument_name} => format!(
                 "Unexpected argument to \"TypeVar()\": \"{argument_name}\""),
            IssueType::TypeVarTooFewArguments => "Too few arguments for TypeVar()".to_owned(),
            IssueType::TypeVarFirstArgMustBeString =>
                "TypeVar() expects a string literal as first argument".to_owned(),
            IssueType::TypeVarVarianceMustBeBool{argument} => format!(
                "TypeVar \"{argument}\" may only be a literal bool"
            ),
            IssueType::TypeVarTypeExpected => "Type expected".to_owned(),
            IssueType::TypeVarNameMismatch{string_name, variable_name} => format!(
                "String argument 1 \"{string_name}\" to TypeVar(...) does not \
                 match variable name \"{variable_name}\""
            ),

            IssueType::BaseExceptionExpected =>
                "Exception type must be derived from BaseException".to_owned(),
            IssueType::UnsupportedClassScopedImport =>
                "Unsupported class scoped import".to_owned(),
            IssueType::StmtOutsideFunction{keyword} => format!("{keyword:?} outside function"),

            IssueType::OverloadImplementationNotLast =>
                "The implementation for an overloaded function must come last".to_owned(),
            IssueType::OverloadImplementationNeeded =>
                "An overloaded function outside a stub file must have an implementation".to_owned(),

            IssueType::Note(s) => {
                type_ = "note";
                s.clone()
            }
        };
        let string = String::new();
        format!("{path}:{line}: {type_}: {error}")
    }
}

impl std::fmt::Debug for Diagnostic<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", &self.as_string())
    }
}

#[derive(Default)]
pub struct DiagnosticConfig {
    pub ignore_missing_imports: bool,
}

impl DiagnosticConfig {
    pub(crate) fn should_be_reported(&self, type_: &IssueType) -> bool {
        match type_ {
            IssueType::ModuleNotFound { .. } => !self.ignore_missing_imports,
            _ => true,
        }
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_sizes() {
        use super::*;
        use std::mem::size_of;
        assert_eq!(size_of::<IssueType>(), 80);
    }
}
