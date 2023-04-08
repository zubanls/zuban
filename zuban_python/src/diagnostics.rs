use parsa_python_ast::{CodeIndex, NodeIndex};

use crate::database::{Database, TypeVarLike};
use crate::file::File;
use crate::file::PythonFile;
use crate::name::TreePosition;
use crate::node_ref::NodeRef;

#[derive(Debug)]
#[rustfmt::skip]  // This is way more readable if we are not auto-formatting this.
pub(crate) enum IssueType {
    AttributeError { object: Box<str>, name: Box<str> },
    ImportAttributeError { module_name: Box<str>, name: Box<str> },
    NameError { name: Box<str> },
    ArgumentIssue(Box<str>),
    TooFewArguments(Box<str>),
    TooManyArguments(Box<str>),
    IncompatibleDefaultArgument{ argument_name: Box<str>, got: Box<str>, expected: Box<str> },
    InvalidType(Box<str>),
    InvalidCastTarget,
    IncompatibleReturn { got: Box<str>, expected: Box<str> },
    IncompatibleAssignment { got: Box<str>, expected: Box<str> },
    ListItemMismatch { item: usize, got: Box<str>, expected: Box<str> },
    Redefinition { line: usize },
    ModuleNotFound { module_name: Box<str> },
    NoParentModule,
    TypeNotFound,
    InvalidTypeDeclaration,
    UnexpectedTypeDeclaration,
    TypeArgumentIssue { class: Box<str>, expected_count: usize, given_count: usize },
    TypeAliasArgumentIssue { expected_count: usize, given_count: usize },
    NotCallable { type_: Box<str> },
    AnyNotCallable,
    NotIterable { type_: Box<str> },
    InvalidCallableArgCount,
    UnsupportedOperand { operand: Box<str>, left: Box<str>, right: Box<str> },
    UnsupportedLeftOperand { operand: Box<str>, left: Box<str> },
    UnsupportedIn { right: Box<str> },
    UnsupportedOperandForUnary { operand: &'static str, got: Box<str>},
    InvalidGetItem { actual: Box<str>, type_: Box<str>, expected: Box<str> },
    NotIndexable { type_: Box<str> },
    TooFewValuesToUnpack { actual: usize, expected: usize },
    OnlyClassTypeApplication,
    InvalidBaseClass,
    InvalidMetaclass,
    DynamicMetaclassNotSupported { class_name: Box<str> },
    CannotSubclassNewType,
    DuplicateBaseClass { name: Box<str> },
    CyclicDefinition { name: Box<str> },
    EnsureSingleGenericOrProtocol,
    InvalidCallableParams,
    InvalidParamSpecGenerics { got: Box<str> },
    NewTypeMustBeSubclassable { got: Box<str> },
    NewTypeInvalidType,

    DuplicateTypeVar,
    UnboundTypeVarLike { type_var_like: TypeVarLike },
    IncompleteGenericOrProtocolTypeVars,
    TypeVarExpected { class: &'static str },
    TypeVarBoundViolation { actual: Box<str>, of: Box<str>, expected: Box<str> },
    InvalidTypeVarValue { type_var_name: Box<str>, of: Box<str>, actual: Box<str> },
    TypeVarCoAndContravariant,
    TypeVarValuesAndUpperBound,
    TypeVarOnlySingleRestriction,
    UnexpectedArgument { class_name: &'static str, argument_name: Box<str> },
    TypeVarLikeTooFewArguments { class_name: &'static str },
    TypeVarLikeFirstArgMustBeString{ class_name: &'static str },
    TypeVarVarianceMustBeBool { argument: &'static str },
    TypeVarTypeExpected,
    TypeVarNameMismatch {
        class_name: &'static str,
        string_name: Box<str>,
        variable_name: Box<str>
    },
    TypeVarInReturnButNotArgument,
    UnexpectedTypeForTypeVar,
    TypeVarLikeTooManyArguments { class_name: &'static str },
    MultipleTypeVarTuplesInClassDef,
    BoundTypeVarInAlias { name: Box<str> },
    NestedConcatenate,
    InvalidSelfArgument { argument_type: Box<str>, function_name: Box<str>, callable: Box<str> },
    InvalidClassMethodFirstArgument { argument_type: Box<str>, function_name: Box<str>, callable: Box<str> },
    UnexpectedComprehension,
    AmbigousClassVariableAccess,

    BaseExceptionExpected,
    UnsupportedClassScopedImport,

    StmtOutsideFunction { keyword: &'static str },

    OverloadMismatch { name: Box<str>, args: Box<[Box<str>]>, variants: Box<[Box<str>]> },
    OverloadImplementationNotLast,
    OverloadImplementationNeeded,
    OverloadStubImplementationNotAllowed,
    OverloadSingleNotAllowed,
    OverloadUnmatchable { unmatchable_signature_index: usize, matchable_signature_index: usize },
    OverloadIncompatibleReturnTypes { first_signature_index: usize, second_signature_index: usize },
    OverloadImplementationReturnTypeIncomplete { signature_index: usize },
    OverloadImplementationArgumentsNotBroadEnough { signature_index: usize },

    MethodWithoutArguments,

    InvariantNote { actual: &'static str, maybe: &'static str },
    Note(Box<str>),
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
                    "Incompatible types in assignment (expression has type \"{got}\", variable has type \"{expected}\")",
                )
            }
            IssueType::ListItemMismatch{item, got, expected} => format!(
                "List item {item} has incompatible type \"{got}\"; expected \"{expected}\"",
            ),
            IssueType::Redefinition{line} => {
                let node_ref = NodeRef::new(self.node_file(), self.issue.node_index);
                format!("Name {:?} already defined line {line}", node_ref.as_code())
            }
            IssueType::ArgumentIssue(s) | IssueType::InvalidType(s) => s.clone().into(),
            IssueType::TooManyArguments(rest) => format!("Too many arguments{rest}"),
            IssueType::TooFewArguments(rest) => format!("Too few arguments{rest}"),
            IssueType::IncompatibleDefaultArgument {argument_name, got, expected} => {
                let mut out = format!(
                    "Incompatible default for argument \"{argument_name}\" \
                     (default has type \"{got}\", argument has type \"{expected}\")"
                );
                if got.as_ref() == "None" {
                    out += &format!("\n{path}:{line}: note: PEP 484 prohibits implicit Optional. Accordingly, mypy has changed its default to no_implicit_optional=True");
                    out += &format!("\n{path}:{line}: note: Use https://github.com/hauntsaninja/no_implicit_optional to automatically upgrade your codebase");
                }
                out
            },
            IssueType::TypeNotFound => {
                let primary = NodeRef::new(self.node_file(), self.issue.node_index);
                format!("Name {:?} is not defined", primary.as_code())
            }
            IssueType::InvalidTypeDeclaration =>
                "Type cannot be declared in assignment to non-self attribute".to_owned(),
            IssueType::UnexpectedTypeDeclaration =>
                "Unexpected type declaration".to_owned(),
            IssueType::OverloadMismatch{name, args, variants} => {
                let arg_str = args.join("\", \"");
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
            IssueType::AnyNotCallable => "Any(...) is no longer supported. Use cast(Any, ...) instead".to_owned(),
            IssueType::NotIterable{type_} => format!("{type_} object is not iterable"),
            IssueType::InvalidCallableArgCount => "Please use \"Callable[[<parameters>], <return type>]\" or \"Callable\"".to_owned(),
            IssueType::UnsupportedOperand{operand, left, right} => {
                format!(
                    "Unsupported operand types for {operand} ({left:?} and {right:?})",
                )
            }
            IssueType::UnsupportedLeftOperand{operand, left} => format!(
                "Unsupported left operand type for {operand} ({left:?})"
            ),
            IssueType::UnsupportedIn{right} => format!(
                "Unsupported right operand type for in ({right:?})"
            ),
            IssueType::UnsupportedOperandForUnary{operand, got} => {
                format!("Unsupported operand type for {operand} ({got:?})")
            }
            IssueType::InvalidGetItem{actual, type_, expected} => format!(
                "Invalid index type {actual:?} for {type_:?}; expected type {expected:?}",
            ),
            IssueType::NotIndexable{type_} => format!("Value of type {type_:?} is not indexable"),
            IssueType::MethodWithoutArguments => {
                "Method must have at least one argument. Did you forget the \"self\" argument?".to_owned()
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
            IssueType::InvalidMetaclass => {
                let primary = NodeRef::new(self.node_file(), self.issue.node_index);
                format!("Invalid metaclass {:?}", primary.as_code())
            }
            IssueType::DynamicMetaclassNotSupported{class_name} => {
                format!("Dynamic metaclass not supported for \"{class_name}\"")
            }
            IssueType::CannotSubclassNewType => "Cannot subclass \"NewType\"".to_owned(),
            IssueType::DuplicateBaseClass{name} => {
                let primary = NodeRef::new(self.node_file(), self.issue.node_index);
                format!("Duplicate base class \"{name}\"")
            }
            IssueType::CyclicDefinition{name} =>
                format!("Cannot resolve name {name:?} (possible cyclic definition)"),
            IssueType::EnsureSingleGenericOrProtocol =>
                "Only single Generic[...] or Protocol[...] can be in bases".to_owned(),
            IssueType::InvalidCallableParams => format!(
                "The first argument to Callable must be a list of types, parameter specification, or \"...\"\n\
                 {path}:{line}: note: See https://mypy.readthedocs.io/en/stable/kinds_of_types.html#callable-types-and-lambdas"
            ),
            IssueType::InvalidParamSpecGenerics{got} => format!(
                "Can only replace ParamSpec with a parameter types list or another ParamSpec, got \"{got}\""
            ),
            IssueType::NewTypeMustBeSubclassable{got} => format!(
                "Argument 2 to NewType(...) must be subclassable (got \"{got}\")"
            ),
            IssueType::NewTypeInvalidType => "Argument 2 to NewType(...) must be a valid type".to_string(),

            IssueType::DuplicateTypeVar =>
                "Duplicate type variables in Generic[...] or Protocol[...]".to_owned(),
            IssueType::UnboundTypeVarLike{type_var_like} => match type_var_like {
                TypeVarLike::TypeVar(type_var) => {
                    let qualified = type_var.qualified_name(self.db);
                    let name = type_var.name(self.db);
                    format!(
                        "Type variable {qualified:?} is unbound\n\
                         {path}:{line}: note: (Hint: Use \"Generic[{name}]\" or \"Protocol[{name}]\" base class to bind \"{name}\" inside a class)\n\
                         {path}:{line}: note: (Hint: Use \"{name}\" in function signature to bind \"{name}\" inside a function)"
                    )
                }
                TypeVarLike::TypeVarTuple(type_var_tuple) => {
                    let name = type_var_tuple.name(self.db);
                    format!("TypeVarTuple {name:?} is unbound")
                }
                TypeVarLike::ParamSpec(param_spec) => {
                    let name = param_spec.name(self.db);
                    format!("ParamSpec {name:?} is unbound")
                }
            }
            IssueType::IncompleteGenericOrProtocolTypeVars =>
                "If Generic[...] or Protocol[...] is present it should list all type variables".to_owned(),
            IssueType::TypeVarExpected{class} => format!("Free type variable expected in {class}[...]"),
            IssueType::TypeVarBoundViolation{actual, of, expected} => format!(
                "Type argument \"{actual}\" of \"{of}\" must be a subtype of \"{expected}\"",
            ),
            IssueType::InvalidTypeVarValue{type_var_name, of, actual} =>
                format!("Value of type variable {type_var_name:?} of {of} cannot be {actual:?}"),
            IssueType::InvalidCastTarget => "Cast target is not a type".to_owned(),
            IssueType::TypeVarCoAndContravariant =>
                "TypeVar cannot be both covariant and contravariant".to_owned(),
            IssueType::TypeVarValuesAndUpperBound =>
                "TypeVar cannot have both values and an upper bound".to_owned(),
            IssueType::TypeVarOnlySingleRestriction =>
                 "TypeVar cannot have only a single constraint".to_owned(),
            IssueType::UnexpectedArgument{class_name, argument_name} => format!(
                 "Unexpected argument to \"{class_name}()\": \"{argument_name}\""),
            IssueType::TypeVarLikeTooFewArguments{class_name} => format!("Too few arguments for {class_name}()"),
            IssueType::TypeVarLikeFirstArgMustBeString{class_name} => format!(
                "{class_name}() expects a string literal as first argument"),
            IssueType::TypeVarVarianceMustBeBool{argument} => format!(
                "TypeVar \"{argument}\" may only be a literal bool"
            ),
            IssueType::TypeVarTypeExpected => "Type expected".to_owned(),
            IssueType::TypeVarNameMismatch{class_name, string_name, variable_name} => format!(
                "String argument 1 \"{string_name}\" to {class_name}(...) does not \
                 match variable name \"{variable_name}\""
            ),
            IssueType::TypeVarInReturnButNotArgument =>
                "A function returning TypeVar should receive at least one argument containing the same Typevar".to_owned(),
            IssueType::UnexpectedTypeForTypeVar =>
                "Cannot declare the type of a TypeVar or similar construct".to_owned(),
            IssueType::TypeVarLikeTooManyArguments{class_name} => format!(
                "Only the first argument to {class_name} has defined semantics"),
            IssueType::MultipleTypeVarTuplesInClassDef =>
                "Can only use one type var tuple in a class def".to_owned(),
            IssueType::BoundTypeVarInAlias{name} =>
                format!("Can't use bound type variable \"{name}\" to define generic alias"),
            IssueType::NestedConcatenate =>
                "Nested Concatenates are invalid".to_owned(),
            IssueType::InvalidSelfArgument{argument_type, function_name, callable} => format!(
                "Invalid self argument \"{argument_type}\" to attribute function \"{function_name}\" with type \"{callable}\""
            ),
            IssueType::InvalidClassMethodFirstArgument{argument_type, function_name, callable} => format!(
                "Invalid self argument \"{argument_type}\" to class attribute function \"{function_name}\" with type \"{callable}\""
            ),
            IssueType::UnexpectedComprehension => "Unexpected comprehension".to_owned(),
            IssueType::AmbigousClassVariableAccess =>
                "Access to generic instance variables via class is ambiguous".to_owned(),

            IssueType::BaseExceptionExpected =>
                "Exception type must be derived from BaseException".to_owned(),
            IssueType::UnsupportedClassScopedImport =>
                "Unsupported class scoped import".to_owned(),
            IssueType::StmtOutsideFunction{keyword} => format!("{keyword:?} outside function"),

            IssueType::OverloadImplementationNotLast =>
                "The implementation for an overloaded function must come last".to_owned(),
            IssueType::OverloadImplementationNeeded =>
                "An overloaded function outside a stub file must have an implementation".to_owned(),
            IssueType::OverloadStubImplementationNotAllowed =>
                "An implementation for an overloaded function is not allowed in a stub file".to_owned(),
            IssueType::OverloadSingleNotAllowed =>
                "Single overload definition, multiple required".to_owned(),
            IssueType::OverloadUnmatchable{unmatchable_signature_index, matchable_signature_index} => format!(
                "Overloaded function signature {unmatchable_signature_index} will never \
                 be matched: signature {matchable_signature_index}'s parameter type(s) \
                 are the same or broader"
            ),
            IssueType::OverloadIncompatibleReturnTypes{first_signature_index, second_signature_index} => format!(
                "Overloaded function signatures {first_signature_index} and \
                 {second_signature_index} overlap with incompatible return types"
            ),
            IssueType::OverloadImplementationReturnTypeIncomplete{signature_index} => format!(
                "Overloaded function implementation cannot produce return type of signature {signature_index}"
            ),
            IssueType::OverloadImplementationArgumentsNotBroadEnough{signature_index} => format!(
                "Overloaded function implementation does not accept all possible arguments of signature {signature_index}"
            ),

            IssueType::InvariantNote{actual, maybe} => {
                type_ = "note";
                let suffix = match *actual {
                    "List" => "",
                    "Dict" => " in the value type",
                    _ => unreachable!(),
                };
                format!(
                    "\"{actual}\" is invariant -- see https://mypy.readthedocs.io/en/stable/common_issues.html#variance\n\
                    {path}:{line}: note: Consider using \"{maybe}\" instead, which is covariant{suffix}"
                )
            }
            IssueType::Note(s) => {
                type_ = "note";
                s.clone().into()
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
        assert_eq!(size_of::<IssueType>(), 56);
    }
}
