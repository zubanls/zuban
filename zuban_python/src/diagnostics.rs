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
    StarredExpressionOnlyNoTarget,
    OnlyClassTypeApplication,
    InvalidBaseClass,
    InvalidMetaclass,
    DynamicMetaclassNotSupported { class_name: Box<str> },
    MetaclassMustInheritFromType,
    MetaclassConflict,
    CannotSubclassNewType,
    DuplicateBaseClass { name: Box<str> },
    CyclicDefinition { name: Box<str> },
    EnsureSingleGenericOrProtocol,
    InvalidCallableParams,
    InvalidParamSpecGenerics { got: Box<str> },
    NewTypeMustBeSubclassable { got: Box<str> },
    NewTypeInvalidType,
    OptionalMustHaveOneArgument,

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
    BaseExceptionExpectedForRaise,
    UnsupportedClassScopedImport,

    StmtOutsideFunction { keyword: &'static str },
    TupleIndexOutOfRange,
    NamedTupleExpectsStringLiteralAsFirstArg { name: &'static str },
    StringLiteralExpectedAsNamedTupleItem,
    InvalidStmtInNamedTuple,
    InvalidSecondArgumentToNamedTuple { name: &'static str },
    UnexpectedArgumentsTo { name: &'static str },
    TupleExpectedAsNamedTupleField,
    NamedTupleNamesCannotStartWithUnderscore { name: &'static str, field_names: Box<str> },

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
        use IssueType::*;
        let error = match &self.issue.type_ {
            AttributeError{object, name} => format!("{object} has no attribute {name:?}"),
            ImportAttributeError{module_name, name} => {
                format!("Module {module_name:?} has no attribute {name:?}")
            }
            NameError{name} => format!("Name {name:?} is not defined"),
            IncompatibleReturn{got, expected} => {
                format!("Incompatible return value type (got {got:?}, expected {expected:?})")
            }
            IncompatibleAssignment{got, expected} => {
                format!(
                    "Incompatible types in assignment (expression has type \"{got}\", variable has type \"{expected}\")",
                )
            }
            ListItemMismatch{item, got, expected} => format!(
                "List item {item} has incompatible type \"{got}\"; expected \"{expected}\"",
            ),
            Redefinition{line} => {
                let node_ref = NodeRef::new(self.node_file(), self.issue.node_index);
                format!("Name {:?} already defined line {line}", node_ref.as_code())
            }
            ArgumentIssue(s) | InvalidType(s) => s.clone().into(),
            TooManyArguments(rest) => format!("Too many arguments{rest}"),
            TooFewArguments(rest) => format!("Too few arguments{rest}"),
            IncompatibleDefaultArgument {argument_name, got, expected} => {
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
            TypeNotFound => {
                let primary = NodeRef::new(self.node_file(), self.issue.node_index);
                format!("Name {:?} is not defined", primary.as_code())
            }
            InvalidTypeDeclaration =>
                "Type cannot be declared in assignment to non-self attribute".to_string(),
            UnexpectedTypeDeclaration => "Unexpected type declaration".to_string(),
            OverloadMismatch{name, args, variants} => {
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
            TypeArgumentIssue{class, expected_count, given_count} => {
                match expected_count {
                    0 => format!("{class:?} expects no type arguments, but {given_count} given"),
                    1 => format!("{class:?} expects {expected_count} type argument, but {given_count} given"),
                    _ => format!("{class:?} expects {expected_count} type arguments, but {given_count} given"),
                }
            }
            TypeAliasArgumentIssue{expected_count, given_count} => {
                format!(
                    "Bad number of arguments for type alias, expected: {expected_count}, given: {given_count}",
                )
            }
            ModuleNotFound{module_name} => format!(
                "Cannot find implementation or library stub for module named {module_name:?}",
            ),
            NoParentModule => "No parent module -- cannot perform relative import".to_string(),
            NotCallable{type_} => format!("{type_} not callable"),
            AnyNotCallable => "Any(...) is no longer supported. Use cast(Any, ...) instead".to_string(),
            NotIterable{type_} => format!("{type_} object is not iterable"),
            InvalidCallableArgCount => "Please use \"Callable[[<parameters>], <return type>]\" or \"Callable\"".to_string(),
            UnsupportedOperand{operand, left, right} => {
                format!(
                    "Unsupported operand types for {operand} ({left:?} and {right:?})",
                )
            }
            UnsupportedLeftOperand{operand, left} => format!(
                "Unsupported left operand type for {operand} ({left:?})"
            ),
            UnsupportedIn{right} => format!(
                "Unsupported right operand type for in ({right:?})"
            ),
            UnsupportedOperandForUnary{operand, got} => {
                format!("Unsupported operand type for {operand} ({got:?})")
            }
            InvalidGetItem{actual, type_, expected} => format!(
                "Invalid index type {actual:?} for {type_:?}; expected type {expected:?}",
            ),
            NotIndexable{type_} => format!("Value of type {type_:?} is not indexable"),
            MethodWithoutArguments => {
                "Method must have at least one argument. Did you forget the \"self\" argument?".to_string()
            }
            OnlyClassTypeApplication => {
                "Type application is only supported for generic classes".to_string()
            }
            TooFewValuesToUnpack{actual, expected} => match actual {
                1 => format!("Need more than {actual} value to unpack ({expected} expected)"),
                _ => format!("Need more than {actual} values to unpack ({expected} expected)"),
            },
            StarredExpressionOnlyNoTarget =>
                "Can use starred expression only as assignment target".to_string(),
            InvalidBaseClass => {
                let primary = NodeRef::new(self.node_file(), self.issue.node_index);
                format!("Invalid base class {:?}", primary.as_code())
            }
            InvalidMetaclass => {
                let primary = NodeRef::new(self.node_file(), self.issue.node_index);
                format!("Invalid metaclass {:?}", primary.as_code())
            }
            DynamicMetaclassNotSupported{class_name} => {
                format!("Dynamic metaclass not supported for \"{class_name}\"")
            }
            MetaclassMustInheritFromType =>
                "Metaclasses not inheriting from \"type\" are not supported".to_string(),
            MetaclassConflict =>
                "Metaclass conflict: the metaclass of a derived class must be \
                 a (non-strict) subclass of the metaclasses of all its bases".to_string(),
            CannotSubclassNewType => "Cannot subclass \"NewType\"".to_string(),
            DuplicateBaseClass{name} => {
                let primary = NodeRef::new(self.node_file(), self.issue.node_index);
                format!("Duplicate base class \"{name}\"")
            }
            CyclicDefinition{name} =>
                format!("Cannot resolve name {name:?} (possible cyclic definition)"),
            EnsureSingleGenericOrProtocol =>
                "Only single Generic[...] or Protocol[...] can be in bases".to_string(),
            InvalidCallableParams => format!(
                "The first argument to Callable must be a list of types, parameter specification, or \"...\"\n\
                 {path}:{line}: note: See https://mypy.readthedocs.io/en/stable/kinds_of_types.html#callable-types-and-lambdas"
            ),
            InvalidParamSpecGenerics{got} => format!(
                "Can only replace ParamSpec with a parameter types list or another ParamSpec, got \"{got}\""
            ),
            NewTypeMustBeSubclassable{got} => format!(
                "Argument 2 to NewType(...) must be subclassable (got \"{got}\")"
            ),
            NewTypeInvalidType => "Argument 2 to NewType(...) must be a valid type".to_string(),
            OptionalMustHaveOneArgument => "Optional[...] must have exactly one type argument".to_string(),

            DuplicateTypeVar =>
                "Duplicate type variables in Generic[...] or Protocol[...]".to_string(),
            UnboundTypeVarLike{type_var_like} => match type_var_like {
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
            IncompleteGenericOrProtocolTypeVars =>
                "If Generic[...] or Protocol[...] is present it should list all type variables".to_string(),
            TypeVarExpected{class} => format!("Free type variable expected in {class}[...]"),
            TypeVarBoundViolation{actual, of, expected} => format!(
                "Type argument \"{actual}\" of \"{of}\" must be a subtype of \"{expected}\"",
            ),
            InvalidTypeVarValue{type_var_name, of, actual} =>
                format!("Value of type variable {type_var_name:?} of {of} cannot be {actual:?}"),
            InvalidCastTarget => "Cast target is not a type".to_string(),
            TypeVarCoAndContravariant =>
                "TypeVar cannot be both covariant and contravariant".to_string(),
            TypeVarValuesAndUpperBound =>
                "TypeVar cannot have both values and an upper bound".to_string(),
            TypeVarOnlySingleRestriction =>
                 "TypeVar cannot have only a single constraint".to_string(),
            UnexpectedArgument{class_name, argument_name} => format!(
                 "Unexpected argument to \"{class_name}()\": \"{argument_name}\""),
            TypeVarLikeTooFewArguments{class_name} => format!("Too few arguments for {class_name}()"),
            TypeVarLikeFirstArgMustBeString{class_name} => format!(
                "{class_name}() expects a string literal as first argument"),
            TypeVarVarianceMustBeBool{argument} => format!(
                "TypeVar \"{argument}\" may only be a literal bool"
            ),
            TypeVarTypeExpected => "Type expected".to_string(),
            TypeVarNameMismatch{class_name, string_name, variable_name} => format!(
                "String argument 1 \"{string_name}\" to {class_name}(...) does not \
                 match variable name \"{variable_name}\""
            ),
            TypeVarInReturnButNotArgument =>
                "A function returning TypeVar should receive at least one argument containing the same Typevar".to_string(),
            UnexpectedTypeForTypeVar =>
                "Cannot declare the type of a TypeVar or similar construct".to_string(),
            TypeVarLikeTooManyArguments{class_name} => format!(
                "Only the first argument to {class_name} has defined semantics"),
            MultipleTypeVarTuplesInClassDef =>
                "Can only use one type var tuple in a class def".to_string(),
            BoundTypeVarInAlias{name} =>
                format!("Can't use bound type variable \"{name}\" to define generic alias"),
            NestedConcatenate =>
                "Nested Concatenates are invalid".to_string(),
            InvalidSelfArgument{argument_type, function_name, callable} => format!(
                "Invalid self argument \"{argument_type}\" to attribute function \"{function_name}\" with type \"{callable}\""
            ),
            InvalidClassMethodFirstArgument{argument_type, function_name, callable} => format!(
                "Invalid self argument \"{argument_type}\" to class attribute function \"{function_name}\" with type \"{callable}\""
            ),
            UnexpectedComprehension => "Unexpected comprehension".to_string(),
            AmbigousClassVariableAccess =>
                "Access to generic instance variables via class is ambiguous".to_string(),

            BaseExceptionExpected =>
                "Exception type must be derived from BaseException".to_string(),
            BaseExceptionExpectedForRaise =>
                "Exception must be derived from BaseException".to_string(),
            UnsupportedClassScopedImport =>
                "Unsupported class scoped import".to_string(),
            StmtOutsideFunction{keyword} => format!("{keyword:?} outside function"),
            TupleIndexOutOfRange => "Tuple index out of range".to_string(),
            NamedTupleExpectsStringLiteralAsFirstArg{name} =>
                format!("\"{name}()\" expects a string literal as the first argument"),
            StringLiteralExpectedAsNamedTupleItem =>
                 "String literal expected as \"namedtuple()\" item".to_string(),
            InvalidStmtInNamedTuple =>
                "Invalid statement in NamedTuple definition; expected \"field_name: field_type [= default]\"".to_string(),
            InvalidSecondArgumentToNamedTuple{name} =>
                format!("List or tuple literal expected as the second argument to \"{name}()\""),
            UnexpectedArgumentsTo{name} =>
                format!("Unexpected arguments to \"{name}()\""),
            TupleExpectedAsNamedTupleField => "Tuple expected as \"NamedTuple()\" field".to_string(),
            NamedTupleNamesCannotStartWithUnderscore{name, field_names} => format!(
                "\"{name}()\" field names cannot start with an underscore: {field_names}"),

            OverloadImplementationNotLast =>
                "The implementation for an overloaded function must come last".to_string(),
            OverloadImplementationNeeded =>
                "An overloaded function outside a stub file must have an implementation".to_string(),
            OverloadStubImplementationNotAllowed =>
                "An implementation for an overloaded function is not allowed in a stub file".to_string(),
            OverloadSingleNotAllowed =>
                "Single overload definition, multiple required".to_string(),
            OverloadUnmatchable{unmatchable_signature_index, matchable_signature_index} => format!(
                "Overloaded function signature {unmatchable_signature_index} will never \
                 be matched: signature {matchable_signature_index}'s parameter type(s) \
                 are the same or broader"
            ),
            OverloadIncompatibleReturnTypes{first_signature_index, second_signature_index} => format!(
                "Overloaded function signatures {first_signature_index} and \
                 {second_signature_index} overlap with incompatible return types"
            ),
            OverloadImplementationReturnTypeIncomplete{signature_index} => format!(
                "Overloaded function implementation cannot produce return type of signature {signature_index}"
            ),
            OverloadImplementationArgumentsNotBroadEnough{signature_index} => format!(
                "Overloaded function implementation does not accept all possible arguments of signature {signature_index}"
            ),

            InvariantNote{actual, maybe} => {
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
            Note(s) => {
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
