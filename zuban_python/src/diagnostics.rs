use parsa_python_ast::{CodeIndex, NodeIndex, Tree};

use crate::database::Database;
use crate::file::File;
use crate::file::PythonFile;
use crate::name::TreePosition;
use crate::type_::{FunctionKind, StringSlice, TypeVarLike};
use crate::utils::{join_with_commas, InsertOnlyVec};

#[derive(Debug)]
#[allow(dead_code)]  // TODO remove this
#[rustfmt::skip]  // This is way more readable if we are not auto-formatting this.
pub(crate) enum IssueType {
    InvalidSyntax,
    InvalidSyntaxInTypeComment { type_comment: Box<str> },
    InvalidSyntaxInTypeAnnotation,

    AttributeError { object: Box<str>, name: Box<str> },
    UnionAttributeError { object: Box<str>, union: Box<str>, name: Box<str> },
    UnionAttributeErrorOfUpperBound(Box<str>),
    // Mypy somehow has a different error here than the one for imports.
    ImportAttributeError { module_name: Box<str>, name: Box<str> },
    ModuleAttributeError { name: Box<str> },
    UnsupportedClassScopedImport,
    NameError { name: Box<str> },
    ArgumentIssue(Box<str>),
    ArgumentTypeIssue(Box<str>),
    TooFewArguments(Box<str>),
    TooManyArguments(Box<str>),
    IncompatibleDefaultArgument{ argument_name: Box<str>, got: Box<str>, expected: Box<str> },
    InvalidCastTarget,
    IncompatibleReturn { got: Box<str>, expected: Box<str> },
    IncompatibleTypes { cause: &'static str, got: Box<str>, expected: Box<str> },
    DoesNotReturnAValue(Box<str>),
    InvalidGeneratorReturnType,
    InvalidAsyncGeneratorReturnType,
    YieldFromCannotBeApplied { to: Box<str> },
    YieldValueExpected,
    IncompatibleAssignment { got: Box<str>, expected: Box<str> },
    CannotAssignToClassVarViaInstance { name: Box<str> },
    ListItemMismatch { item: usize, got: Box<str>, expected: Box<str> },
    ListComprehensionMismatch { got: Box<str>, expected: Box<str> },
    SetComprehensionMismatch { got: Box<str>, expected: Box<str> },
    GeneratorComprehensionMismatch { got: Box<str>, expected: Box<str> },
    DictComprehensionMismatch { part: &'static str, got: Box<str>, expected: Box<str> },
    DictMemberMismatch { item: usize, got_pair: Box<str>, expected_pair: Box<str> },
    UnpackedDictMemberMismatch { item: usize, got: Box<str>, expected: Box<str> },
    CannotInferLambdaParams,

    Redefinition { line: usize },
    ModuleNotFound { module_name: Box<str> },
    NoParentModule,
    TypeNotFound,
    UnexpectedTypeDeclaration,
    TypeArgumentIssue { class: Box<str>, expected_count: usize, given_count: usize },
    TypeAliasArgumentIssue { expected_count: usize, given_count: usize },
    NotCallable { type_: Box<str> },
    UnknownFunctionNotCallable,
    AnyNotCallable,
    NotIterable { type_: Box<str> },
    AsyncNotIterable { type_: Box<str> },
    InvalidCallableArgCount,
    UnsupportedOperand { operand: Box<str>, left: Box<str>, right: Box<str> },
    UnsupportedLeftOperand { operand: Box<str>, left: Box<str> },
    UnsupportedIn { right: Box<str> },
    UnsupportedOperandForUnary { operand: &'static str, got: Box<str>},
    InvalidGetItem { actual: Box<str>, type_: Box<str>, expected: Box<str> },
    UnsupportedSetItemTarget(Box<str>),
    InvalidSetItemTarget { got: Box<str>, expected: Box<str> },
    NotIndexable { type_: Box<str> },
    InvalidSliceIndex,
    TooFewValuesToUnpack { actual: usize, expected: usize },
    TooManyValuesToUnpack { actual: usize, expected: usize},
    UnpackingAStringIsDisallowed,
    StarredExpressionOnlyNoTarget,
    StmtOutsideFunction { keyword: &'static str },
    YieldOrYieldFromInsideComprehension { keyword: &'static str },
    AwaitOutsideFunction,
    AwaitOutsideCoroutine,
    YieldFromInAsyncFunction,
    ReturnInAsyncGenerator,
    OnlyClassTypeApplication,
    InvalidBaseClass,
    IncompatibleBaseTuples,
    InvalidMetaclass,
    MetaclassMustInheritFromType,
    MetaclassConflict,
    CannotSubclassNewType,
    DuplicateBaseClass { name: Box<str> },
    InconsistentMro { name: Box<str> },
    CyclicDefinition { name: Box<str> },
    EnsureSingleGenericOrProtocol,

    InvalidType(Box<str>),
    InvalidTypeDeclaration,
    ClassVarOnlyInAssignmentsInClass,
    ClassVarNestedInsideOtherType,
    ClassVarTooManyArguments,
    ClassVarCannotContainTypeVariables,
    ClassVarCannotContainSelfTypeInGenericClass,
    InvalidCallableParams,
    InvalidParamSpecGenerics { got: Box<str> },
    NewTypeInvalidType,
    NewTypeMustBeSubclassable { got: Box<str> },
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
    TypeVarCovariantInParamType,
    TypeVarContravariantInReturnType,
    TypeVarVarianceIncompatibleWithParentType { type_var_name: Box<str> },
    UnexpectedTypeForTypeVar,
    TypeVarTupleTooManyArguments,
    ParamSpecTooManyKeywordArguments,
    ParamSpecNestedSpecificationsNotAllowed,
    MultipleTypeVarTuplesInClassDef,
    BoundTypeVarInAlias { name: Box<str> },
    NestedConcatenate,
    ConcatenateLastParamNeedsToBeParamSpec,
    InvalidSelfArgument { argument_type: Box<str>, function_name: Box<str>, callable: Box<str> },
    SelfTypeInMetaclass,
    SelfTypeInTypeAliasTarget,
    InvalidClassMethodFirstArgument { argument_type: Box<str>, function_name: Box<str>, callable: Box<str> },
    InvalidClassmethodAndStaticmethod,
    UsedWithANonMethod { name: &'static str },
    UnexpectedComprehension,
    AmbigousClassVariableAccess,
    CannotInstantiateProtocol { name: Box<str> },

    InvalidAssertType { actual: Box<str>, wanted: Box<str> },

    SuperUsedOutsideClass,
    SuperWithSingleArgumentNotSupported,
    SuperVarargsNotSupported,
    SuperOnlyAcceptsPositionalArguments,
    SuperArgument1MustBeTypeObject,
    SuperArgument2MustBeAnInstanceOfArgument1,
    SuperUnsupportedArgument{argument_index: usize},
    SuperTargetClassHasNoBaseClass,
    UndefinedInSuperclass { name: Box<str> },

    IncompatibleAssignmentInSubclass { base_class: Box<str>, got: Box<str>, expected: Box<str> },
    SignatureIncompatibleWithSupertype { base_class: Box<str>, name: Box<str>, notes: Box<[Box<str>]> },
    MultipleInheritanceIncompatibility { name: Box<str>, class1: Box<str>, class2: Box<str> },
    NewMustReturnAnInstance { got: Box<str> },
    NewIncompatibleReturnType { returns: Box<str>, must_return: Box<str> },

    BaseExceptionExpected,
    BaseExceptionExpectedForRaise,
    ExceptStarIsNotAllowedToBeAnExceptionGroup,

    TupleIndexOutOfRange,
    NamedTupleExpectsStringLiteralAsFirstArg { name: &'static str },
    StringLiteralExpectedAsNamedTupleItem,
    InvalidStmtInNamedTuple,
    NamedTupleNonDefaultFieldFollowsDefault,
    InvalidSecondArgumentToNamedTuple { name: &'static str },
    UnexpectedArgumentsTo { name: &'static str },
    UnexpectedArgumentTo { name: &'static str },
    TupleExpectedAsNamedTupleField,
    NamedTupleNamesCannotStartWithUnderscore { name: &'static str, field_names: Box<str> },
    NamedTupleNameCannotStartWithUnderscore { field_name: Box<str> },
    NamedTupleInvalidFieldName,
    NamedTupleFirstArgumentMismatch { should: Box<str>, is: Box<str> },
    NamedTupleDefaultsShouldBeListOrTuple,
    NamedTupleToManyDefaults,

    TypedDictIncompatibleType { got: Box<str>, key: Box<str>, expected: Box<str> },
    TypedDictExtraKey { key: Box<str>, typed_dict: Box<str> },
    UnexpectedArgumentsToTypedDict,
    TypedDictFirstArgMustBeString,
    TypedDictSecondArgMustBeDict,
    TypedDictInvalidFieldName,
    TypedDictSelfNotAllowed,
    TypedDictNameMismatch { string_name: Box<str>, variable_name: Box<str> },
    TypedDictTotalMustBeTrueOrFalse,
    TypedDictWrongArgumentsInConstructor,
    TypedDictKeysMustBeStringLiteral,
    TypedDictAccessKeyMustBeStringLiteral { keys: Box<str> },
    TypedDictKeySetItemIncompatibleType { key: Box<str>, got: Box<str>, expected: Box<str> },
    TypedDictHasNoKey { typed_dict: Box<str>, key: Box<str> },
    TypedDictHasNoKeyForGet { typed_dict: Box<str>, key: Box<str> },
    TypedDictKeyCannotBeDeleted { typed_dict: Box<str>, key: Box<str> },
    TypedDictInvalidMember,
    TypedDictInvalidMemberRightSide,
    TypedDictBasesMustBeTypedKeys,
    TypedDictDuplicateKey { key: Box<str> },
    TypedDictOverwritingKeyWhileExtending { key: Box<str> },
    TypedDictOverwritingKeyWhileMerging { key: Box<str> },
    TypedDictMissingKeys { typed_dict: Box<str>, keys: Box<[Box<str>]> },
    TypedDictNonRequired { key: Box<str> },
    TypedDictUnsupportedTypeInStarStar { type_: Box<str> },

    OverloadMismatch { name: Box<str>, args: Box<[Box<str>]>, variants: Box<[Box<str>]> },
    OverloadImplementationNotLast,
    OverloadImplementationNeeded,
    OverloadStubImplementationNotAllowed,
    OverloadSingleNotAllowed,
    OverloadUnmatchable { unmatchable_signature_index: usize, matchable_signature_index: usize },
    OverloadIncompatibleReturnTypes { first_signature_index: usize, second_signature_index: usize },
    OverloadImplementationReturnTypeIncomplete { signature_index: usize },
    OverloadImplementationArgumentsNotBroadEnough { signature_index: usize },
    OverloadInconsistentKind { kind: FunctionKind },
    OverloadedPropertyNotSupported,

    DecoratorOnTopOfPropertyNotSupported,
    OnlySupportedTopDecoratorSetter { name: Box<str> },
    UnexpectedDefinitionForProperty { name: Box<str> },
    PropertyIsReadOnly { class_name: Box<str>, property_name: Box<str> },

    MethodWithoutArguments,
    MultipleStarredExpressionsInAssignment,

    EnumFirstArgMustBeString,
    EnumInvalidSecondArgument,
    EnumNeedsAtLeastOneItem { name: Box<str> },
    EnumWithTupleOrListExpectsStringPairs { name: Box<str> },
    EnumWithDictRequiresStringLiterals { name: Box<str> },
    EnumUnexpectedArguments { name: Box<str> },
    EnumAttemptedReuseOfMemberName { member_name: Box<str>, enum_name: Box<str> },
    EnumIndexShouldBeAString { actual: Box<str> },
    EnumCannotBeGeneric,
    EnumReusedMemberName { enum_name: Box<str>, member_name: Box<str> },
    EnumWithMembersNotExtendable  { name: Box<str> },
    EnumMultipleMixinNew { extra: Box<str> },
    EnumMixinNotAllowedAfterEnum { after: Box<str> },
    EnumMembersAttributeOverwritten,

    DataclassMultipleKwOnly,
    DataclassNoDefaultAfterDefault,
    DataclassOrderEnabledButNotEq,
    DataclassCustomOrderMethodNotAllowed { method_name: &'static str },
    DataclassCannotInheritNonFrozenFromFrozen,
    DataclassCannotInheritFrozenFromNonFrozen,
    DataclassReplaceExpectedDataclass { got: Box<str> },
    DataclassReplaceExpectedDataclassInTypeVarBound { got: Box<str> },

    // From --disallow-untyped-defs
    FunctionIsDynamic,
    FunctionMissingReturnAnnotation,
    FunctionMissingParamAnnotations,
    // From --disallow-untyped-calls
    CallToUntypedFunction { name: Box<str> },

    InvariantNote { actual: &'static str, maybe: &'static str },
    AnnotationInUntypedFunction,
    Note(Box<str>),
}

impl IssueType {
    pub fn mypy_error_code(&self) -> Option<&'static str> {
        use IssueType::*;
        Some(match &self {
            Note(_) | InvariantNote { .. } => return None,
            InvalidSyntax | InvalidSyntaxInTypeComment { .. } | InvalidSyntaxInTypeAnnotation => {
                "syntax"
            }
            AttributeError { .. }
            | ImportAttributeError { .. }
            | ModuleAttributeError { .. }
            | AsyncNotIterable { .. }
            | NotIterable { .. } => "attr-defined",
            NameError { .. } => "name-defined",
            UnionAttributeError { .. } | UnionAttributeErrorOfUpperBound(..) => "union-attr",
            ArgumentTypeIssue(s) => "arg-type",
            ArgumentIssue { .. } | TooManyArguments { .. } => "call-arg",
            TooFewArguments { .. } => "call-arg",
            InvalidType(_) => "valid-type",
            IncompatibleReturn { .. } => "return-value",
            IncompatibleDefaultArgument { .. }
            | IncompatibleAssignment { .. }
            | InvalidSetItemTarget { .. } => "assignment",
            InvalidGetItem { .. } | NotIndexable { .. } | UnsupportedSetItemTarget(_) => "index",
            TypeVarInReturnButNotArgument
            | TypeVarCovariantInParamType
            | TypeVarContravariantInReturnType
            | TypeVarVarianceIncompatibleWithParentType { .. }
            | InvalidTypeVarValue { .. }
            | TypeVarBoundViolation { .. } => "type-var",
            UnsupportedOperand { .. }
            | UnsupportedLeftOperand { .. }
            | UnsupportedIn { .. }
            | UnsupportedOperandForUnary { .. }
            | NotCallable { .. }
            | UnknownFunctionNotCallable => "operator",
            TypeArgumentIssue { .. } => "type-arg",
            ModuleNotFound { .. } => "import",
            ListItemMismatch { .. } => "list-item",
            DictMemberMismatch { .. } | UnpackedDictMemberMismatch { .. } => "dict-item",
            NewTypeMustBeSubclassable { .. } => "valid-newtype",
            OverloadImplementationNeeded { .. } => "no-overload-impl",
            OverloadMismatch { .. } => "call-overload",
            IncompatibleAssignmentInSubclass { .. } | SignatureIncompatibleWithSupertype { .. } => {
                "override"
            }
            FunctionIsDynamic
            | FunctionMissingReturnAnnotation
            | FunctionMissingParamAnnotations => "no-untyped-def",
            DoesNotReturnAValue(_) => "func-returns-value",
            CallToUntypedFunction { .. } => "no-untyped-call",
            AnnotationInUntypedFunction => "annotation-unchecked",
            AwaitOutsideFunction => "top-level-await",
            AwaitOutsideCoroutine => "await-not-async",

            TypedDictNameMismatch { .. } | NamedTupleFirstArgumentMismatch { .. } => "name-match",
            TypedDictMissingKeys { .. }
            | TypedDictIncompatibleType { .. }
            | TypedDictKeySetItemIncompatibleType { .. }
            | TypedDictHasNoKeyForGet { .. } => "typeddict-item",
            TypedDictExtraKey { .. } | TypedDictHasNoKey { .. } => "typeddict-unknown-key",
            _ => "misc",
        })
    }

    fn mypy_error_supercode(&self) -> Option<&'static str> {
        // See also https://mypy.readthedocs.io/en/stable/error_codes.html#subcodes-of-error-codes
        use IssueType::*;
        match &self {
            TypedDictExtraKey { .. } | TypedDictHasNoKey { .. } => Some("typeddict-item"),
            _ => None,
        }
    }
}

#[derive(Debug)]
pub struct Issue {
    pub(crate) type_: IssueType,
    pub start_position: CodeIndex,
    pub end_position: CodeIndex,
}

impl Issue {
    pub(crate) fn from_node_index(tree: &Tree, node_index: NodeIndex, type_: IssueType) -> Self {
        Self {
            type_,
            start_position: tree.node_start_position(node_index),
            end_position: tree.node_end_position(node_index),
        }
    }

    pub(crate) fn from_string_slice(s: StringSlice, type_: IssueType) -> Self {
        Self {
            type_,
            start_position: s.start,
            end_position: s.end,
        }
    }
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
        self.account_for_sub_file(TreePosition::new(
            self.node_file(),
            self.issue.start_position,
        ))
    }

    #[allow(dead_code)] // TODO remove this
    fn end_position(&self) -> TreePosition<'db> {
        self.account_for_sub_file(TreePosition::new(self.node_file(), self.issue.end_position))
    }

    fn code_under_issue(&self) -> &'db str {
        &self.file.tree.code()[self.start_position().byte_position() as usize
            ..self.end_position().byte_position() as usize]
    }

    fn node_file(&self) -> &'db PythonFile {
        self.in_sub_file
            .as_ref()
            .map(|f| f.file)
            .unwrap_or(self.file)
    }

    pub fn mypy_error_code(&self) -> &'static str {
        self.issue.type_.mypy_error_code().unwrap_or("note")
    }

    pub fn as_string(&self, config: &DiagnosticConfig) -> String {
        let mut type_ = "error";
        // TODO REMOVE mypy removal
        let mut path = self
            .db
            .file_path(self.file.file_index())
            .trim_start_matches("/mypylike/");
        if path == "__main__" {
            path = "main";
        }
        let line_column = self.start_position().line_and_column();
        let line = line_column.0;
        let mut additional_notes = vec![];
        use IssueType::*;
        let error = match &self.issue.type_ {
            InvalidSyntax => "invalid syntax".to_string(),
            InvalidSyntaxInTypeComment { type_comment } => format!(
                r#"Syntax error in type comment "{type_comment}""#
            ),
            InvalidSyntaxInTypeAnnotation => "Syntax error in type annotation".to_string(),

            AttributeError{object, name} => format!("{object} has no attribute {name:?}"),
            UnionAttributeError{object, union, name} => format!("Item {object} of \"{union}\" has no attribute {name:?}"),
            UnionAttributeErrorOfUpperBound(s) => s.to_string(),
            ImportAttributeError{module_name, name} => {
                format!("Module {module_name:?} has no attribute {name:?}")
            }
            ModuleAttributeError{name} => {
                format!("Module has no attribute {name:?}")
            }
            UnsupportedClassScopedImport =>
                "Unsupported class scoped import".to_string(),
            NameError{name} => format!("Name {name:?} is not defined"),
            IncompatibleReturn{got, expected} => {
                format!("Incompatible return value type (got {got:?}, expected {expected:?})")
            }
            IncompatibleTypes{cause, got, expected} => {
                format!(r#"Incompatible types in {cause} (actual type "{got}", expected type "{expected}")"#)
            }
            DoesNotReturnAValue(named) => format!("{named} does not return a value (it only ever returns None)"),
            InvalidGeneratorReturnType =>
                r#"The return type of a generator function should be "Generator" or one of its supertypes"#.to_string(),
            InvalidAsyncGeneratorReturnType =>
                r#"The return type of an async generator function should be "AsyncGenerator" or one of its supertypes"#.to_string(),
            YieldFromCannotBeApplied { to } => format!(r#""yield from" can't be applied to "{to}""#),
            YieldValueExpected => "Yield value expected".to_string(),
            IncompatibleAssignment{got, expected} => {
                format!(
                    "Incompatible types in assignment (expression has type \"{got}\", variable has type \"{expected}\")",
                )
            }
            CannotAssignToClassVarViaInstance { name } => format!(
                "Cannot assign to class variable \"{name}\" via instance"
            ),
            ListItemMismatch{item, got, expected} => format!(
                "List item {item} has incompatible type \"{got}\"; expected \"{expected}\"",
            ),
            ListComprehensionMismatch{got, expected} => format!(
                "List comprehension has incompatible type List[{got}]; expected List[{expected}]",
            ),
            SetComprehensionMismatch{got, expected} => format!(
                "Set comprehension has incompatible type Set[{got}]; expected Set[{expected}]",
            ),
            GeneratorComprehensionMismatch{got, expected} => format!(
                "Generator has incompatible item type \"{got}\"; expected \"{expected}\"",
            ),
            DictComprehensionMismatch{part, got, expected} => format!(
                r#"{part} expression in dictionary comprehension has incompatible type "{got}"; expected type "{expected}""#,
            ),
            DictMemberMismatch{item, got_pair, expected_pair} => format!(
                "Dict entry {item} has incompatible type {got_pair}; expected {expected_pair}",
            ),
            UnpackedDictMemberMismatch{item, got, expected} => format!(
                r#"Unpacked dict entry {item} has incompatible type "{got}"; expected "{expected}""#,
            ),
            CannotInferLambdaParams => "Cannot infer type of lambda".to_string(),

            Redefinition{line} => {
                format!("Name {:?} already defined line {line}", self.code_under_issue())
            }
            ArgumentIssue(s) | ArgumentTypeIssue(s) | InvalidType(s) => s.clone().into(),
            TooManyArguments(rest) => format!("Too many arguments{rest}"),
            TooFewArguments(rest) => format!("Too few arguments{rest}"),
            IncompatibleDefaultArgument {argument_name, got, expected} => {
                if got.as_ref() == "None" {
                    additional_notes.push("PEP 484 prohibits implicit Optional. Accordingly, mypy has changed its default to no_implicit_optional=True".into());
                    additional_notes.push("Use https://github.com/hauntsaninja/no_implicit_optional to automatically upgrade your codebase".into());
                }
                format!(
                    "Incompatible default for argument \"{argument_name}\" \
                     (default has type \"{got}\", argument has type \"{expected}\")"
                )
            },
            TypeNotFound => format!("Name {:?} is not defined", self.code_under_issue()),
            UnexpectedTypeDeclaration => "Unexpected type declaration".to_string(),
            OverloadMismatch{name, args, variants} => {
                let arg_str = args.join("\", \"");
                additional_notes.push("Possible overload variants:".into());
                for variant in variants.iter() {
                    additional_notes.push(format!("    {variant}"));
                }
                match args.len() {
                    0 => format!(
                        "All overload variants of {name} require at least one argument"
                    ),
                    1 => format!(
                        "No overload variant of {name} matches argument type \"{arg_str}\"",
                    ),
                    _ => format!(
                        "No overload variant of {name} matches argument types \"{arg_str}\"",
                    ),
                }
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
            UnknownFunctionNotCallable => "Cannot call function of unknown type".to_string(),
            AnyNotCallable => "Any(...) is no longer supported. Use cast(Any, ...) instead".to_string(),
            NotIterable{type_} => format!("{type_} object is not iterable"),
            AsyncNotIterable{type_} => format!(
                r#""{type_}" has no attribute "__aiter__" (not async iterable)"#
            ),
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
            InvalidSetItemTarget{got, expected} => format!(
                "Incompatible types in assignment (expression has type \
                 \"{got}\", target has type \"{expected}\")",
            ),
            UnsupportedSetItemTarget(t) => format!(
                r#"Unsupported target for indexed assignment ("{t}")"#
            ),
            NotIndexable{type_} => format!("Value of type {type_:?} is not indexable"),
            InvalidSliceIndex => "Slice index must be an integer, SupportsIndex or None".to_string(),

            MethodWithoutArguments => {
                "Method must have at least one argument. Did you forget the \"self\" argument?".to_string()
            }
            MultipleStarredExpressionsInAssignment =>
                "Two starred expressions in assignment".to_string(),

            EnumFirstArgMustBeString =>
                "Enum() expects a string literal as the first argument".to_string(),
            EnumInvalidSecondArgument =>
                "Second argument of Enum() must be string, tuple, list or dict \
                 literal for mypy to determine Enum members".to_string(),
            EnumNeedsAtLeastOneItem { name } => format!(
                "{name}() needs at least one item"
            ),
            EnumWithTupleOrListExpectsStringPairs { name } => format!(
                "{name}() with tuple or list expects strings or (name, value) pairs"
            ),
            EnumWithDictRequiresStringLiterals { name } => format!(
                "{name}() with dict literal requires string literals"
            ),
            EnumUnexpectedArguments { name } => format!(
                "Unexpected arguments to {name}()"
            ),
            EnumAttemptedReuseOfMemberName { member_name, enum_name } => format!(
                r#"Attempted to reuse member name "{member_name}" in Enum definition "{enum_name}""#
            ),
            EnumIndexShouldBeAString { actual } => format!(
                r#"Enum index should be a string (actual index type "{actual}")"#
            ),
            EnumCannotBeGeneric => "Enum class cannot be generic".to_string(),
            EnumReusedMemberName { enum_name, member_name } => format!(
                r#"Attempted to reuse member name "{member_name}" in Enum definition "{enum_name}""#
            ),
            EnumWithMembersNotExtendable { name } => format!(
                r#"Cannot extend enum with existing members: "{name}""#
            ),
            EnumMultipleMixinNew { extra } => format!(
                r#"Only a single data type mixin is allowed for Enum subtypes, found extra "{extra}""#
            ),
            EnumMixinNotAllowedAfterEnum { after } => format!(
                r#"No non-enum mixin classes are allowed after "{after}""#
            ),
            EnumMembersAttributeOverwritten =>
                r#"Assigned "__members__" will be overridden by "Enum" internally"#.to_string(),

            DataclassMultipleKwOnly =>
                "There may not be more than one field with the KW_ONLY type".to_string(),
            DataclassNoDefaultAfterDefault =>
                "Attributes without a default cannot follow attributes with one".to_string(),
            DataclassOrderEnabledButNotEq =>
                r#""eq" must be True if "order" is True"#.to_string(),
            DataclassCustomOrderMethodNotAllowed { method_name } => format!(
                r#"You may not have a custom "{method_name}" method when "order" is True"#
            ),
            DataclassCannotInheritNonFrozenFromFrozen =>
                "Cannot inherit non-frozen dataclass from a frozen one".to_string(),
            DataclassCannotInheritFrozenFromNonFrozen =>
                "Cannot inherit frozen dataclass from a non-frozen one".to_string(),
            DataclassReplaceExpectedDataclass { got } => format!(
                r#"Argument 1 to "replace" has incompatible type "{got}"; expected a dataclass"#,
            ),
            DataclassReplaceExpectedDataclassInTypeVarBound { got } => format!(
                r#"Argument 1 to "replace" has a variable type "{got}" not bound to a dataclass"#,
            ),

            FunctionIsDynamic => "Function is missing a type annotation".to_string(),
            FunctionMissingReturnAnnotation =>
                "Function is missing a return type annotation".to_string(),
            FunctionMissingParamAnnotations =>
                "Function is missing a type annotation for one or more arguments".to_string(),
            CallToUntypedFunction{name} => format!(
                "Call to untyped function \"{name}\" in typed context"
            ),

            OnlyClassTypeApplication => {
                "Type application is only supported for generic classes".to_string()
            }
            TooFewValuesToUnpack{actual, expected} => match actual {
                1 => format!("Need more than {actual} value to unpack ({expected} expected)"),
                _ => format!("Need more than {actual} values to unpack ({expected} expected)"),
            },
            TooManyValuesToUnpack{actual, expected} =>
                format!("Too many values to unpack ({expected} expected, {actual} provided)"),
            UnpackingAStringIsDisallowed => "Unpacking a string is disallowed".to_string(),
            StarredExpressionOnlyNoTarget =>
                "Can use starred expression only as assignment target".to_string(),
            StmtOutsideFunction{keyword} => format!("{keyword:?} outside function"),
            YieldOrYieldFromInsideComprehension { keyword } => format!(
                "{keyword:?} inside comprehension or generator expression"
            ),
            AwaitOutsideFunction => r#""await" outside function"#.to_string(),
            AwaitOutsideCoroutine => r#""await" outside coroutine ("async def")"#.to_string(),
            YieldFromInAsyncFunction => r#""yield from" in async function"#.to_string(),
            ReturnInAsyncGenerator => r#""return" with value in async generator is not allowed"#.to_string(),
            InvalidBaseClass => format!("Invalid base class {:?}", self.code_under_issue()),
            IncompatibleBaseTuples => "Class has two incompatible bases derived from tuple".to_string(),
            InvalidMetaclass => format!("Invalid metaclass {:?}", self.code_under_issue()),
            MetaclassMustInheritFromType =>
                "Metaclasses not inheriting from \"type\" are not supported".to_string(),
            MetaclassConflict =>
                "Metaclass conflict: the metaclass of a derived class must be \
                 a (non-strict) subclass of the metaclasses of all its bases".to_string(),
            CannotSubclassNewType => "Cannot subclass \"NewType\"".to_string(),
            DuplicateBaseClass{name} => format!("Duplicate base class \"{name}\""),
            InconsistentMro{name} => format!(
                "Cannot determine consistent method resolution order (MRO) for \"{name}\""
            ),
            CyclicDefinition{name} =>
                format!("Cannot resolve name {name:?} (possible cyclic definition)"),
            EnsureSingleGenericOrProtocol =>
                "Only single Generic[...] or Protocol[...] can be in bases".to_string(),

            InvalidTypeDeclaration =>
                "Type cannot be declared in assignment to non-self attribute".to_string(),
            ClassVarOnlyInAssignmentsInClass =>
                "ClassVar can only be used for assignments in class body".to_string(),
            ClassVarNestedInsideOtherType =>
                "Invalid Type: ClassVar nested inside other type".to_string(),
            ClassVarTooManyArguments => "ClassVar[...] must have at most one type argument".to_string(),
            ClassVarCannotContainTypeVariables => "ClassVar cannot contain type variables".to_string(),
            ClassVarCannotContainSelfTypeInGenericClass =>
                "ClassVar cannot contain Self type in generic classes".to_string(),
            InvalidCallableParams => {
                additional_notes.push("See https://mypy.readthedocs.io/en/stable/kinds_of_types.html#callable-types-and-lambdas".into());
                "The first argument to Callable must be a list of types, parameter specification, or \"...\"".to_string()
            }
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
                    additional_notes.push(format!("(Hint: Use \"Generic[{name}]\" or \"Protocol[{name}]\" base class to bind \"{name}\" inside a class)"));
                    additional_notes.push(format!("(Hint: Use \"{name}\" in function signature to bind \"{name}\" inside a function)"));
                    format!("Type variable {qualified:?} is unbound")
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
            TypeVarCovariantInParamType =>
                "Cannot use a covariant type variable as a parameter".to_string(),
            TypeVarContravariantInReturnType =>
                "Cannot use a contravariant type variable as return type".to_string(),
            TypeVarVarianceIncompatibleWithParentType{ type_var_name } => format!(
                r#"Variance of TypeVar "{type_var_name}" incompatible with variance in parent type"#
            ),
            UnexpectedTypeForTypeVar =>
                "Cannot declare the type of a TypeVar or similar construct".to_string(),
            TypeVarTupleTooManyArguments =>
                "Only the first argument to TypeVarTuple has defined semantics".to_string(),
            ParamSpecTooManyKeywordArguments =>
                "The variance and bound arguments to ParamSpec do not have defined semantics yet".to_string(),
            ParamSpecNestedSpecificationsNotAllowed =>
                "Nested parameter specifications are not allowed".to_string(),
            MultipleTypeVarTuplesInClassDef =>
                "Can only use one type var tuple in a class def".to_string(),
            BoundTypeVarInAlias{name} =>
                format!("Can't use bound type variable \"{name}\" to define generic alias"),
            NestedConcatenate =>
                "Nested Concatenates are invalid".to_string(),
            ConcatenateLastParamNeedsToBeParamSpec =>
                "The last parameter to Concatenate needs to be a ParamSpec".to_string(),
            InvalidSelfArgument{argument_type, function_name, callable} => format!(
                "Invalid self argument \"{argument_type}\" to attribute function \"{function_name}\" with type \"{callable}\""
            ),
            SelfTypeInMetaclass => "Self type cannot be used in a metaclass".to_string(),
            SelfTypeInTypeAliasTarget => "Self type cannot be used in type alias target".to_string(),
            InvalidClassMethodFirstArgument{argument_type, function_name, callable} => format!(
                "Invalid self argument \"{argument_type}\" to class attribute function \"{function_name}\" with type \"{callable}\""
            ),
            InvalidClassmethodAndStaticmethod =>
                "Cannot have both classmethod and staticmethod".to_string(),
            UsedWithANonMethod{name} => format!(r#""{name}" used with a non-method"#),
            UnexpectedComprehension => "Unexpected comprehension".to_string(),
            AmbigousClassVariableAccess =>
                "Access to generic instance variables via class is ambiguous".to_string(),
            CannotInstantiateProtocol{name} => format!(
                "Cannot instantiate protocol class \"{name}\""
            ),

            InvalidAssertType { actual, wanted } => format!(
                r#"Expression is of type "{actual}", not "{wanted}""#
            ),

            SuperUsedOutsideClass => "\"super\" used outside class".to_string(),
            SuperWithSingleArgumentNotSupported => "\"super\" with a single argument not supported".to_string(),
            SuperVarargsNotSupported => "Varargs not supported with \"super\"".to_string(),
            SuperOnlyAcceptsPositionalArguments =>
                "\"super\" only accepts positional arguments".to_string(),
            SuperArgument1MustBeTypeObject =>
                "Argument 1 for \"super\" must be a type object; got a non-type instance".to_string(),
            SuperArgument2MustBeAnInstanceOfArgument1 =>
                "Argument 2 for \"super\" not an instance of argument 1".to_string(),
            SuperUnsupportedArgument{argument_index} =>
                format!("Unsupported argument {argument_index} for \"super\""),
            SuperTargetClassHasNoBaseClass => "Target class has no base class".to_string(),
            UndefinedInSuperclass{name} => format!("\"{name}\" undefined in superclass"),

            IncompatibleAssignmentInSubclass {base_class, got, expected} => format!(
                "Incompatible types in assignment (expression has type \"{got}\", \
                 base class \"{base_class}\" defined the type as \"{expected}\")"
            ),
            SignatureIncompatibleWithSupertype {base_class, name, notes} => {
                for note in notes.iter() {
                    additional_notes.push(note.to_string());
                }
                format!(r#"Signature of "{name}" incompatible with supertype "{base_class}""#)
            }
            MultipleInheritanceIncompatibility { name, class1, class2 } => format!(
                "Definition of \"{name}\" in base class \"{class1}\" is incompatible \
                 with definition in base class \"{class2}\""
            ),
            NewMustReturnAnInstance { got } => format!(
                "\"__new__\" must return a class instance (got \"{got}\")"
            ),
            NewIncompatibleReturnType { returns, must_return } => format!(
                "Incompatible return type for \"__new__\" (returns \
                 \"{returns}\", but must return a subtype of \"{must_return}\")"
            ),

            BaseExceptionExpected =>
                "Exception type must be derived from BaseException (or be a \
                 tuple of exception classes)".to_string(),
            BaseExceptionExpectedForRaise =>
                "Exception must be derived from BaseException".to_string(),
            ExceptStarIsNotAllowedToBeAnExceptionGroup =>
                "Exception type in except* cannot derive from BaseExceptionGroup".to_string(),

            TupleIndexOutOfRange => "Tuple index out of range".to_string(),
            NamedTupleExpectsStringLiteralAsFirstArg{name} =>
                format!("\"{name}()\" expects a string literal as the first argument"),
            StringLiteralExpectedAsNamedTupleItem =>
                 "String literal expected as \"namedtuple()\" item".to_string(),
            InvalidStmtInNamedTuple =>
                "Invalid statement in NamedTuple definition; expected \"field_name: field_type [= default]\"".to_string(),
            NamedTupleNonDefaultFieldFollowsDefault =>
                "Non-default NamedTuple fields cannot follow default fields".to_string(),
            InvalidSecondArgumentToNamedTuple{name} =>
                format!("List or tuple literal expected as the second argument to \"{name}()\""),
            UnexpectedArgumentsTo{name} =>
                format!("Unexpected arguments to \"{name}()\""),
            UnexpectedArgumentTo{name} =>
                format!("Unexpected argument to \"{name}()\""),
            TupleExpectedAsNamedTupleField => "Tuple expected as \"NamedTuple()\" field".to_string(),
            NamedTupleNamesCannotStartWithUnderscore{name, field_names} => format!(
                "\"{name}()\" field names cannot start with an underscore: {field_names}"),
            NamedTupleNameCannotStartWithUnderscore{field_name} => format!(
                "NamedTuple field name cannot start with an underscore: {field_name}"),
            NamedTupleInvalidFieldName => "Invalid \"NamedTuple()\" field name".to_string(),
            NamedTupleFirstArgumentMismatch { should, is } => format!(
                r#"First argument to namedtuple() should be "{should}", not "{is}""#
            ),
            NamedTupleDefaultsShouldBeListOrTuple =>
                r#"List or tuple literal expected as the defaults argument to namedtuple()"#.to_string(),
            NamedTupleToManyDefaults =>
                r#"Too many defaults given in call to "namedtuple()""#.to_string(),

            TypedDictIncompatibleType {got, key, expected} => format!(
                r#"Incompatible types (expression has type "{got}", TypedDict item "{key}" has type "{expected}")"#
            ),
            TypedDictExtraKey { key, typed_dict } => format!(
                r#"Extra key{} {key} for TypedDict "{typed_dict}""#,
                match key.as_bytes()[0] {
                    b'(' => "s",
                    _ => "",
                },
            ),
            UnexpectedArgumentsToTypedDict => "Unexpected arguments to TypedDict()".to_string(),
            TypedDictFirstArgMustBeString =>
                "TypedDict() expects a string literal as the first argument".to_string(),
            TypedDictSecondArgMustBeDict =>
                "TypedDict() expects a dictionary literal as the second argument".to_string(),
            TypedDictInvalidFieldName => "Invalid TypedDict() field name".to_string(),
            TypedDictSelfNotAllowed => "Self type cannot be used in TypedDict item type".to_string(),
            TypedDictNameMismatch { string_name, variable_name } => format!(
                r#"First argument "{string_name}" to TypedDict() does not match variable name "{variable_name}""#
            ),
            TypedDictTotalMustBeTrueOrFalse =>
                r#""total" argument must be a True or False literal"#.to_string(),
            TypedDictWrongArgumentsInConstructor =>
                "Expected keyword arguments, {...}, or dict(...) in TypedDict constructor".to_string(),
            TypedDictKeysMustBeStringLiteral =>
                "Expected TypedDict key to be string literal".to_string(),
            TypedDictAccessKeyMustBeStringLiteral { keys } => format!(
                "TypedDict key must be a string literal; expected one of ({keys})"
            ),
            TypedDictKeySetItemIncompatibleType { key, got, expected } => format!(
                r#"Value of "{key}" has incompatible type "{got}"; expected "{expected}""#
            ),
            TypedDictHasNoKey { typed_dict, key } | TypedDictHasNoKeyForGet { typed_dict, key } => format!(
                r#"TypedDict "{typed_dict}" has no key "{key}""#
            ),

            TypedDictKeyCannotBeDeleted { typed_dict, key } => format!(
                r#"Key "{key}" of TypedDict "{typed_dict}" cannot be deleted"#
            ),
            TypedDictInvalidMember =>
                "Invalid statement in TypedDict definition; expected \"field_name: field_type\"".to_string(),
            TypedDictInvalidMemberRightSide =>
                "Right hand side values are not supported in TypedDict".to_string(),
            TypedDictBasesMustBeTypedKeys =>
                "All bases of a new TypedDict must be TypedDict types".to_string(),
            TypedDictDuplicateKey { key } => format!(
                r#"Duplicate TypedDict key "{key}""#
            ),
            TypedDictOverwritingKeyWhileExtending { key } => format!(
                r#"Overwriting TypedDict field "{key}" while extending"#
            ),
            TypedDictOverwritingKeyWhileMerging { key } => format!(
                r#"Overwriting TypedDict field "{key}" while merging"#
            ),
            TypedDictMissingKeys { typed_dict, keys } => match keys.as_ref() {
                [key] => format!(r#"Missing key "{key}" for TypedDict "{typed_dict}""#),
                _ => format!(
                    r#"Missing keys ({}) for TypedDict "{typed_dict}""#,
                    join_with_commas(keys.iter().map(|key| format!("\"{key}\"")))
                ),
            },
            TypedDictNonRequired { key } => format!(
                r#"Non-required key "{key}" not explicitly found in any ** item"#
            ),
            TypedDictUnsupportedTypeInStarStar { type_ } => format!(
                r#"Unsupported type "{type_}" for ** expansion in TypedDict"#
            ),

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
            OverloadInconsistentKind { kind } => format!(
                "Overload does not consistently use the \"@{}\" decorator on all function signatures.",
                match kind {
                    FunctionKind::Classmethod { .. } => "classmethod",
                    FunctionKind::Staticmethod { .. } => "staticmethod",
                    FunctionKind::Property { .. } => "property",
                    FunctionKind::Function { .. } => unreachable!()
                }
            ),
            OverloadedPropertyNotSupported =>
                "An overload can not be a property".to_string(),

            DecoratorOnTopOfPropertyNotSupported =>
                "Decorators on top of @property are not supported".to_string(),
            OnlySupportedTopDecoratorSetter{name} =>
                format!("Only supported top decorator is @{name}.setter"),
            UnexpectedDefinitionForProperty{name} =>
                format!("Unexpected definition for property \"{name}\""),
            PropertyIsReadOnly{class_name, property_name} => format!(
                "Property \"{property_name}\" defined in \"{class_name}\" is read-only"
            ),

            InvariantNote{actual, maybe} => {
                type_ = "note";
                let suffix = match *actual {
                    "List" => "",
                    "Dict" => " in the value type",
                    _ => unreachable!(),
                };
                additional_notes.push(format!("Consider using \"{maybe}\" instead, which is covariant{suffix}"));
                format!(
                    "\"{actual}\" is invariant -- see \
                     https://mypy.readthedocs.io/en/stable/common_issues.html#variance",
                )
            }
            AnnotationInUntypedFunction => {
                type_ = "note";
                "By default the bodies of untyped functions are not checked, \
                 consider using --check-untyped-defs".to_string()
            }
            Note(s) => {
                type_ = "note";
                s.clone().into()
            }
        };
        let mut result = fmt_line(config, path, line_column, type_, &error);
        if config.show_error_codes {
            if let Some(mypy_error_code) = self.issue.type_.mypy_error_code() {
                result += &format!("  [{mypy_error_code}]");
            }
        }
        for note in additional_notes {
            result += "\n";
            result += &fmt_line(config, path, line_column, "note", &note);
        }
        result
    }
}

fn fmt_line(
    config: &DiagnosticConfig,
    path: &str,
    line_column: (usize, usize),
    type_: &str,
    error: &str,
) -> String {
    let line = line_column.0;
    if config.show_column_numbers {
        format!("{path}:{line}:{}: {type_}: {error}", line_column.1)
    } else {
        format!("{path}:{line}: {type_}: {error}")
    }
}

impl std::fmt::Debug for Diagnostic<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", &self.as_string(&DiagnosticConfig::default()))
    }
}

#[derive(Default)]
pub struct DiagnosticConfig {
    pub ignore_missing_imports: bool,
    pub show_error_codes: bool,
    pub show_column_numbers: bool,
}

impl DiagnosticConfig {
    pub(crate) fn should_be_reported(&self, type_: &IssueType) -> bool {
        match type_ {
            IssueType::ImportAttributeError { .. }
            | IssueType::ModuleNotFound { .. }
            | IssueType::ModuleAttributeError { .. } => !self.ignore_missing_imports,
            _ => true,
        }
    }
}

#[derive(Default)]
pub struct Diagnostics(InsertOnlyVec<Issue>);

impl Diagnostics {
    pub fn add_if_not_ignored(
        &self,
        issue: Issue,
        maybe_ignored: Option<Option<&str>>,
    ) -> Result<&Issue, Issue> {
        let mut add_not_covered_note = None;
        if let Some(specific) = maybe_ignored {
            if let Some(specific) = specific {
                // It's possible to write # type: ignore   [ xyz , name-defined ]
                let e = issue.type_.mypy_error_code();
                let super_ = issue.type_.mypy_error_supercode();
                if specific.split(',').any(|specific| {
                    let code = specific.trim_matches(' ');
                    e == Some(code) || super_ == Some(code) || e.is_none()
                }) {
                    return Err(issue);
                } else if e.is_some() {
                    add_not_covered_note = e;
                }
            } else {
                return Err(issue);
            }
        }
        self.0.push(Box::pin(issue));
        let last_issue = self.0.last().unwrap();
        if let Some(s) = add_not_covered_note {
            self.0.push(Box::pin(Issue {
                type_: IssueType::Note(
                    format!(r#"Error code "{s}" not covered by "type: ignore" comment"#).into(),
                ),
                start_position: last_issue.start_position,
                end_position: last_issue.end_position,
            }));
        }
        Ok(last_issue)
    }

    pub unsafe fn iter(&self) -> impl Iterator<Item = &Issue> {
        self.0.iter()
    }

    pub fn clear(&mut self) {
        self.0.as_vec_mut().clear()
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
