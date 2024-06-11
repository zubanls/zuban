use std::collections::HashMap;

use parsa_python_cst::{CodeIndex, NodeIndex, Tree};

use crate::{
    database::Database,
    file::{File, GenericCounts, PythonFile, OVERLAPPING_REVERSE_TO_NORMAL_METHODS},
    name::TreePosition,
    type_::{FunctionKind, TypeVarLike, Variance},
    utils::{join_with_commas, InsertOnlyVec},
    PythonVersion, TypeCheckerFlags,
};

#[derive(Debug, Clone)]
#[allow(dead_code)]  // TODO remove this
#[rustfmt::skip]  // This is way more readable if we are not auto-formatting this.
pub(crate) enum IssueKind {
    InvalidSyntax,
    InvalidSyntaxInTypeComment { type_comment: Box<str> },
    InvalidSyntaxInTypeAnnotation,
    TypeIgnoreWithErrorCodeNotSupportedForModules { ignore_code: Box<str> },
    DirectiveSyntaxError(Box<str>),

    AttributeError { object: Box<str>, name: Box<str> },
    UnionAttributeError { object: Box<str>, union: Box<str>, name: Box<str> },
    UnionAttributeErrorOfUpperBound(Box<str>),
    // Mypy somehow has a different error here than the one for imports.
    ImportAttributeError { module_name: Box<str>, name: Box<str> },
    ModuleAttributeError { name: Box<str> },
    ImportStubNoExplicitReexport { module_name: Box<str>, attribute: Box<str> },
    UnsupportedClassScopedImport,
    UnimportedRevealType,  // From --enable-error-code=unimported-reveal
    NameError { name: Box<str> },
    ArgumentIssue(Box<str>),
    ArgumentTypeIssue(Box<str>),
    TooFewArguments(Box<str>),
    TooManyArguments(Box<str>),
    IncompatibleDefaultArgument{ argument_name: Box<str>, got: Box<str>, expected: Box<str> },
    InvalidCastTarget,
    IncompatibleReturn { got: Box<str>, expected: Box<str> },
    IncompatibleImplicitReturn { expected: Box<str> },
    ReturnValueExpected,
    NoReturnValueExpected,
    IncompatibleTypes { cause: &'static str, got: Box<str>, expected: Box<str> },
    DoesNotReturnAValue(Box<str>),
    InvalidGeneratorReturnType,
    InvalidAsyncGeneratorReturnType,
    ReturnStmtInFunctionWithNeverReturn,
    ImplicitReturnInFunctionWithNeverReturn,
    MissingReturnStatement { code: &'static str },
    YieldFromCannotBeApplied { to: Box<str> },
    YieldValueExpected,
    IncompatibleAssignment { got: Box<str>, expected: Box<str> },
    IncompatibleImportAssignment { name: Box<str>, got: Box<str>, expected: Box<str> },
    CannotAssignToClassVarViaInstance { name: Box<str> },
    CannotAssignToAMethod,
    CannotAssignToFinal { name: Box<str>, is_attribute: bool },
    AssigningToNameOutsideOfSlots { name: Box<str>, class: Box<str> },
    ListItemMismatch { item: usize, got: Box<str>, expected: Box<str> },
    ListComprehensionMismatch { got: Box<str>, expected: Box<str> },
    SetComprehensionMismatch { got: Box<str>, expected: Box<str> },
    GeneratorComprehensionMismatch { got: Box<str>, expected: Box<str> },
    DictComprehensionMismatch { part: &'static str, got: Box<str>, expected: Box<str> },
    DictMemberMismatch { item: usize, got_pair: Box<str>, expected_pair: Box<str> },
    UnpackedDictMemberMismatch { item: usize, got: Box<str>, expected: Box<str> },
    CannotInferLambdaParams,
    NeedTypeAnnotation { for_: Box<str>, hint: Option<&'static str> },

    Redefinition { name: Box<str>, suffix: Box<str> },
    CannotRedifineAs { name: Box<str>, as_: &'static str },
    CannotRedifineAsFinal,
    IncompatibleConditionalFunctionSignature { original: Box<str>, redefinition: Box<str> },
    IncompatibleConditionalFunctionSignaturePretty { original: Box<str>, redefinition: Box<str> },
    NameUsedBeforeDefinition { name: Box<str> },
    ModuleNotFound { module_name: Box<str> },
    NoParentModule,
    TypeNotFound,
    UnexpectedTypeDeclaration,
    TypeArgumentIssue { class: Box<str>, counts: GenericCounts },
    TypeAliasArgumentIssue { counts: GenericCounts },
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
    VariadicTupleUnpackingRequiresStarTarget,
    TooManyAssignmentTargetsForVariadicUnpack,
    UnpackingAStringIsDisallowed,
    StarredExpressionOnlyNoTarget,
    BreakOutsideLoop,
    ContinueOutsideLoop,
    StmtOutsideFunction { keyword: &'static str },
    YieldOrYieldFromInsideComprehension { keyword: &'static str },
    AwaitOutsideFunction,
    AwaitOutsideCoroutine,
    YieldFromInAsyncFunction,
    ReturnInAsyncGenerator,
    NonlocalAtModuleLevel,
    NonlocalNoBindingFound { name: Box<str> },
    NonlocalAndGlobal { name: Box<str> },
    NameDefinedInLocalScopeBeforeNonlocal { name: Box<str> },
    OnlyClassTypeApplication,
    InvalidBaseClass,
    CannotInheritFromFinalClass { class_name: Box<str> },
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
    SubclassOfFinalCannotExist { final_class: Box<str>, other_class: Box<str> },
    NewTypeCannotUseProtocols,
    BasesOfProtocolMustBeProtocol,
    MustHaveOneArgument { name: &'static str },
    TypeCannotContainAnotherType,
    InvalidRecursiveTypeAliasUnionOfItself { target: &'static str },
    InvalidRecursiveTypeAliasTypeVarNesting,
    RecursiveTypesNotAllowedInFunctionScope { alias_name: Box<str> },

    FinalTooManyArguments,
    FinalNameMustBeInitializedWithValue,
    FinalInWrongPlace,
    FinalWithoutInitializerAndType,
    FinalInClassBodyCannotDependOnTypeVariables,
    FinalAndClassVarUsedBoth,
    FinalCanOnlyBeUsedInMethods,
    FinalShouldBeAppliedOnlyToOverloadImplementation,
    FinalInStubMustBeAppliedToFirstOverload,
    NeedTypeArgumentForFinalInDataclass,

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
    TypeVarInvalidDefault,
    TypeVarTupleInvalidDefault,
    ParamSpecInvalidDefault,
    TypeVarDefaultMustBeASubtypeOfBound,
    TypeVarDefaultMustBeASubtypeOfConstraints,
    VarNameMismatch {
        class_name: Box<str>,
        string_name: Box<str>,
        variable_name: Box<str>
    },
    TypeVarInReturnButNotArgument,
    TypeVarCovariantInParamType,
    TypeVarContravariantInReturnType,
    TypeVarVarianceIncompatibleWithParentType { type_var_name: Box<str> },
    UnexpectedTypeForTypeVar,
    ParamSpecTooManyKeywordArguments,
    ParamSpecNestedSpecificationsNotAllowed,
    MultipleTypeVarTuplesInClassDef,
    BoundTypeVarInAlias { name: Box<str> },
    NestedConcatenate,
    ConcatenateLastParamNeedsToBeParamSpec,
    InvalidSelfArgument { argument_type: Box<str>, function_name: Box<str>, callable: Box<str> },
    SelfTypeInMetaclass,
    SelfTypeInTypeAliasTarget,
    SelfTypeOutsideOfClass,
    InvalidClassMethodFirstArgument { argument_type: Box<str>, function_name: Box<str>, callable: Box<str> },
    InvalidClassmethodAndStaticmethod,
    UsedWithANonMethod { name: &'static str },
    UnexpectedComprehension,
    AmbigousClassVariableAccess,
    SlotsConflictWithClassVariableAccess { name: Box<str> },
    CannotInstantiateProtocol { name: Box<str> },
    OnlyConcreteClassAllowedWhereTypeExpected { type_: Box<str> },
    UnpackRequiresExactlyOneArgument,
    UnpackOnlyValidInVariadicPosition,
    VariadicUnpackMustBeTupleLike { actual: Box<str> },
    MoreThanOneUnpackTypeIsNotAllowed,
    VariadicUnpackMustBeTupleOrTypeVarTuple { type_: Box<str> },
    TypeVarTupleCannotBeSplit,

    CannotUseIsinstanceWith { func: &'static str, with: &'static str },
    CannotUseIsinstanceWithParametrizedGenerics,

    InvalidAssertType { actual: Box<str>, wanted: Box<str> },
    AssertionAlwaysTrueBecauseOfParentheses,

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
    OverloadOrderMustMatchSupertype { name: Box<str>, base_class: Box<str> },
    ReturnTypeIncompatibleWithSupertype { message: String, async_note: Option<Box<str>> },
    ArgumentIncompatibleWithSupertype { message: Box<str>, eq_class: Option<Box<str>>, add_liskov_note: bool },
    MultipleInheritanceIncompatibility { name: Box<str>, class1: Box<str>, class2: Box<str> },
    MissingBaseForOverride { name: Box<str> },
    InvalidSignature { signature: Box<str> },
    OperatorSignaturesAreUnsafelyOverlapping { reverse_name: Box<str>, reverse_class: Box<str>, forward_class: Box<str> },
    ForwardOperatorIsNotCallable { forward_name: &'static str },
    SignaturesAreIncompatible { name1: Box<str>, name2: &'static str },
    NewMustReturnAnInstance { got: Box<str> },
    NewIncompatibleReturnType { returns: Box<str>, must_return: Box<str> },
    MustReturnNone { function_name: Box<str> },
    IncorrectExitReturn,
    InvalidSpecialMethodSignature { type_: Box<str>, special_method: &'static str },
    GetattributeInvalidAtModuleLevel,
    InvalidSlotsDefinition { actual: Box<str> },
    ProtocolMembersMustHaveExplicitlyDeclaredTypes,
    ProtocolMembersCannotHaveSelfVariableDefinitions,
    ProtocolWrongVariance { type_var_name: Box<str>, actual_variance: Variance, expected_variance: Variance },
    CannotOverrideClassVariableWithInstanceVariable { base_class: Box<str> },
    CannotOverrideInstanceVariableWithClassVariable { base_class: Box<str> },
    CannotOverrideFinalAttribute { base_class: Box<str>, name: Box<str> },
    ExplicitOverrideFlagRequiresOverride { method: Box<str>, class: Box<str> },

    BaseExceptionExpected,
    BaseExceptionExpectedForRaise,
    ExceptStarIsNotAllowedToBeAnExceptionGroup,

    TypeGuardFunctionsMustHaveArgument { name: &'static str },
    TypeIsNarrowedTypeIsNotSubtypeOfInput { narrowed_t: Box<str>, input_t: Box<str> },

    TupleIndexOutOfRange { variadic_max_len: Option<usize> },
    TupleSliceStepCannotBeZero,  // Not in mypy
    AmbigousSliceOfVariadicTuple,
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
    NamedTupleGenericInClassDefinition,
    NamedTupleShouldBeASingleBase,
    NamedTupleSelfNotAllowed,

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
    TypedDictBasesMustBeTypedDicts,
    TypedDictDuplicateKey { key: Box<str> },
    TypedDictOverwritingKeyWhileExtending { key: Box<str> },
    TypedDictOverwritingKeyWhileMerging { key: Box<str> },
    TypedDictMissingKeys { typed_dict: Box<str>, keys: Box<[Box<str>]> },
    TypedDictNonRequired { key: Box<str> },
    TypedDictUnsupportedTypeInStarStar { type_: Box<str> },
    TypedDictArgumentNameOverlapWithUnpack { names: Box<str> },
    UnpackItemInStarStarMustBeTypedDict,
    TypedDictSetdefaultWrongDefaultType { got: Box<str>, expected: Box<str> },

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
    ReadOnlyPropertyCannotOverwriteReadWriteProperty,
    OnlyInstanceMethodsCanBeDecoratedWithProperty,
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
    EnumCannotOverrideWritableAttributeWithFinal { name: Box<str> },

    DataclassMultipleKwOnly,
    DataclassNoDefaultAfterDefault,
    DataclassOrderEnabledButNotEq,
    DataclassCustomOrderMethodNotAllowed { method_name: &'static str },
    DataclassCannotInheritNonFrozenFromFrozen,
    DataclassCannotInheritFrozenFromNonFrozen,
    DataclassReplaceExpectedDataclass { got: Box<str> },
    DataclassReplaceExpectedDataclassInTypeVarBound { got: Box<str> },
    DataclassContainsTypeAlias,
    DataclassUnpackingKwargsInField,
    DataclassAttributeMayOnlyBeOverriddenByAnotherAttribute,
    DataclassPlusExplicitSlots { class_name: Box<str> },

    // From --disallow-untyped-defs
    FunctionIsDynamic,
    FunctionMissingReturnAnnotation { hint_return_none: bool }, // Also from --disallow-incomplete-defs
    FunctionMissingParamAnnotations, // Also from --disallow-incomplete-defs

    CallToUntypedFunction { name: Box<str> }, // From --disallow-untyped-calls
    MissingTypeParameters { name: Box<str> }, // From --disallow-any-generics
    UntypedDecorator { name: Box<str> }, // From --disallow-untyped-decorators
    UntypedFunctionAfterDecorator { got: Option<Box<str>> }, // From --disallow-any-decorated
    DisallowedAnySubclass { class: Box<str> }, // From --disallow-subclassing-any
    DisallowedAnyMetaclass { class: Box<str> }, // From --disallow-subclassing-any
    DisallowedAnyExplicit, // From --disallow-any-explicit
    UnimportedTypeBecomesAny { prefix: Box<str>, type_: Box<str> }, // From --diallow-any-unimported
    DisallowedAnyExpr { type_: Box<str> },
    UnreachableStatement, // From --warn-unreachable
    RightOperandIsNeverOperated { right: &'static str }, // From --warn-unreachable
    RedundantCast { to: Box<str> }, // From --warn-redundant-casts
    ReturnedAnyWarning { expected: Box<str> }, // From --warn-return-any
    NonOverlappingEqualityCheck { left_type: Box<str>, right_type: Box<str> }, // From --strict-equality
    NonOverlappingIdentityCheck { left_type: Box<str>, right_type: Box<str> }, // From --strict-equality
    NonOverlappingContainsCheck { element_type: Box<str>, container_type: Box<str> }, // From --strict-equality

    InvariantNote { actual: &'static str, maybe: &'static str },
    AnnotationInUntypedFunction,
    Note(Box<str>),
}

impl IssueKind {
    pub fn mypy_error_code(&self) -> Option<&'static str> {
        use IssueKind::*;
        Some(match &self {
            Note(_) | InvariantNote { .. } => return None,
            InvalidSyntax
            | InvalidSyntaxInTypeComment { .. }
            | InvalidSyntaxInTypeAnnotation
            | TypeIgnoreWithErrorCodeNotSupportedForModules { .. }
            | DirectiveSyntaxError(..) => "syntax",
            AttributeError { .. }
            | ImportAttributeError { .. }
            | ModuleAttributeError { .. }
            | ImportStubNoExplicitReexport { .. }
            | AsyncNotIterable { .. }
            | NotIterable { .. } => "attr-defined",
            NameError { .. } => "name-defined",
            Redefinition { .. } => "no-redef",
            NameUsedBeforeDefinition { .. } => "used-before-def",
            UnionAttributeError { .. } | UnionAttributeErrorOfUpperBound(..) => "union-attr",
            ArgumentTypeIssue(_) | SuperArgument1MustBeTypeObject => "arg-type",
            ArgumentIssue { .. } | TooManyArguments { .. } | TooFewArguments { .. } => "call-arg",
            InvalidType(_) => "valid-type",
            IncompatibleReturn { .. }
            | IncompatibleImplicitReturn { .. }
            | ReturnValueExpected
            | NoReturnValueExpected => "return-value",
            MissingReturnStatement { code } => code,
            IncompatibleDefaultArgument { .. }
            | IncompatibleAssignment { .. }
            | IncompatibleAssignmentInSubclass { .. }
            | IncompatibleImportAssignment { .. }
            | InvalidSetItemTarget { .. } => "assignment",
            CannotAssignToAMethod => "method-assign",
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
            TypeArgumentIssue { .. } | MissingTypeParameters { .. } => "type-arg",
            ModuleNotFound { .. } => "import-not-found",
            ListItemMismatch { .. } => "list-item",
            DictMemberMismatch { .. } | UnpackedDictMemberMismatch { .. } => "dict-item",
            NewTypeMustBeSubclassable { .. } => "valid-newtype",
            OverloadImplementationNeeded { .. } => "no-overload-impl",
            OverloadMismatch { .. } => "call-overload",
            OverloadIncompatibleReturnTypes { .. } => "overload-overlap",
            SignatureIncompatibleWithSupertype { .. }
            | ArgumentIncompatibleWithSupertype { .. }
            | OverloadOrderMustMatchSupertype { .. }
            | ReturnTypeIncompatibleWithSupertype { .. } => "override",
            IncorrectExitReturn => "exit-return",
            FunctionIsDynamic
            | FunctionMissingReturnAnnotation { .. }
            | FunctionMissingParamAnnotations => "no-untyped-def",
            DoesNotReturnAValue(_) => "func-returns-value",
            CallToUntypedFunction { .. } => "no-untyped-call",
            AnnotationInUntypedFunction => "annotation-unchecked",
            AwaitOutsideFunction => "top-level-await",
            AwaitOutsideCoroutine => "await-not-async",
            NeedTypeAnnotation { .. } => "var-annotated",
            TypeIsNarrowedTypeIsNotSubtypeOfInput { .. } => "narrowed-type-not-subtype",

            TypedDictNameMismatch { .. } | NamedTupleFirstArgumentMismatch { .. } => "name-match",
            TypedDictMissingKeys { .. }
            | TypedDictIncompatibleType { .. }
            | TypedDictKeySetItemIncompatibleType { .. }
            | TypedDictSetdefaultWrongDefaultType { .. }
            | TypedDictHasNoKeyForGet { .. } => "typeddict-item",
            TypedDictExtraKey { .. } | TypedDictHasNoKey { .. } => "typeddict-unknown-key",

            UnreachableStatement | RightOperandIsNeverOperated { .. } => "unreachable",
            RedundantCast { .. } => "redundant-cast",
            ReturnedAnyWarning { .. } => "no-any-return",
            NonOverlappingEqualityCheck { .. }
            | NonOverlappingContainsCheck { .. }
            | NonOverlappingIdentityCheck { .. } => "comparison-overlap",
            UnimportedRevealType => "unimported-reveal",

            _ => "misc",
        })
    }

    fn mypy_error_supercode(&self) -> Option<&'static str> {
        // See also https://mypy.readthedocs.io/en/stable/error_codes.html#subcodes-of-error-codes
        use IssueKind::*;
        match &self {
            TypedDictExtraKey { .. } | TypedDictHasNoKey { .. } => Some("typeddict-item"),
            CannotAssignToAMethod => Some("assignment"),
            ModuleNotFound { .. } => Some("import"),
            _ => None,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Issue {
    pub(crate) kind: IssueKind,
    pub start_position: CodeIndex,
    pub end_position: CodeIndex,
}

impl Issue {
    pub(crate) fn from_node_index(tree: &Tree, node_index: NodeIndex, kind: IssueKind) -> Self {
        Self {
            kind,
            start_position: tree.node_start_position(node_index),
            end_position: tree.node_end_position(node_index),
        }
    }

    pub(crate) fn from_start_stop(
        start_position: CodeIndex,
        end_position: CodeIndex,
        kind: IssueKind,
    ) -> Self {
        Self {
            kind,
            start_position,
            end_position,
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
        self.issue.kind.mypy_error_code().unwrap_or("note")
    }

    pub fn is_mypy_semanal_error(&self) -> bool {
        // Mypy has semanal-*.test tests that only use Mypy's semantic analysis part instead of
        // full type checking, which leads to not all errors being relevant. Here we filter only
        // for the relevant ones.
        use IssueKind::*;
        !self.issue.kind.mypy_error_code().is_some_and(|c| {
            [
                "var-annotated",
                "assignment",
                "annotation-unchecked",
                "index",
                "return-value",
                "return",
            ]
            .contains(&c)
        }) && !matches!(
            self.issue.kind,
            NotIterable { .. }
                | AttributeError { .. }
                | OverloadUnmatchable { .. }
                | OverloadImplementationArgumentsNotBroadEnough { .. }
                | TypeVarInReturnButNotArgument { .. }
                | OnlyClassTypeApplication { .. }
                | UnsupportedClassScopedImport { .. }
                | CannotInheritFromFinalClass { .. }
                | InvalidAssertType { .. }
                | BaseExceptionExpected
                | BaseExceptionExpectedForRaise
        )
    }

    pub fn as_string(&self, config: &DiagnosticConfig) -> String {
        let mut kind = "error";
        let mut path = self
            .db
            .file_path(self.file.file_index())
            .trim_start_matches(&self.file.file_entry(self.db).parent.workspace_path() as &str);
        if path == "__main__" {
            path = "main";
        }
        let line_column = self.start_position().line_and_column();
        let line = line_column.0;
        let mut additional_notes = vec![];
        use IssueKind::*;
        let error = match &self.issue.kind {
            InvalidSyntax => "invalid syntax".to_string(),
            InvalidSyntaxInTypeComment { type_comment } => format!(
                r#"Syntax error in type comment "{type_comment}""#
            ),
            InvalidSyntaxInTypeAnnotation => "Syntax error in type annotation".to_string(),
            TypeIgnoreWithErrorCodeNotSupportedForModules { ignore_code } => {
                additional_notes.push(r#"Error code "syntax" not covered by "type: ignore" comment"#.to_string());
                format!(
                    "type ignore with error code is not supported for modules; \
                     use `# mypy: disable-error-code=\"{ignore_code}\"`"
                )
            }
            DirectiveSyntaxError(s) => s.to_string(),

            AttributeError{object, name} => format!("{object} has no attribute {name:?}"),
            UnionAttributeError{object, union, name} => format!("Item {object} of \"{union}\" has no attribute {name:?}"),
            UnionAttributeErrorOfUpperBound(s) => s.to_string(),
            ImportAttributeError{module_name, name} => {
                format!("Module {module_name:?} has no attribute {name:?}")
            }
            ModuleAttributeError{name} => {
                format!("Module has no attribute {name:?}")
            }
            ImportStubNoExplicitReexport { module_name, attribute } => format!(
                r#"Module "{module_name}" does not explicitly export attribute "{attribute}""#
            ),
            UnsupportedClassScopedImport =>
                "Unsupported class scoped import".to_string(),
            NameError{name} => format!("Name {name:?} is not defined"),
            IncompatibleReturn{got, expected} => {
                format!("Incompatible return value type (got {got:?}, expected {expected:?})")
            }
            IncompatibleImplicitReturn { expected } => format!(
                r#"Incompatible return value type (implicitly returns "None", expected "{expected}")"#
            ),
            ReturnValueExpected => "Return value expected".to_string(),
            NoReturnValueExpected => "No return value expected".to_string(),
            IncompatibleTypes{cause, got, expected} => {
                format!(r#"Incompatible types in {cause} (actual type "{got}", expected type "{expected}")"#)
            }
            DoesNotReturnAValue(named) => format!("{named} does not return a value (it only ever returns None)"),
            InvalidGeneratorReturnType =>
                r#"The return type of a generator function should be "Generator" or one of its supertypes"#.to_string(),
            InvalidAsyncGeneratorReturnType =>
                r#"The return type of an async generator function should be "AsyncGenerator" or one of its supertypes"#.to_string(),
            ReturnStmtInFunctionWithNeverReturn =>
                "Return statement in function which does not return".to_string(),
            ImplicitReturnInFunctionWithNeverReturn =>
                "Implicit return in function which does not return".to_string(),
            MissingReturnStatement { .. } => "Missing return statement".to_string(),
            YieldFromCannotBeApplied { to } => format!(r#""yield from" can't be applied to "{to}""#),
            YieldValueExpected => "Yield value expected".to_string(),
            IncompatibleAssignment{got, expected} => format!(
                r#"Incompatible types in assignment (expression has type "{got}", variable has type "{expected}")"#,
            ),
            IncompatibleImportAssignment { name, got, expected } => {
                if got.as_ref() == "ModuleType" {
                    format!(
                        r#"Incompatible import of "{name}" (imported name has type Module, local name has type "{expected}")"#,
                    )
                } else {
                    format!(
                        r#"Incompatible import of "{name}" (imported name has type "{got}", local name has type "{expected}")"#,
                    )
                }
            }
            CannotAssignToClassVarViaInstance { name } => format!(
                "Cannot assign to class variable \"{name}\" via instance"
            ),
            CannotAssignToAMethod => "Cannot assign to a method".to_owned(),
            CannotAssignToFinal { is_attribute, name } => {
                if *is_attribute {
                    format!("Cannot assign to final attribute \"{name}\"")
                } else {
                    format!("Cannot assign to final name \"{name}\"")
                }
            }
            AssigningToNameOutsideOfSlots { name, class } => format!(
                r#"Trying to assign name "{name}" that is not in "__slots__" of type "{class}""#
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
            NeedTypeAnnotation { for_, hint } => match hint {
                Some(hint) => format!(
                    r#"Need type annotation for "{for_}" (hint: "{for_}: {hint} = ...")"#
                ),
                None => format!(r#"Need type annotation for "{for_}""#),
            },

            Redefinition{name, suffix} => format!(r#"Name "{name}" already defined {suffix}"#),
            CannotRedifineAs { name, as_ } => format!(r#"Cannot redefine "{name}" as {as_}"#),
            CannotRedifineAsFinal => r#"Cannot redefine an existing name as final"#.to_string(),
            IncompatibleConditionalFunctionSignature { original, redefinition } => format!(
                r#"Incompatible redefinition (redefinition with type "{redefinition}", original type "{original}")"#
            ),
            IncompatibleConditionalFunctionSignaturePretty { original, redefinition } => {
                additional_notes.push("Original:".into());
                additional_notes.push(format!("    {original}"));
                additional_notes.push("Redefinition:".into());
                additional_notes.push(format!("    {redefinition}"));
                "All conditional function variants must have identical signatures".into()
            }
            NameUsedBeforeDefinition { name } => format!(
                r#"Name "{name}" is used before definition"#
            ),
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
            TypeArgumentIssue{class, counts} => {
                if counts.at_least_expected {
                    format!(
                        "Bad number of arguments, expected: at least {}, given: {}",
                        counts.expected,
                        counts.given,
                    )
                } else if let Some(expected_minimum) = counts.expected_minimum {
                    format!(
                        "{class:?} expects between {expected_minimum} and {} type arguments, but {} given",
                        counts.expected,
                        counts.given,
                    )
                } else {
                    match counts.expected {
                        0 => format!("{class:?} expects no type arguments, but {} given", counts.given),
                        1 => format!("{class:?} expects {} type argument, but {} given", counts.expected, counts.given),
                        _ => format!("{class:?} expects {} type arguments, but {} given", counts.expected, counts.given),
                    }
                }
            }
            TypeAliasArgumentIssue{counts} => {
                if let Some(expected_minimum) = counts.expected_minimum {
                    format!(
                        "Bad number of arguments for type alias, expected between {expected_minimum} and {}, given {}",
                        counts.expected,
                        counts.given,
                    )
                } else {
                    format!(
                        "Bad number of arguments for type alias, expected {}{}, given {}",
                        if counts.at_least_expected {
                            "at least "
                        } else {
                            ""
                        },
                        counts.expected,
                        counts.given,
                    )
                }
            }
            ModuleNotFound{module_name} => {
                if let Some(types_package) = has_known_types_package(module_name) {
                    additional_notes.push(format!("Hint: \"python3 -m pip install {types_package}\""));
                    additional_notes.push(
                        r#"(or run "mypy --install-types" to install all missing stub packages)"#.to_string()
                    );
                    format!("Library stubs not installed for \"{module_name}\"")
                } else {
                    format!("Cannot find implementation or library stub for module named {module_name:?}")

                }
            }
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
            EnumCannotOverrideWritableAttributeWithFinal { name } => format!(
                r#"Cannot override writable attribute "{name}" with a final one"#
            ),

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
            DataclassContainsTypeAlias =>
                "Type aliases inside dataclass definitions are not supported at runtime".to_string(),
            DataclassUnpackingKwargsInField =>
                r#"Unpacking **kwargs in "field()" is not supported"#.to_string(),
            DataclassAttributeMayOnlyBeOverriddenByAnotherAttribute =>
                "Dataclass attribute may only be overridden by another attribute".to_string(),
            DataclassPlusExplicitSlots { class_name } => format!(
                r#""{class_name}" both defines "__slots__" and is used with "slots=True""#
            ),

            FunctionIsDynamic => "Function is missing a type annotation".to_string(),
            FunctionMissingReturnAnnotation { hint_return_none } => {
                if *hint_return_none {
                    additional_notes.push(r#"Use "-> None" if function does not return a value"#.into());
                }
                "Function is missing a return type annotation".to_string()
            }
            FunctionMissingParamAnnotations =>
                "Function is missing a type annotation for one or more arguments".to_string(),
            CallToUntypedFunction{name} => format!(
                "Call to untyped function \"{name}\" in typed context"
            ),
            MissingTypeParameters { name } => format!(
                r#"Missing type parameters for generic type "{name}""#
            ),
            UntypedDecorator { name } => format!(
                r#"Untyped decorator makes function "{name}" untyped"#
            ),
            UntypedFunctionAfterDecorator { got } => match got {
                Some(got) => format!(r#"Type of decorated function contains type "Any" ("{got}")"#),
                None => "Function is untyped after decorator transformation".to_string(),
            },
            DisallowedAnySubclass{class} => format!(
                r#"Class cannot subclass "{class}" (has type "Any")"#
            ),
            DisallowedAnyMetaclass{class} => format!(
                r#"Class cannot use "{class}" as a metaclass (has type "Any")"#
            ),
            DisallowedAnyExplicit => r#"Explicit "Any" is not allowed"#.to_string(),
            UnimportedTypeBecomesAny { prefix, type_ } => format!(
                r#"{prefix} becomes "{type_}" due to an unfollowed import"#,
            ),
            DisallowedAnyExpr { type_ } => match type_.as_ref() {
                "Any" => r#"Expression has type "Any""#.to_string(),
                _ => format!(r#"Expression type contains "Any" ("{type_}")"#),
            },
            UnreachableStatement => "Statement is unreachable".to_string(),
            RightOperandIsNeverOperated { right } => format!(
                r#"Right operand of "{right}" is never evaluated"#
            ),
            RedundantCast { to } => format!(r#"Redundant cast to "{to}""#),
            ReturnedAnyWarning { expected } => format!(
                r#"Returning Any from function declared to return "{expected}""#
            ),
            NonOverlappingEqualityCheck { left_type, right_type } => format!(
                r#"Non-overlapping equality check (left operand type: "{left_type}", right operand type: "{right_type}")"#
            ),
            NonOverlappingIdentityCheck { left_type, right_type } => format!(
                r#"Non-overlapping identity check (left operand type: "{left_type}", right operand type: "{right_type}")"#
            ),
            NonOverlappingContainsCheck { element_type, container_type } => format!(
                r#"Non-overlapping container check (element type: "{element_type}", container item type: "{container_type}")"#
            ),
            UnimportedRevealType => {
                let module = if self.db.project.flags.python_version < PythonVersion::new(3, 11) {
                    "typing_extensions"
                } else {
                    "typing"
                };
                additional_notes.push(format!(
                    "Did you forget to import it from \"{module}\"? \
                     (Suggestion: \"from {module} import reveal_type\")"
                ));
                r#"Name "reveal_type" is not defined"#.to_string()
            }

            OnlyClassTypeApplication => {
                "Type application is only supported for generic classes".to_string()
            }
            TooFewValuesToUnpack{actual, expected} => match actual {
                1 => format!("Need more than {actual} value to unpack ({expected} expected)"),
                _ => format!("Need more than {actual} values to unpack ({expected} expected)"),
            },
            TooManyValuesToUnpack{actual, expected} =>
                format!("Too many values to unpack ({expected} expected, {actual} provided)"),
            VariadicTupleUnpackingRequiresStarTarget =>
                "Variadic tuple unpacking requires a star target".to_string(),
            TooManyAssignmentTargetsForVariadicUnpack =>
                "Too many assignment targets for variadic unpack".to_string(),
            UnpackingAStringIsDisallowed => "Unpacking a string is disallowed".to_string(),
            StarredExpressionOnlyNoTarget =>
                "can't use starred expression here".to_string(),
            BreakOutsideLoop => "\"break\" outside loop".to_string(),
            ContinueOutsideLoop => "\"continue\" outside loop".to_string(),
            StmtOutsideFunction{keyword} => format!("{keyword:?} outside function"),
            YieldOrYieldFromInsideComprehension { keyword } => format!(
                "{keyword:?} inside comprehension or generator expression"
            ),
            AwaitOutsideFunction => r#""await" outside function"#.to_string(),
            AwaitOutsideCoroutine => r#""await" outside coroutine ("async def")"#.to_string(),
            YieldFromInAsyncFunction => r#""yield from" in async function"#.to_string(),
            ReturnInAsyncGenerator => r#""return" with value in async generator is not allowed"#.to_string(),
            NonlocalAtModuleLevel => "nonlocal declaration not allowed at module level".to_string(),
            NonlocalNoBindingFound { name } => format!(r#"No binding for nonlocal "{name}" found"#),
            NonlocalAndGlobal { name } => format!(r#"Name "{name}" is nonlocal and global"#),
            NameDefinedInLocalScopeBeforeNonlocal { name } => format!(
                r#"Name "{name}" is already defined in local scope before nonlocal declaration"#
            ),
            InvalidBaseClass => format!("Invalid base class {:?}", self.code_under_issue()),
            CannotInheritFromFinalClass { class_name } => format!(
                r#"Cannot inherit from final class "{class_name}""#
            ),
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
            NewTypeInvalidType => "Argument 2 to NewType(...) must be a valid type".to_string(),
            NewTypeMustBeSubclassable{got} => format!(
                "Argument 2 to NewType(...) must be subclassable (got \"{got}\")"
            ),
            SubclassOfFinalCannotExist { final_class, other_class } => format!(
                r#"Subclass of "{final_class}" and "{other_class}" cannot exist: "{final_class}" is final"#
            ),
            NewTypeCannotUseProtocols => "NewType cannot be used with protocol classes".to_string(),
            BasesOfProtocolMustBeProtocol => "All bases of a protocol must be protocols".to_string(),
            MustHaveOneArgument { name } => format!(
                "{name} must have exactly one type argument"
            ),
            TypeCannotContainAnotherType =>
                "Type[...] can't contain another Type[...]".to_string(),
            InvalidRecursiveTypeAliasUnionOfItself { target } => format!(
                "Invalid recursive alias: a {target} item of itself"
            ),
            InvalidRecursiveTypeAliasTypeVarNesting =>
                "Invalid recursive alias: type variable nesting on right hand side".to_string(),
            RecursiveTypesNotAllowedInFunctionScope { alias_name } => {
                additional_notes.push("Recursive types are not allowed at function scope".to_string());
                format!(r#"Cannot resolve name "{alias_name}" (possible cyclic definition)"#)
            }

            FinalTooManyArguments => "Final[...] takes at most one type argument".to_string(),
            FinalNameMustBeInitializedWithValue => "Final name must be initialized with a value".to_string(),
            FinalInWrongPlace =>
                "Final can be only used as an outermost qualifier in a variable annotation".to_string(),
            FinalWithoutInitializerAndType =>
                "Type in Final[...] can only be omitted if there is an initializer".to_string(),
            FinalInClassBodyCannotDependOnTypeVariables =>
                "Final name declared in class body cannot depend on type variables".to_string(),
            FinalAndClassVarUsedBoth =>
                "Variable should not be annotated with both ClassVar and Final".to_string(),
            FinalCanOnlyBeUsedInMethods =>
                "@final cannot be used with non-method functions".to_string(),
            FinalShouldBeAppliedOnlyToOverloadImplementation =>
                "@final should be applied only to overload implementation".to_string(),
            FinalInStubMustBeAppliedToFirstOverload =>
                "In a stub file @final must be applied only to the first overload".to_string(),
            NeedTypeArgumentForFinalInDataclass =>
                "Need type argument for Final[...] with non-literal default in dataclass".to_string(),

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
            TypeVarInvalidDefault => "TypeVar \"default\" must be a type".to_string(),
            TypeVarTupleInvalidDefault =>
                "The default argument to TypeVarTuple must be an Unpacked tuple".to_string(),
            ParamSpecInvalidDefault =>
                "The default argument to ParamSpec must be a list expression, ellipsis, or a ParamSpec".to_string(),
            TypeVarDefaultMustBeASubtypeOfBound =>
                "TypeVar default must be a subtype of the bound type".to_owned(),
            TypeVarDefaultMustBeASubtypeOfConstraints =>
                "TypeVar default must be one of the constraint types".to_owned(),
            VarNameMismatch{class_name, string_name, variable_name} => format!(
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
            SelfTypeOutsideOfClass =>
                "Self type is only allowed in annotations within class definition".to_string(),
            InvalidClassMethodFirstArgument{argument_type, function_name, callable} => format!(
                "Invalid self argument \"{argument_type}\" to class attribute function \"{function_name}\" with type \"{callable}\""
            ),
            InvalidClassmethodAndStaticmethod =>
                "Cannot have both classmethod and staticmethod".to_string(),
            UsedWithANonMethod{name} => format!(r#""{name}" used with a non-method"#),
            UnexpectedComprehension => "Unexpected comprehension".to_string(),
            AmbigousClassVariableAccess =>
                "Access to generic instance variables via class is ambiguous".to_string(),
            SlotsConflictWithClassVariableAccess { name } => format!(
                r#""{name}" in __slots__ conflicts with class variable access"#
            ),
            CannotInstantiateProtocol{name} => format!(
                "Cannot instantiate protocol class \"{name}\""
            ),
            OnlyConcreteClassAllowedWhereTypeExpected { type_ } => format!(
                r#"Only concrete class can be given where "{type_}" is expected"#
            ),
            UnpackRequiresExactlyOneArgument =>
                "Unpack[...] requires exactly one type argument".to_string(),
            UnpackOnlyValidInVariadicPosition => "Unpack is only valid in a variadic position".to_string(),
            VariadicUnpackMustBeTupleLike { actual } => format!(
                r#""{actual}" cannot be unpacked (must be tuple or TypeVarTuple)"#
            ),
            MoreThanOneUnpackTypeIsNotAllowed =>
                "More than one Unpack in a type is not allowed".to_string(),
            VariadicUnpackMustBeTupleOrTypeVarTuple { type_ } => format!(
                r#""{type_}" cannot be unpacked (must be tuple or TypeVarTuple)"#
            ),
            TypeVarTupleCannotBeSplit => "TypeVarTuple cannot be split".to_string(),

            CannotUseIsinstanceWith { func, with } => format!("Cannot use {func}() with {with} type"),
            CannotUseIsinstanceWithParametrizedGenerics =>
                "Parameterized generics cannot be used with class or instance checks".to_string(),

            InvalidAssertType { actual, wanted } => format!(
                r#"Expression is of type "{actual}", not "{wanted}""#
            ),
            AssertionAlwaysTrueBecauseOfParentheses => "Assertion is always true, perhaps remove parentheses?".to_string(),

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
            OverloadOrderMustMatchSupertype { name, base_class } => {
                additional_notes.push(format!(
                    r#"Overload variants must be defined in the same order as they are in "{base_class}""#
                ));
                format!(r#"Signature of "{name}" incompatible with supertype "{base_class}""#)
            }
            ReturnTypeIncompatibleWithSupertype { message, async_note } => {
                if let Some(async_note) = async_note {
                    additional_notes.push(async_note.clone().into());
                    additional_notes.push(
                        "See https://mypy.readthedocs.io/en/stable/more_types.html#asynchronous-iterators".into()
                    )
                }
                message.clone()
            }
            ArgumentIncompatibleWithSupertype { message, eq_class, add_liskov_note } => {
                if *add_liskov_note {
                    additional_notes.push("This violates the Liskov substitution principle".into());
                    additional_notes.push("See https://mypy.readthedocs.io/en/stable/common_issues.html#incompatible-overrides".into());
                }
                if let Some(class_name) = eq_class {
                    additional_notes.push(r#"It is recommended for "__eq__" to work with arbitrary objects, for example:"#.into());
                    additional_notes.push(r#"    def __eq__(self, other: object) -> bool:"#.into());
                    additional_notes.push(format!(r"        if not isinstance(other, {class_name}):"));
                    additional_notes.push(r#"            return NotImplemented"#.into());
                    additional_notes.push(format!(r#"        return <logic to compare two {class_name} instances>"#));
                }
                message.clone().into()
            }
            MultipleInheritanceIncompatibility { name, class1, class2 } => format!(
                "Definition of \"{name}\" in base class \"{class1}\" is incompatible \
                 with definition in base class \"{class2}\""
            ),
            MissingBaseForOverride { name } => format!(
                r#"Method "{name}" is marked as an override, but no base method was found with this name"#
            ),
            InvalidSignature { signature } => format!(r#"Invalid signature "{signature}""#),
            OperatorSignaturesAreUnsafelyOverlapping { reverse_name, reverse_class, forward_class } => {
                let normal_name = OVERLAPPING_REVERSE_TO_NORMAL_METHODS[reverse_name.as_ref()];
                format!(r#"Signatures of "__{reverse_name}__" of "{reverse_class}" and "{normal_name}" of "{forward_class}" are unsafely overlapping"#)
            }
            ForwardOperatorIsNotCallable { forward_name } => format!(
                r#"Forward operator "{forward_name}" is not callable"#
            ),
            SignaturesAreIncompatible { name1, name2 } => format!(
                r#"Signatures of "{name1}" and "{name2}" are incompatible"#
            ),
            NewMustReturnAnInstance { got } => format!(
                "\"__new__\" must return a class instance (got \"{got}\")"
            ),
            NewIncompatibleReturnType { returns, must_return } => format!(
                "Incompatible return type for \"__new__\" (returns \
                 \"{returns}\", but must return a subtype of \"{must_return}\")"
            ),
            MustReturnNone { function_name } => format!(
                r#"The return type of "{function_name}" must be None"#
            ),
            IncorrectExitReturn => {
                additional_notes.push(r#"Use "typing_extensions.Literal[False]" as the return type or change it to "None""#.to_string());
                additional_notes.push(r#"If return type of "__exit__" implies that it may return True, the context manager may swallow exceptions"#.to_string());
                r#""bool" is invalid as return type for "__exit__" that always returns False"#.to_owned()
            }
            InvalidSpecialMethodSignature { type_, special_method } => format!(
                r#"Invalid signature "{type_}" for "{special_method}""#
            ),
            GetattributeInvalidAtModuleLevel =>
                "__getattribute__ is not valid at the module level".to_string(),
            InvalidSlotsDefinition { actual } => format!(
                r#"Invalid type for "__slots__" (actual type "{actual}", expected type "str | Iterable[str]")"#
            ),
            ProtocolMembersMustHaveExplicitlyDeclaredTypes =>
                "All protocol members must have explicitly declared types".to_string(),
            ProtocolMembersCannotHaveSelfVariableDefinitions =>
                "Protocol members cannot be defined via assignment to self".to_string(),
            ProtocolWrongVariance { type_var_name, actual_variance, expected_variance } => format!(
                r#"{} type variable "{type_var_name}" used in protocol where {} one is expected"#,
                actual_variance.name(),
                expected_variance.name(),
            ),
            CannotOverrideClassVariableWithInstanceVariable { base_class } => format!(
                r#"Cannot override class variable (previously declared on base class "{base_class}") with instance variable"#
            ),
            CannotOverrideInstanceVariableWithClassVariable { base_class } => format!(
                r#"Cannot override instance variable (previously declared on base class "{base_class}") with class variable"#
            ),
            CannotOverrideFinalAttribute { name, base_class } => format!(
                r#"Cannot override final attribute "{name}" (previously declared in base class "{base_class}")"#
            ),
            ExplicitOverrideFlagRequiresOverride { method, class } => format!(
                r#"Method "{method}" is not using @override but is overriding a method in class "{class}""#
            ),

            BaseExceptionExpected =>
                "Exception type must be derived from BaseException (or be a \
                 tuple of exception classes)".to_string(),
            BaseExceptionExpectedForRaise =>
                "Exception must be derived from BaseException".to_string(),
            ExceptStarIsNotAllowedToBeAnExceptionGroup =>
                "Exception type in except* cannot derive from BaseExceptionGroup".to_string(),

            TypeGuardFunctionsMustHaveArgument { name } => format!(
                "{name} functions must have a positional argument"
            ),
            TypeIsNarrowedTypeIsNotSubtypeOfInput { narrowed_t, input_t} => format!(
                r#"Narrowed type "{narrowed_t}" is not a subtype of input type "{input_t}""#
            ),

            TupleIndexOutOfRange { variadic_max_len } => {
                if let Some(len) = variadic_max_len {
                    additional_notes.push(format!("Variadic tuple can have length {len}"));
                }
                "Tuple index out of range".to_string()
            }
            TupleSliceStepCannotBeZero => "slice step cannot be zero".to_string(),
            AmbigousSliceOfVariadicTuple => "Ambiguous slice of a variadic tuple".to_string(),
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
            NamedTupleGenericInClassDefinition => {
                additional_notes.push("Use either Python 3 class syntax, or the assignment syntax".into());
                "Generic named tuples are not supported for legacy class syntax".to_string()
            }
            NamedTupleShouldBeASingleBase => "NamedTuple should be a single base".to_string(),
            NamedTupleSelfNotAllowed => "Self type cannot be used in NamedTuple item type".to_string(),

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
            TypedDictBasesMustBeTypedDicts =>
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
            TypedDictArgumentNameOverlapWithUnpack { names } => format!(
                r#"Overlap between argument names and ** TypedDict items: {names}"#
            ),
            UnpackItemInStarStarMustBeTypedDict =>
                "Unpack item in ** argument must be a TypedDict".to_string(),
            TypedDictSetdefaultWrongDefaultType { got, expected } => format!(
                r#"Argument 2 to "setdefault" of "TypedDict" has incompatible type "{got}"; expected "{expected}""#,
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
            ReadOnlyPropertyCannotOverwriteReadWriteProperty =>
                "Read-only property cannot override read-write property".to_string(),
            OnlyInstanceMethodsCanBeDecoratedWithProperty =>
                "Only instance methods can be decorated with @property".to_string(),
            OnlySupportedTopDecoratorSetter{name} =>
                format!("Only supported top decorator is @{name}.setter"),
            UnexpectedDefinitionForProperty{name} =>
                format!("Unexpected definition for property \"{name}\""),
            PropertyIsReadOnly{class_name, property_name} => format!(
                "Property \"{property_name}\" defined in \"{class_name}\" is read-only"
            ),

            InvariantNote{actual, maybe} => {
                kind = "note";
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
                kind = "note";
                "By default the bodies of untyped functions are not checked, \
                 consider using --check-untyped-defs".to_string()
            }
            Note(s) => {
                kind = "note";
                s.clone().into()
            }
        };
        let mut result = fmt_line(config, path, line_column, self.end_position(), kind, &error);
        if config.show_error_codes {
            if let Some(mypy_error_code) = self.issue.kind.mypy_error_code() {
                result += &format!("  [{mypy_error_code}]");
            }
        }
        for note in additional_notes {
            result += "\n";
            result += &fmt_line(
                config,
                path,
                line_column,
                self.end_position(),
                "note",
                &note,
            );
        }
        result
    }
}

fn fmt_line(
    config: &DiagnosticConfig,
    path: &str,
    (line, column): (usize, usize),
    end_position: TreePosition,
    type_: &str,
    error: &str,
) -> String {
    let mut line_number_infos = String::with_capacity(32);
    let mut add_part = |n| line_number_infos.push_str(&format!(":{n}"));
    add_part(line);
    if config.show_column_numbers {
        add_part(column);
    }
    if config.show_error_end {
        let (line, column) = end_position.line_and_column();
        add_part(line);
        if config.show_column_numbers {
            add_part(column);
        }
    }
    format!("{path}{line_number_infos}: {type_}: {error}")
}

impl std::fmt::Debug for Diagnostic<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", &self.as_string(&DiagnosticConfig::default()))
    }
}

#[derive(Default)]
pub struct DiagnosticConfig {
    pub show_error_codes: bool,
    pub show_error_end: bool,
    pub show_column_numbers: bool,
}

impl DiagnosticConfig {
    pub(crate) fn should_be_reported(&self, flags: &TypeCheckerFlags, type_: &IssueKind) -> bool {
        if !flags.disabled_error_codes.is_empty() {
            let should_not_report = |code| {
                if let Some(code) = code {
                    if flags.disabled_error_codes.iter().any(|c| c == code)
                        && !flags.enabled_error_codes.iter().any(|c| c == code)
                    {
                        return true;
                    }
                }
                false
            };
            if should_not_report(type_.mypy_error_code()) {
                return false;
            }
            if should_not_report(type_.mypy_error_supercode()) {
                return false;
            }
        }
        true
    }
}

#[derive(Default, Clone)]
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
                let e = issue.kind.mypy_error_code();
                let super_ = issue.kind.mypy_error_supercode();
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
                kind: IssueKind::Note(
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

pub fn has_known_types_package(name: &str) -> Option<&str> {
    lazy_static::lazy_static! {
        // This list is simply copied from Mypy
        static ref KNOWN_STUBS: HashMap<&'static str, &'static str> = HashMap::from([
            // Part of mypy.stubinfo.legacy_bundled_packages
            ("aiofiles", "types-aiofiles"),
            ("bleach", "types-bleach"),
            ("boto", "types-boto"),
            ("cachetools", "types-cachetools"),
            ("click_spinner", "types-click-spinner"),
            ("contextvars", "types-contextvars"),
            ("croniter", "types-croniter"),
            ("dataclasses", "types-dataclasses"),
            ("dateparser", "types-dateparser"),
            ("dateutil", "types-python-dateutil"),
            ("decorator", "types-decorator"),
            ("deprecated", "types-Deprecated"),
            ("docutils", "types-docutils"),
            ("first", "types-first"),
            ("gflags", "types-python-gflags"),
            ("google.protobuf", "types-protobuf"),
            ("markdown", "types-Markdown"),
            ("mock", "types-mock"),
            ("OpenSSL", "types-pyOpenSSL"),
            ("paramiko", "types-paramiko"),
            ("pkg_resources", "types-setuptools"),
            ("polib", "types-polib"),
            ("pycurl", "types-pycurl"),
            ("pymysql", "types-PyMySQL"),
            ("pyrfc3339", "types-pyRFC3339"),
            ("python2", "types-six"),
            ("pytz", "types-pytz"),
            ("pyVmomi", "types-pyvmomi"),
            ("redis", "types-redis"),
            ("requests", "types-requests"),
            ("retry", "types-retry"),
            ("simplejson", "types-simplejson"),
            ("singledispatch", "types-singledispatch"),
            ("six", "types-six"),
            ("slugify", "types-python-slugify"),
            ("tabulate", "types-tabulate"),
            ("toml", "types-toml"),
            ("typed_ast", "types-typed-ast"),
            ("tzlocal", "types-tzlocal"),
            ("ujson", "types-ujson"),
            ("waitress", "types-waitress"),
            ("yaml", "types-PyYAML"),
            // Part of mypy.stubinfo.non_bundled_packages
            ("MySQLdb", "types-mysqlclient"),
            ("PIL", "types-Pillow"),
            ("PyInstaller", "types-pyinstaller"),
            ("Xlib", "types-python-xlib"),
            ("aws_xray_sdk", "types-aws-xray-sdk"),
            ("babel", "types-babel"),
            ("backports.ssl_match_hostname", "types-backports.ssl_match_hostname"),
            ("braintree", "types-braintree"),
            ("bs4", "types-beautifulsoup4"),
            ("bugbear", "types-flake8-bugbear"),
            ("caldav", "types-caldav"),
            ("cffi", "types-cffi"),
            ("chevron", "types-chevron"),
            ("colorama", "types-colorama"),
            ("commonmark", "types-commonmark"),
            ("consolemenu", "types-console-menu"),
            ("crontab", "types-python-crontab"),
            ("d3dshot", "types-D3DShot"),
            ("dockerfile_parse", "types-dockerfile-parse"),
            ("docopt", "types-docopt"),
            ("editdistance", "types-editdistance"),
            ("entrypoints", "types-entrypoints"),
            ("farmhash", "types-pyfarmhash"),
            ("flake8_2020", "types-flake8-2020"),
            ("flake8_builtins", "types-flake8-builtins"),
            ("flake8_docstrings", "types-flake8-docstrings"),
            ("flake8_plugin_utils", "types-flake8-plugin-utils"),
            ("flake8_rst_docstrings", "types-flake8-rst-docstrings"),
            ("flake8_simplify", "types-flake8-simplify"),
            ("flake8_typing_imports", "types-flake8-typing-imports"),
            ("flask_cors", "types-Flask-Cors"),
            ("flask_migrate", "types-Flask-Migrate"),
            ("fpdf", "types-fpdf2"),
            ("gdb", "types-gdb"),
            ("google.cloud.ndb", "types-google-cloud-ndb"),
            ("hdbcli", "types-hdbcli"),
            ("html5lib", "types-html5lib"),
            ("httplib2", "types-httplib2"),
            ("humanfriendly", "types-humanfriendly"),
            ("invoke", "types-invoke"),
            ("jack", "types-JACK-Client"),
            ("jmespath", "types-jmespath"),
            ("jose", "types-python-jose"),
            ("jsonschema", "types-jsonschema"),
            ("keyboard", "types-keyboard"),
            ("ldap3", "types-ldap3"),
            ("nmap", "types-python-nmap"),
            ("oauthlib", "types-oauthlib"),
            ("openpyxl", "types-openpyxl"),
            ("opentracing", "types-opentracing"),
            ("paho.mqtt", "types-paho-mqtt"),
            ("parsimonious", "types-parsimonious"),
            ("passlib", "types-passlib"),
            ("passpy", "types-passpy"),
            ("peewee", "types-peewee"),
            ("pep8ext_naming", "types-pep8-naming"),
            ("playsound", "types-playsound"),
            ("psutil", "types-psutil"),
            ("psycopg2", "types-psycopg2"),
            ("pyaudio", "types-pyaudio"),
            ("pyautogui", "types-PyAutoGUI"),
            ("pycocotools", "types-pycocotools"),
            ("pyflakes", "types-pyflakes"),
            ("pygments", "types-Pygments"),
            ("pyi_splash", "types-pyinstaller"),
            ("pynput", "types-pynput"),
            ("pythoncom", "types-pywin32"),
            ("pythonwin", "types-pywin32"),
            ("pyscreeze", "types-PyScreeze"),
            ("pysftp", "types-pysftp"),
            ("pytest_lazyfixture", "types-pytest-lazy-fixture"),
            ("pywintypes", "types-pywin32"),
            ("regex", "types-regex"),
            ("send2trash", "types-Send2Trash"),
            ("slumber", "types-slumber"),
            ("stdlib_list", "types-stdlib-list"),
            ("stripe", "types-stripe"),
            ("toposort", "types-toposort"),
            ("tqdm", "types-tqdm"),
            ("tree_sitter", "types-tree-sitter"),
            ("tree_sitter_languages", "types-tree-sitter-languages"),
            ("ttkthemes", "types-ttkthemes"),
            ("vobject", "types-vobject"),
            ("whatthepatch", "types-whatthepatch"),
            ("win32", "types-pywin32"),
            ("win32api", "types-pywin32"),
            ("win32con", "types-pywin32"),
            ("win32com", "types-pywin32"),
            ("win32comext", "types-pywin32"),
            ("win32gui", "types-pywin32"),
            ("xmltodict", "types-xmltodict"),
            ("zxcvbn", "types-zxcvbn"),
            ("pandas", "pandas-stubs"),
            ("lxml", "lxml-stubs"),
        ]);
    };
    KNOWN_STUBS.get(name).copied()
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_sizes() {
        use std::mem::size_of;

        use super::*;
        assert_eq!(size_of::<IssueKind>(), 56);
    }
}
