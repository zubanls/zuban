use std::{collections::HashMap, io::Write, sync::Arc};

use colored::{ColoredString, Colorize as _};
use config::DiagnosticConfig;
use parsa_python_cst::{CodeIndex, NodeIndex, Tree};
use utils::InsertOnlyVec;

use crate::{
    PythonVersion, TypeCheckerFlags,
    database::{Database, PointLink},
    file::{File, GenericCounts, OVERLAPPING_REVERSE_TO_NORMAL_METHODS, PythonFile},
    lines::PositionInfos,
    node_ref::NodeRef,
    type_::{TypeVarLike, Variance},
    utils::join_with_commas,
};

// Ord/PartialOrd are not important, but we ideally have something to support by IssueKind entry to
// know which issue arises often. Since there is no other way to get the "current" entry so we can
// sort by that
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
#[allow(dead_code)]  // TODO remove this
#[rustfmt::skip]  // This is way more readable if we are not auto-formatting this.
pub(crate) enum IssueKind {
    InvalidSyntax,
    InvalidSyntaxInTypeComment { type_comment: Box<str> },
    InvalidSyntaxInTypeAnnotation,
    StarExceptionWithoutTypingSupport,
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
    ReadingDeletedVariable,
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
    YieldFromIncompatibleSendTypes { got: Box<str>, expected: Box<str> },
    YieldFromCannotBeApplied { to: Box<str> },
    YieldValueExpected,
    IncompatibleAssignment { got: Box<str>, expected: Box<str> },
    IncompatibleImportAssignment { name: Box<str>, got: Box<str>, expected: Box<str> },
    IncompatiblePatternAssignment { got: Box<str>, expected: Box<str> },
    IncompatibleDataclassTransformConverterAssignment { got: Box<str>, expected: Box<str> },
    CannotAssignToClassVarViaInstance { name: Box<str> },
    CannotAssignToAMethod,
    CannotAssignToFinal { name: Box<str>, is_attribute: bool },
    AssigningToNameOutsideOfSlots { name: Box<str>, class: Box<str> },
    ListItemMismatch { item: usize, got: Box<str>, expected: Box<str> },
    ListComprehensionMismatch { got: Box<str>, expected: Box<str> },
    SetItemMismatch { item: usize, got: Box<str>, expected: Box<str> },
    SetComprehensionMismatch { got: Box<str>, expected: Box<str> },
    GeneratorComprehensionMismatch { got: Box<str>, expected: Box<str> },
    DictComprehensionMismatch { part: &'static str, got: Box<str>, expected: Box<str> },
    DictMemberMismatch { item: usize, got_pair: Box<str>, expected_pair: Box<str> },
    UnpackedDictMemberMismatch { item: usize, got: Box<str>, expected: Box<str> },
    CannotInferLambdaParams,
    NeedTypeAnnotation { for_: Box<str>, hint: Option<&'static str> },
    CannotDetermineType { for_: Box<str> },
    Deprecated { identifier: Box<str>, reason: Arc<Box<str>>},

    Redefinition { name: Box<str>, suffix: Box<str>, is_self_attribute: bool },
    CannotRedefineAs { name: Box<str>, as_: &'static str },
    CannotRedefineAsFinal,
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
    UnpackNotIterable { type_: Box<str> },
    NotIterableMissingIter { type_: Box<str> },
    NotIterableMissingIterInUnion { object: Box<str>, union: Box<str> },
    AsyncNotIterable { type_: Box<str> },
    IterableExpectedAsVariadicArgs,
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
    InvalidAssignmentTarget,
    UnpackingAStringIsDisallowed,
    StarredExpressionOnlyNoTarget,
    BreakOutsideLoop,
    ContinueOutsideLoop,
    StmtOutsideFunction { keyword: &'static str },
    AsyncOutsideAsyncFunction { keyword: &'static str },
    YieldOrYieldFromInsideComprehension { keyword: &'static str },
    AwaitOutsideFunction,
    AwaitOutsideCoroutine,
    YieldFromInAsyncFunction,
    ReturnInAsyncGenerator,
    NonlocalAtModuleLevel,
    NonlocalNoBindingFound { name: Box<str> },
    NonlocalBindingDisallowedForTypeParams { name: Box<str> },
    GlobalAtModuleLevel,
    NonlocalAndGlobal { name: Box<str> },
    NameAssignedBeforeGlobalDeclaration { name: Box<str> },
    NameDefinedInLocalScopeBeforeNonlocal { name: Box<str> },
    OnlyClassTypeApplication,
    InvalidBaseClass,
    TypeAliasSyntaxInBaseClassIsInvalid,
    TypeAliasSyntaxInFunction,
    CannotInheritFromFinalClass { class_name: Box<str> },
    FinalClassHasAbstractAttributes { class_name: Box<str>, attributes: Box<str> },
    FinalMethodIsAbstract { name: Box<str> },
    ClassNeedsAbcMeta { class_name: Box<str>, attributes: Box<str> },
    IncompatibleBaseTuples,
    InvalidMetaclass,
    MetaclassMustInheritFromType,
    MetaclassConflict,
    CannotSubclassNewType,
    DuplicateBaseClass { name: Box<str> },
    InconsistentMro { name: Box<str> },
    CyclicDefinition { name: Box<str> },
    InvalidTypeCycle,
    CurrentlyUnsupportedBaseClassCycle,
    EnsureSingleGenericOrProtocol,
    GenericWithTypeParamsIsRedundant,
    ProtocolWithTypeParamsNoBracketsExpected,

    InvalidType(Box<str>),
    InvalidTypeDeclaration,
    ClassVarOnlyInAssignmentsInClass,
    ClassVarNestedInsideOtherType,
    ClassVarTooManyArguments,
    ClassVarCannotContainTypeVariables,
    ClassVarCannotContainSelfTypeInGenericClass,
    InvalidCallableParams,
    InvalidParamSpecGenerics { got: Box<str> },
    UseParamSpecArgs { name: Box<str> },
    UseParamSpecKwargs { name: Box<str> },
    ParamSpecParamsNeedBothStarAndStarStar { name: Box<str> },
    ParamSpecArgumentsNeedsBothStarAndStarStar { name: Box<str> },
    ParamSpecKwParamNotAllowed,
    ParamSpecComponentsNotAllowed,
    NewTypeCannotHaveTypeDeclaration,
    NewTypeInvalidType,
    NewTypeMustBeSubclassable { got: Box<str> },
    NewTypeCannotUseProtocols,
    NewTypesExpectSinglePositionalArgument,
    BasesOfProtocolMustBeProtocol,
    MustHaveOneArgument { name: &'static str },
    CannotContainType { name: &'static str },
    InvalidRecursiveTypeAliasUnionOfItself { target: &'static str },
    InvalidRecursiveTypeAliasTypeVarNesting,
    RecursiveTypesNotAllowedInFunctionScope { alias_name: Box<str> },
    RuntimeCheckableCanOnlyBeUsedWithProtocolClasses,
    ProtocolNotRuntimeCheckable,
    IssubcclassWithProtocolNonMethodMembers { protocol: Box<str>, non_method_members: Box<str> },
    TypeAliasRightSideNeeded,
    TypeAliasInTypeCommentNotSupported,

    FinalTooManyArguments,
    FinalNameMustBeInitializedWithValue,
    FinalInWrongPlace,
    WithoutInitializerAndType { kind: &'static str },
    FinalInClassBodyCannotDependOnTypeVariables,
    FinalAndClassVarUsedBoth,
    FinalCanOnlyBeUsedInMethods,
    ShouldBeAppliedOnlyToOverloadImplementation { kind: &'static str },
    InStubMustBeAppliedToFirstOverload { kind: &'static str },
    NeedTypeArgumentForFinalInDataclass,
    ProtocolMemberCannotBeFinal,
    FinalAttributeOnlyValidInClassBodyOrInit,
    FinalInLoopDisallowed,

    DuplicateTypeVar,
    UnboundTypeVarLike { type_var_like: TypeVarLike },
    TypeVarLikeBoundByOuterClass { type_var_like: TypeVarLike },
    TypeParametersShouldBeDeclared { type_var_like: TypeVarLike },
    IncompleteGenericOrProtocolTypeVars,
    TypeVarExpected { class: &'static str },
    FreeTypeVariableExpectInTypeAliasTypeTypeParams { is_unpack: bool },
    TypeVarBoundViolation { actual: Box<str>, of: Box<str>, expected: Box<str> },
    InvalidTypeVarValue { type_var_name: Box<str>, of: Box<str>, actual: Box<str> },
    TypeVarCoAndContravariant,
    TypeVarValuesAndUpperBound,
    TypeVarValuesNeedsAtLeastTwo,
    UnexpectedArgument { class_name: &'static str, argument_name: Box<str> },
    InvalidAssignmentForm { class_name: &'static str },
    TypeVarLikeTooFewArguments { class_name: &'static str },
    TypeVarLikeFirstArgMustBeString{ class_name: &'static str },
    TypeVarVarianceMustBeBool { argument: &'static str },
    TypeVarTypeExpected,
    TypeVarBoundMustBeType,
    TypeVarConstraintCannotHaveTypeVariables,
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
    ParamSpecKeywordArgumentWithoutDefinedSemantics,
    ParamSpecNestedSpecificationsNotAllowed,
    MultipleTypeVarTuplesInClassDef,
    BoundTypeVarInAlias { name: Box<str> },
    NestedConcatenate,
    ConcatenateLastParamNeedsToBeParamSpec,
    InvalidSelfArgument { argument_type: Box<str>, function_name: Box<str>, callable: Box<str> },
    NotAcceptingSelfArgument { function_name: Box<str>, callable: Box<str> },
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
    CannotInstantiateAbstractClass{ name: Box<str>, abstract_attributes: Box<[PointLink]> },
    OnlyConcreteClassAllowedWhereTypeExpected { type_: Box<str> },
    OnlyConcreteClassAllowedWhereTypeExpectedForVariable { type_: Box<str> },
    UnpackRequiresExactlyOneArgument,
    UnpackOnlyValidInVariadicPosition,
    VariadicUnpackMustBeTupleLike { actual: Box<str> },
    MoreThanOneUnpackTypeIsNotAllowed,
    TypeVarTupleCannotBeSplit,
    TypeVarDefaultWrongOrder { type_var1: Box<str>, type_var2: Box<str> },
    TypeVarDefaultTypeVarOutOfScope { type_var: Box<str> },
    AlreadyDefinedTypeParameter { name: Box<str> },
    DuplicateTypeVarInTypeAliasType { name: Box<str> },
    MultipleTypeVarTupleDisallowedInTypeParams { in_type_alias_type: bool },
    InvalidTypeVarOfOuterClass { name: Box<str> },
    TypeVarInferVarianceCannotSpecifyVariance { specified: &'static str },

    CannotUseIsinstanceWith { func: &'static str, with: &'static str },
    CannotUseIsinstanceWithParametrizedGenerics,

    InvalidAssertType { actual: Box<str>, wanted: Box<str> },
    AssertionAlwaysTrueBecauseOfParentheses,

    SuperUsedOutsideClass,
    SuperOutsideOfAMethod,
    SuperRequiresOneOrTwoPositionalArgumentsInEnclosingFunction,
    SuperWithSingleArgumentNotSupported,
    SuperVarargsNotSupported,
    SuperOnlyAcceptsPositionalArguments,
    SuperArgument1MustBeTypeObject { got: Box<str> },
    SuperArgument2MustBeAnInstanceOfArgument1,
    SuperUnsupportedArgument{argument_index: usize},
    SuperTargetClassHasNoBaseClass,
    UndefinedInSuperclass { name: Box<str> },
    CallToAbstractMethodViaSuper { method_name: Box<str>, class_name: Box<str> },

    IncompatibleAssignmentInSubclass { base_class: Box<str>, got: Box<str>, expected: Box<str> },
    SignatureIncompatibleWithSupertype { base_class: Box<str>, name: Box<str>, notes: Box<[Box<str>]> },
    OverloadOrderMustMatchSupertype { name: Box<str>, base_class: Box<str> },
    ReturnTypeIncompatibleWithSupertype { message: String, async_note: Option<Box<str>> },
    ArgumentIncompatibleWithSupertype { message: Box<str>, eq_class: Option<Box<str>>, add_liskov_note: bool },
    MultipleInheritanceIncompatibility { name: Box<str>, class1: Box<str>, class2: Box<str> },
    IncompatiblePropertySetterOverride { notes: Vec<String> },
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
    CannotOverrideWritableWithFinalAttribute { name: Box<str> },
    CannotOverrideWritableAttributeWithReadOnlyProperty { name: Box<str>, base_class: Box<str>, other_class: Box<str> },
    ExplicitOverrideFlagRequiresOverride { method: Box<str>, class: Box<str> },
    TotalOrderingMissingMethod,

    BaseExceptionExpected,
    BaseExceptionExpectedForRaise { did_you_mean: Option<Box<str>> },
    ExceptStarIsNotAllowedToBeAnExceptionGroup,

    ClassHasNoMatchArgs { class: Box<str> },
    TooManyPositionalPatternsForMatchArgs,
    ExpectedTypeInClassPattern { got: Box<str> },
    InvalidDunderMatchArgs,
    DuplicateKeywordPattern { name: Box<str> },

    IntersectionCannotExistDueToIncompatibleMethodSignatures { intersection: Box<str> },
    IntersectionCannotExistDueToFinalClass { intersection: Box<str>, final_class: Box<str> },
    IntersectionCannotExistDueToInconsistentMro { intersection: Box<str> },

    TypeGuardFunctionsMustHaveArgument { name: &'static str },
    TypeIsNarrowedTypeIsNotSubtypeOfInput { narrowed_t: Box<str>, input_t: Box<str> },

    TupleIndexOutOfRange { variadic_max_len: Option<usize> },
    TupleSliceStepCannotBeZero,  // Not in mypy
    AmbigousSliceOfVariadicTuple,
    NamedTupleExpectsStringLiteralAsFirstArg { name: &'static str },
    StringLiteralExpectedAsNamedTupleItem,
    InvalidStmtInNamedTuple,
    NamedTupleNonDefaultFieldFollowsDefault,
    NamedTupleFieldExpectsTupleOfStrAndType,
    NamedTupleInvalidAttributeOverride { name: Box<str> },
    InvalidSecondArgumentToNamedTuple { name: &'static str },
    UnexpectedArgumentsTo { name: &'static str },
    UnexpectedArgumentTo { name: &'static str },
    TupleExpectedAsNamedTupleField,
    FunctionalNamedTupleInvalidFieldName { name: &'static str, field_name: Box<str> },
    FunctionalNamedTupleNameUsedAKeyword { name: &'static str, field_name: Box<str> },
    FunctionalNamedTupleNameCannotStartWithUnderscore { name: &'static str, field_name: Box<str> },
    FunctionalNamedTupleDuplicateField { name: &'static str, field_name: Box<str> },
    NamedTupleNameCannotStartWithUnderscore { field_name: Box<str> },
    NamedTupleInvalidFieldName,
    NamedTupleFirstArgumentMismatch { should: Box<str>, is: Box<str> },
    NamedTupleExpectedBoolForRenameArgument,
    NamedTupleUnexpectedKeywordArgument { keyword_name: Box<str> },
    NamedTupleDefaultsShouldBeListOrTuple,
    NamedTupleToManyDefaults,
    NamedTupleGenericInClassDefinition,
    NamedTupleShouldBeASingleBase,
    NamedTupleSelfNotAllowed,
    NamedTupleAttributeCannotBeDeleted,

    TypedDictIncompatibleType { got: Box<str>, key: Box<str>, expected: Box<str> },
    TypedDictExtraKey { key: Box<str>, typed_dict: Box<str> },
    UnexpectedArgumentsToTypedDict,
    TypedDictFirstArgMustBeString,
    TypedDictSecondArgMustBeDict,
    TypedDictInvalidFieldName,
    TypedDictFieldModifierCannotBeNested { modifier: &'static str },
    TypedDictSelfNotAllowed,
    TypedDictNameMismatch { string_name: Box<str>, variable_name: Box<str> },
    TypedDictWrongArgumentsInConstructor,
    TypedDictKeysMustBeStringLiteral,
    TypedDictAccessKeyMustBeStringLiteral { keys: Box<str> },
    TypedDictKeySetItemIncompatibleType { key: Box<str>, got: Box<str>, expected: Box<str> },
    TypedDictHasNoKey { typed_dict: Box<str>, key: Box<str> },
    TypedDictHasNoKeyForGet { typed_dict: Box<str>, key: Box<str> },
    TypedDictKeyCannotBeDeleted { typed_dict: Box<str>, key: Box<str> },
    TypedDictReadOnlyKeyMutated { key: Box<str> },
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
    ArgumentMustBeTrueOrFalse { key: Box<str> },
    TypedDictCannotUseCloseIfSuperClassExtraItemsNonReadOnly,
    TypedDictCannotUseCloseFalseIfSuperClassClosed,
    TypedDictCannotUseCloseFalseIfSuperClassHasExtraItems,
    TypedDictExtraItemsCannotBe { kind: &'static str },
    TypedDictExtraItemsNonReadOnlyChangeDisallowed,
    TypedDictExtraItemsIncompatibleTypes { in_super_class: Box<str>, in_sub_class: Box<str> },
    TypedDictSetItemWithExtraItemsMismatch { got: Box<str>, expected: Box<str> },
    TypedDictMemberRequiredButHasExtraItemsOfSuper { name: Box<str> },
    TypedDictMemberReadOnlyButExtraItemsOfSuperClassIsNot { name: Box<str> },
    TypedDictMemberNotAssignableToExtraItemsOfSuperClass { name: Box<str>, in_super_class: Box<str>, member_type: Box<str> },

    OverloadMismatch { name: Box<str>, args: Box<[Box<str>]>, variants: Box<[Box<str>]> },
    OverloadImplementationNotLast,
    OverloadImplementationNeeded,
    OverloadStubImplementationNotAllowed,
    OverloadSingleNotAllowed,
    OverloadUnmatchable { unmatchable_signature_index: usize, matchable_signature_index: usize },
    OverloadIncompatibleReturnTypes { first_signature_index: usize, second_signature_index: usize },
    OverloadImplementationReturnTypeIncomplete { signature_index: usize },
    OverloadImplementationParamsNotBroadEnough { signature_index: usize },
    OverloadInconsistentKind { kind: &'static str },
    OverloadedPropertyNotSupported,
    OverloadWithAbstractAndNonAbstract,
    OverloadTooManyUnions,

    DecoratorOnTopOfPropertyNotSupported,
    ReadOnlyPropertyCannotOverwriteReadWriteProperty,
    ReadOnlyPropertyCannotOverwriteWritableAttribute,
    OnlyInstanceMethodsCanBeDecoratedWithProperty,
    OnlySupportedTopDecoratorSetter { name: Box<str> },
    InvalidPropertySetterSignature,
    UnexpectedDefinitionForProperty { name: Box<str> },
    PropertyIsReadOnly { class_name: Box<str>, property_name: Box<str> },

    MethodWithoutArguments,
    TypeOfSelfIsNotASupertypeOfItsClass { self_type: Box<str>, class: Box<str> },
    SelfArgumentMissing,
    MultipleStarredExpressionsInAssignment,

    EnumFirstArgMustBeString,
    EnumInvalidSecondArgument { enum_name: Box<str> },
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
    EnumMemberAnnotationDisallowed,

    DataclassCannotBe { kind: Box<str> },
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
    DataclassTransformUnknownParam { name: Box<str> },
    DataclassTransformFieldSpecifiersMustBeTuple,
    DataclassTransformFieldSpecifiersMustOnlyContainIdentifiers,
    DataclassTransformFieldAliasParamMustBeString,

    NegativeShiftCount,
    DivisionByZero,

    // From --disallow-untyped-defs
    FunctionIsUntyped,
    FunctionMissingReturnAnnotation { hint_return_none: bool }, // Also from --disallow-incomplete-defs
    FunctionMissingParamAnnotations, // Also from --disallow-incomplete-defs

    CallToUntypedFunction { name: Box<str> }, // From --disallow-untyped-calls
    CoroutineValueMustBeUsed { type_: Box<str> },
    AwaitableValueMustBeUsed { type_: Box<str> }, // From --enable-error-code unused-awaitable
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
            Note(_) | InvariantNote { .. } | InvalidDunderMatchArgs => return None,
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
            | NotIterableMissingIter { .. } => "attr-defined",
            NameError { .. } | TypeNotFound => "name-defined",
            Redefinition { .. } => "no-redef",
            NameUsedBeforeDefinition { .. } => "used-before-def",
            UnionAttributeError { .. }
            | UnionAttributeErrorOfUpperBound(..)
            | NotIterableMissingIterInUnion { .. } => "union-attr",
            ArgumentTypeIssue(_) | SuperArgument1MustBeTypeObject { .. } => "arg-type",
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
            | IncompatiblePatternAssignment { .. }
            | IncompatibleDataclassTransformConverterAssignment { .. }
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
            ModuleNotFound { module_name } => {
                if has_known_types_package(module_name).is_some() {
                    "import-untyped"
                } else {
                    "import-not-found"
                }
            }
            ListItemMismatch { .. } => "list-item",
            SetItemMismatch { .. } => "arg-type", // This has no error code in Mypy currently.
            DictMemberMismatch { .. } | UnpackedDictMemberMismatch { .. } => "dict-item",
            NewTypeMustBeSubclassable { .. } => "valid-newtype",
            OverloadImplementationNeeded => "no-overload-impl",
            OverloadMismatch { .. } => "call-overload",
            OverloadIncompatibleReturnTypes { .. } => "overload-overlap",
            OverloadUnmatchable { .. } => "overload-cannot-match",
            SignatureIncompatibleWithSupertype { .. }
            | ArgumentIncompatibleWithSupertype { .. }
            | OverloadOrderMustMatchSupertype { .. }
            | IncompatiblePropertySetterOverride { .. }
            | ReturnTypeIncompatibleWithSupertype { .. }
            | CannotOverrideWritableAttributeWithReadOnlyProperty { .. }
            | ReadOnlyPropertyCannotOverwriteWritableAttribute => "override",
            IncorrectExitReturn => "exit-return",
            FunctionIsUntyped
            | FunctionMissingReturnAnnotation { .. }
            | FunctionMissingParamAnnotations => "no-untyped-def",
            DoesNotReturnAValue(_) => "func-returns-value",
            CallToUntypedFunction { .. } => "no-untyped-call",
            CoroutineValueMustBeUsed { .. } => "unused-coroutine",
            AwaitableValueMustBeUsed { .. } => "unused-awaitable",
            AnnotationInUntypedFunction => "annotation-unchecked",
            AwaitOutsideFunction => "top-level-await",
            AwaitOutsideCoroutine => "await-not-async",
            NeedTypeAnnotation { .. } => "var-annotated",
            CannotDetermineType { .. } => "has-type",
            TypeIsNarrowedTypeIsNotSubtypeOfInput { .. } => "narrowed-type-not-subtype",
            DecoratorOnTopOfPropertyNotSupported => "prop-decorator",
            CannotInstantiateAbstractClass { .. } => "abstract",
            CallToAbstractMethodViaSuper { .. } => "safe-super",
            Deprecated { .. } => "deprecated",

            TypedDictNameMismatch { .. } | NamedTupleFirstArgumentMismatch { .. } => "name-match",
            TypedDictMissingKeys { .. }
            | TypedDictIncompatibleType { .. }
            | TypedDictKeySetItemIncompatibleType { .. }
            | TypedDictSetdefaultWrongDefaultType { .. }
            | TypedDictHasNoKeyForGet { .. } => "typeddict-item",
            TypedDictExtraKey { .. } | TypedDictHasNoKey { .. } => "typeddict-unknown-key",
            TypedDictReadOnlyKeyMutated { .. } => "typeddict-readonly-mutated",

            UnreachableStatement
            | RightOperandIsNeverOperated { .. }
            | IntersectionCannotExistDueToFinalClass { .. }
            | IntersectionCannotExistDueToIncompatibleMethodSignatures { .. }
            | IntersectionCannotExistDueToInconsistentMro { .. } => "unreachable",
            RedundantCast { .. } => "redundant-cast",
            ReturnedAnyWarning { .. } => "no-any-return",
            NonOverlappingEqualityCheck { .. }
            | NonOverlappingContainsCheck { .. }
            | NonOverlappingIdentityCheck { .. } => "comparison-overlap",
            UnimportedRevealType => "unimported-reveal",
            DisallowedAnyExplicit => "explicit-any",

            _ => "misc",
        })
    }

    fn mypy_error_supercode(&self) -> Option<&'static str> {
        // See also https://mypy.readthedocs.io/en/stable/error_codes.html#subcodes-of-error-codes
        use IssueKind::*;
        Some(match &self {
            TypedDictExtraKey { .. } | TypedDictHasNoKey { .. } => "typeddict-item",
            CannotAssignToAMethod => "assignment",
            ModuleNotFound { .. } => "import",
            OverloadUnmatchable { .. } | DecoratorOnTopOfPropertyNotSupported => "misc",
            _ => return None,
        })
    }

    pub(crate) fn should_be_reported(&self, flags: &TypeCheckerFlags) -> bool {
        if !flags.disabled_error_codes.is_empty() {
            let should_not_report = |code| {
                if let Some(code) = code
                    && flags.disabled_error_codes.iter().any(|c| c == code)
                    && !flags.enabled_error_codes.iter().any(|c| c == code)
                {
                    return true;
                }
                false
            };
            if should_not_report(self.mypy_error_code()) {
                return false;
            }
            if should_not_report(self.mypy_error_supercode()) {
                return false;
            }
        }
        true
    }
}

#[derive(Debug, Clone)]
pub(crate) struct Issue {
    pub kind: IssueKind,
    pub start_position: CodeIndex,
    pub end_position: CodeIndex,
    from_name_binder: bool,
}

impl Issue {
    pub(crate) fn from_node_index(
        tree: &Tree,
        node_index: NodeIndex,
        kind: IssueKind,
        from_name_binder: bool,
    ) -> Self {
        Self {
            kind,
            start_position: tree.node_start_position(node_index),
            end_position: tree.node_end_position_without_whitespace(node_index),
            from_name_binder,
        }
    }

    // This method implies it is NOT called by the name binder
    pub(crate) fn from_start_stop(
        start_position: CodeIndex,
        end_position: CodeIndex,
        kind: IssueKind,
    ) -> Self {
        Self {
            kind,
            start_position,
            end_position,
            from_name_binder: false,
        }
    }
}

// These roughly correspond to LSP DiagnosticSeverity:
// https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#diagnosticSeverity
#[derive(PartialEq, Eq)]
pub enum Severity {
    Error,
    Warning,
    Information,
    Hint,
}

pub struct Diagnostic<'db> {
    db: &'db Database,
    file: &'db PythonFile,
    pub(crate) issue: &'db Issue,
}

impl<'db> Diagnostic<'db> {
    pub(crate) fn new(db: &'db Database, file: &'db PythonFile, issue: &'db Issue) -> Self {
        Self { db, file, issue }
    }

    pub fn start_position(&self) -> PositionInfos<'db> {
        self.file
            .byte_to_position_infos(self.db, self.issue.start_position)
    }

    pub fn end_position(&self) -> PositionInfos<'db> {
        self.file
            .byte_to_position_infos(self.db, self.issue.end_position)
    }

    pub fn severity(&self) -> Severity {
        match &self.is_note() {
            false => Severity::Error,
            true => Severity::Information,
        }
    }

    fn is_note(&self) -> bool {
        match &self.issue.kind {
            IssueKind::Note(_)
            | IssueKind::InvariantNote { .. }
            | IssueKind::AnnotationInUntypedFunction
            | IssueKind::InvalidDunderMatchArgs => true,
            _ => false,
        }
    }

    fn code_under_issue(&self) -> &'db str {
        self.start_position().code_until(self.end_position())
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
            UnpackNotIterable { .. }
                | NotIterableMissingIter { .. }
                | NotIterableMissingIterInUnion { .. }
                | IterableExpectedAsVariadicArgs
                | AttributeError { .. }
                | OverloadUnmatchable { .. }
                | OverloadImplementationParamsNotBroadEnough { .. }
                | TypeVarInReturnButNotArgument
                | OnlyClassTypeApplication
                | UnsupportedClassScopedImport
                | CannotInheritFromFinalClass { .. }
                | InvalidAssertType { .. }
                | BaseExceptionExpected
                | BaseExceptionExpectedForRaise { .. }
                | TypeOfSelfIsNotASupertypeOfItsClass { .. }
                | SelfArgumentMissing
        )
    }

    pub(crate) fn message_with_notes(&self, additional_notes: &mut Vec<String>) -> String {
        use IssueKind::*;
        match &self.issue.kind {
            InvalidSyntax => "Invalid syntax".to_string(),
            InvalidSyntaxInTypeComment { type_comment } => format!(
                r#"Syntax error in type comment "{type_comment}""#
            ),
            InvalidSyntaxInTypeAnnotation => "Syntax error in type annotation".to_string(),
            StarExceptionWithoutTypingSupport => {
                additional_notes.push("Your --python-version is probably too low.".to_string());
                "Missing the typing symbols for star exceptions".to_string()
            }
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
            NameError{name} => format!(r#"Name "{name}" is not defined"#),
            ReadingDeletedVariable => format!(
                r#"Trying to read deleted variable "{}""#,
                self.code_under_issue()
            ),
            IncompatibleReturn{got, expected} => {
                format!(r#"Incompatible return value type (got "{got}", expected "{expected}")"#)
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
            YieldFromIncompatibleSendTypes { got, expected } => format!(
                r#"Incompatible send types in yield from (actual type "{got}", expected type "{expected}")"#
            ),
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
            IncompatiblePatternAssignment { got, expected } => format!(
                r#"Incompatible types in capture pattern (pattern captures type "{got}", variable has type "{expected}")"#,
            ),
            IncompatibleDataclassTransformConverterAssignment { got, expected } => format!(
                r#"Incompatible types in assignment of a dataclass converter (expression has type "{got}", expected type "{expected}")"#,
            ),
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
            SetItemMismatch{item, got, expected} => format!(
                "Set item {item} has incompatible type \"{got}\"; expected \"{expected}\"",
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
            CannotDetermineType { for_ } => format!(r#"Cannot determine type of "{for_}""#),
            Deprecated { identifier, reason: message } => format!(
                "{identifier} is deprecated: {message}"
            ),

            Redefinition{name, suffix, is_self_attribute } => match *is_self_attribute {
                false => format!(r#"Name "{name}" already defined {suffix}"#),
                true => format!(r#"Attribute "{name}" already defined {suffix}"#),
            },
            CannotRedefineAs { name, as_ } => format!(r#"Cannot redefine "{name}" as {as_}"#),
            CannotRedefineAsFinal => r#"Cannot redefine an existing name as final"#.to_string(),
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
            UnpackNotIterable{type_} => format!("{type_} object is not iterable"),
            NotIterableMissingIter { type_ } => format!(r#""{type_}" has no attribute "__iter__" (not iterable)"#),
            NotIterableMissingIterInUnion { object, union } => format!(
                r#"Item "{object}" of "{union}" has no attribute "__iter__" (not iterable)"#
            ),
            AsyncNotIterable{type_} => format!(
                r#""{type_}" has no attribute "__aiter__" (not async iterable)"#
            ),
            IterableExpectedAsVariadicArgs => "Expected iterable as variadic argument".to_string(),
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
            TypeOfSelfIsNotASupertypeOfItsClass { self_type, class } => format!(
                r#"The erased type of self "{self_type}" is not a supertype of its class "{class}""#
            ),
            SelfArgumentMissing =>
                "Self argument missing for a non-static method (or an invalid type for self)".to_string(),
            MultipleStarredExpressionsInAssignment =>
                "Two starred expressions in assignment".to_string(),

            EnumFirstArgMustBeString =>
                "Enum() expects a string literal as the first argument".to_string(),
            EnumInvalidSecondArgument { enum_name } => format!(
                "Second argument of {enum_name}() must be string, tuple, list or dict \
                 literal for mypy to determine Enum members"
            ),
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
            EnumMemberAnnotationDisallowed => {
                additional_notes.push("See https://typing.readthedocs.io/en/latest/spec/enums.html#defining-members".into());
                r#"Enum members must be left unannotated"#.to_string()
            }

            DataclassCannotBe { kind: kind_name } => format!("{kind_name} cannot be a dataclass"),
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
                "Non-frozen dataclass cannot inherit from a frozen dataclass".to_string(),
            DataclassCannotInheritFrozenFromNonFrozen =>
                "Frozen dataclass cannot inherit from a non-frozen dataclass".to_string(),
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
            DataclassTransformUnknownParam { name } => format!(
                r#"Unrecognized dataclass_transform parameter "{name}""#
            ),
            DataclassTransformFieldSpecifiersMustBeTuple =>
                r#""field_specifiers" argument must be a tuple literal"#.to_string(),
            DataclassTransformFieldSpecifiersMustOnlyContainIdentifiers =>
                r#""field_specifiers" must only contain identifiers"#.to_string(),
            DataclassTransformFieldAliasParamMustBeString =>
                r#""alias" argument to dataclass field must be a string literal"#.to_string(),

            NegativeShiftCount => "Negative shift count".to_string(),
            DivisionByZero => "Division by zero".to_string(),

            FunctionIsUntyped => "Function is missing a type annotation".to_string(),
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
            CoroutineValueMustBeUsed { type_ } => {
                additional_notes.push("Are you missing an await?".to_string());
                format!(r#"Value of type "{type_}" must be used"#)
            }
            AwaitableValueMustBeUsed { type_ } => {
                additional_notes.push("Are you missing an await?".to_string());
                format!(r#"Value of type "{type_}" must be used"#)
            }
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
                let module = if self.db.project.settings.python_version_or_default() < PythonVersion::new(3, 11) {
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
            InvalidAssignmentTarget => "Invalid assignment target".to_string(),
            UnpackingAStringIsDisallowed => "Unpacking a string is disallowed".to_string(),
            StarredExpressionOnlyNoTarget =>
                "can't use starred expression here".to_string(),
            BreakOutsideLoop => "\"break\" outside loop".to_string(),
            ContinueOutsideLoop => "\"continue\" outside loop".to_string(),
            StmtOutsideFunction{keyword} => format!("{keyword:?} outside function"),
            AsyncOutsideAsyncFunction { keyword }  => format!(
                r#""async {keyword}" outside async function"#
            ),
            YieldOrYieldFromInsideComprehension { keyword } => format!(
                "{keyword:?} inside comprehension or generator expression"
            ),
            AwaitOutsideFunction => r#""await" outside function"#.to_string(),
            AwaitOutsideCoroutine => r#""await" outside coroutine ("async def")"#.to_string(),
            YieldFromInAsyncFunction => r#""yield from" in async function"#.to_string(),
            ReturnInAsyncGenerator => r#""return" with value in async generator is not allowed"#.to_string(),
            NonlocalAtModuleLevel => "nonlocal declaration not allowed at module level".to_string(),
            NonlocalNoBindingFound { name } => format!(r#"No binding for nonlocal "{name}" found"#),
            NonlocalBindingDisallowedForTypeParams { name } => format!(
                r#"nonlocal binding not allowed for type parameter "{name}""#
            ),
            GlobalAtModuleLevel => r#"Global at module level is unnecessary"#.to_string(),
            NonlocalAndGlobal { name } => format!(r#"Name "{name}" is nonlocal and global"#),
            NameAssignedBeforeGlobalDeclaration { name } => format!(
                r#"SyntaxError: name '{name}' is assigned to before global declaration"#
            ),
            NameDefinedInLocalScopeBeforeNonlocal { name } => format!(
                r#"Name "{name}" is already defined in local scope before nonlocal declaration"#
            ),
            InvalidBaseClass => format!("Invalid base class {:?}", self.code_under_issue()),
            TypeAliasSyntaxInBaseClassIsInvalid =>
                "Type alias defined using \"type\" statement not valid as base class".to_string(),
            TypeAliasSyntaxInFunction =>
                "Type alias not allowed in function".to_string(),
            CannotInheritFromFinalClass { class_name } => format!(
                r#"Cannot inherit from final class "{class_name}""#
            ),
            FinalClassHasAbstractAttributes { class_name, attributes } => format!(
                "Final class {class_name} has abstract attributes {attributes}"
            ),
            FinalMethodIsAbstract { name } => format!("Method {name} is both abstract and final"),
            ClassNeedsAbcMeta { class_name, attributes } => {
                additional_notes.push(
                    "If it is meant to be abstract, add 'abc.ABCMeta' as an explicit metaclass".to_string()
                );
                format!("Class {class_name} has abstract attributes {attributes}")
            }
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
            InvalidTypeCycle => "Invalid type cycle".to_string(),
            CurrentlyUnsupportedBaseClassCycle =>
                "This base class/alias cycle is currently unsupported".to_string(),
            EnsureSingleGenericOrProtocol =>
                "Only single Generic[...] or Protocol[...] can be in bases".to_string(),
            GenericWithTypeParamsIsRedundant => "Generic[...] base class is redundant".to_string(),
            ProtocolWithTypeParamsNoBracketsExpected =>
                r#"No arguments expected for "Protocol" base class"#.to_string(),

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
            UseParamSpecArgs { name } => format!(r#"Use "{name}.args" for variadic "*" parameter"#),
            UseParamSpecKwargs { name } => format!(r#"Use "{name}.kwargs" for variadic "**" parameter"#),
            ParamSpecParamsNeedBothStarAndStarStar { name } => format!(
                r#"ParamSpec must have "*args" typed as "{name}.args" and "**kwargs" typed as "{name}.kwargs""#
            ),
            ParamSpecArgumentsNeedsBothStarAndStarStar { name } => format!(
                r#"ParamSpec arguments must be of types "*{name}.args, **{name}.kwargs""#
            ),
            ParamSpecKwParamNotAllowed => "Arguments not allowed after ParamSpec.args".to_string(),
            ParamSpecComponentsNotAllowed => "ParamSpec components are not allowed here".to_string(),
            NewTypeCannotHaveTypeDeclaration =>
                "Cannot declare the type of a NewType declaration".to_string(),
            NewTypeInvalidType => "Argument 2 to NewType(...) must be a valid type".to_string(),
            NewTypeMustBeSubclassable{got} => format!(
                "Argument 2 to NewType(...) must be subclassable (got \"{got}\")"
            ),
            NewTypeCannotUseProtocols => "NewType cannot be used with protocol classes".to_string(),
            NewTypesExpectSinglePositionalArgument =>
                "NewTypes expect a single positional argument".to_string(),
            BasesOfProtocolMustBeProtocol => "All bases of a protocol must be protocols".to_string(),
            MustHaveOneArgument { name } => format!(
                "{name} must have exactly one type argument"
            ),
            CannotContainType { name } => format!(r#"type[...] can't contain "{name}[...]""#),
            InvalidRecursiveTypeAliasUnionOfItself { target } => format!(
                "Invalid recursive alias: a {target} item of itself"
            ),
            InvalidRecursiveTypeAliasTypeVarNesting =>
                "Invalid recursive alias: type variable nesting on right hand side".to_string(),
            RecursiveTypesNotAllowedInFunctionScope { alias_name } => {
                additional_notes.push("Recursive types are not allowed at function scope".to_string());
                format!(r#"Cannot resolve name "{alias_name}" (possible cyclic definition)"#)
            }
            RuntimeCheckableCanOnlyBeUsedWithProtocolClasses =>
                "@runtime_checkable can only be used with protocol classes".to_string(),
            ProtocolNotRuntimeCheckable =>
                "Only @runtime_checkable protocols can be used with instance and class checks".to_string(),
            IssubcclassWithProtocolNonMethodMembers { protocol, non_method_members }=> {
                additional_notes.push(format!(
                    r#"Protocol "{protocol}" has non-method member(s): {non_method_members}"#
                ));
                "Only protocols that don't have non-method members can be used with issubclass()".to_string()
            }
            TypeAliasRightSideNeeded => "Right side needed for TypeAlias".to_string(),
            TypeAliasInTypeCommentNotSupported => "TypeAlias comment currently not supported".to_string(),

            FinalTooManyArguments => "Final[...] takes at most one type argument".to_string(),
            FinalNameMustBeInitializedWithValue => "Final name must be initialized with a value".to_string(),
            FinalInWrongPlace =>
                "Final can be only used as an outermost qualifier in a variable annotation".to_string(),
            WithoutInitializerAndType { kind } => format!(
                "Type in {kind}[...] can only be omitted if there is an initializer"
            ),
            FinalInClassBodyCannotDependOnTypeVariables =>
                "Final name declared in class body cannot depend on type variables".to_string(),
            FinalAndClassVarUsedBoth =>
                "Variable should not be annotated with both ClassVar and Final".to_string(),
            FinalCanOnlyBeUsedInMethods =>
                "@final cannot be used with non-method functions".to_string(),
            ShouldBeAppliedOnlyToOverloadImplementation { kind } => format!(
                "@{kind} should be applied only to overload implementation"
            ),
            InStubMustBeAppliedToFirstOverload { kind } => format!(
                "In a stub file @{kind} must be applied only to the first overload"
            ),
            NeedTypeArgumentForFinalInDataclass =>
                "Need type argument for Final[...] with non-literal default in dataclass".to_string(),
            ProtocolMemberCannotBeFinal => "Protocol member cannot be final".to_string(),
            FinalAttributeOnlyValidInClassBodyOrInit =>
                "Can only declare a final attribute in class body or __init__".to_string(),
            FinalInLoopDisallowed => "Cannot use Final inside a loop".to_string(),

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
            TypeVarLikeBoundByOuterClass{type_var_like} => format!(
                r#"Type variable "{}" is bound by an outer class"#,
                type_var_like.name(self.db)
            ),
            TypeParametersShouldBeDeclared { type_var_like } => format!(
                r#"All type parameters should be declared ("{}" not declared)"#,
                type_var_like.name(self.db)
            ),
            IncompleteGenericOrProtocolTypeVars =>
                "If Generic[...] or Protocol[...] is present it should list all type variables".to_string(),
            TypeVarExpected{class} => format!("Free type variable expected in {class}[...]"),
            FreeTypeVariableExpectInTypeAliasTypeTypeParams  { is_unpack } => {
                if *is_unpack {
                    additional_notes.push("Don't Unpack type variables in type_params".to_string());
                }
                "Free type variable expected in type_params argument to TypeAliasType".to_string()
            }
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
            TypeVarValuesNeedsAtLeastTwo =>
                 "Type variable must have at least two constrained types".to_string(),
            UnexpectedArgument{class_name, argument_name} => format!(
                 "Unexpected argument to \"{class_name}()\": \"{argument_name}\""),
            InvalidAssignmentForm { class_name } => format!(
                "Invalid assignment form for {class_name}, please use the simple \
                 form \"X = {class_name}(..)\""
            ),
            TypeVarLikeTooFewArguments{class_name} => format!("Too few arguments for {class_name}()"),
            TypeVarLikeFirstArgMustBeString{class_name} => format!(
                "{class_name}() expects a string literal as first argument"),
            TypeVarVarianceMustBeBool{argument} => format!(
                "TypeVar \"{argument}\" may only be a literal bool"
            ),
            TypeVarTypeExpected => "Type expected".to_string(),
            TypeVarBoundMustBeType => r#"TypeVar "bound" must be a type"#.to_string(),
            TypeVarConstraintCannotHaveTypeVariables =>
                "TypeVar constraint type cannot be parametrized by type variables".to_string(),
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
            ParamSpecKeywordArgumentWithoutDefinedSemantics =>
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
            NotAcceptingSelfArgument { function_name, callable } => format!(
                r#"Attribute function "{function_name}" with type "{callable}" does not accept self argument"#
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
            CannotInstantiateAbstractClass{ name, abstract_attributes } => {
                let mut iterator = abstract_attributes
                    .iter()
                    .map(|&link| format!("\"{}\"", NodeRef::from_link(self.db, link).as_code()));
                let end = iterator.next_back().unwrap();
                let suffix = match abstract_attributes.len() {
                    1 => format!("attribute {end}"),
                    2..=5 => format!("attributes {} and {end}", join_with_commas(iterator)),
                    _ => format!(
                        "attributes {}, {}, ... and {end} ({} methods suppressed)",
                        iterator.next().unwrap(),
                        iterator.next().unwrap(),
                        abstract_attributes.len() - 3
                    ),
                };
                format!("Cannot instantiate abstract class \"{name}\" with abstract {suffix}")
            }
            OnlyConcreteClassAllowedWhereTypeExpected { type_ } => format!(
                r#"Only concrete class can be given where "{type_}" is expected"#
            ),
            OnlyConcreteClassAllowedWhereTypeExpectedForVariable  { type_ } => format!(
                r#"Can only assign concrete classes to a variable of type "{type_}""#
            ),
            UnpackRequiresExactlyOneArgument =>
                "Unpack[...] requires exactly one type argument".to_string(),
            UnpackOnlyValidInVariadicPosition => "Unpack is only valid in a variadic position".to_string(),
            VariadicUnpackMustBeTupleLike { actual } => format!(
                r#""{actual}" cannot be unpacked (must be tuple or TypeVarTuple)"#
            ),
            MoreThanOneUnpackTypeIsNotAllowed =>
                "More than one Unpack in a type is not allowed".to_string(),
            TypeVarTupleCannotBeSplit => "TypeVarTuple cannot be split".to_string(),
            TypeVarDefaultWrongOrder { type_var1, type_var2 } => format!(
                r#""{type_var1}" cannot appear after "{type_var2}" in type parameter list because it has no default type"#
            ),
            TypeVarDefaultTypeVarOutOfScope { type_var } => format!(
                r#"Type parameter "{type_var}" has a default type that refers to one or more type variables that are out of scope"#
            ),
            AlreadyDefinedTypeParameter { name } => format!(
                r#""{name}" already defined as a type parameter"#
            ),
            DuplicateTypeVarInTypeAliasType { name } => format!(
                r#"Duplicate type variable "{name}" in type_params argument to TypeAliasType"#
            ),
            MultipleTypeVarTupleDisallowedInTypeParams { in_type_alias_type } => {
                if *in_type_alias_type {
                    "Can only use one TypeVarTuple in type_params argument to TypeAliasType".to_string()
                } else {
                    "Can only use one TypeVarTuple in type params".to_string()
                }
            }
            InvalidTypeVarOfOuterClass { name } => format!(
                "\"{name}\" may not be used, because it's defined in an outer class"
            ),
            TypeVarInferVarianceCannotSpecifyVariance { specified } => format!(
                "Cannot use {specified} with infer_variance"
            ),

            CannotUseIsinstanceWith { func, with } => format!("Cannot use {func}() with {with} type"),
            CannotUseIsinstanceWithParametrizedGenerics =>
                "Parameterized generics cannot be used with class or instance checks".to_string(),

            InvalidAssertType { actual, wanted } => format!(
                r#"Expression is of type "{actual}", not "{wanted}""#
            ),
            AssertionAlwaysTrueBecauseOfParentheses => "Assertion is always true, perhaps remove parentheses?".to_string(),

            SuperUsedOutsideClass => r#""super" used outside class"#.to_string(),
            SuperOutsideOfAMethod => r#""super()" outside of a method is not supported"#.to_string(),
            SuperRequiresOneOrTwoPositionalArgumentsInEnclosingFunction => r#""super()" requires one or two positional arguments in enclosing function"#.to_string(),
            SuperWithSingleArgumentNotSupported => "\"super\" with a single argument not supported".to_string(),
            SuperVarargsNotSupported => "Varargs not supported with \"super\"".to_string(),
            SuperOnlyAcceptsPositionalArguments =>
                "\"super\" only accepts positional arguments".to_string(),
            SuperArgument1MustBeTypeObject { got } => format!(
                "Argument 1 for \"super\" must be a type object; got {got}"
            ),
            SuperArgument2MustBeAnInstanceOfArgument1 =>
                "Argument 2 for \"super\" not an instance of argument 1".to_string(),
            SuperUnsupportedArgument{argument_index} =>
                format!("Unsupported argument {argument_index} for \"super\""),
            SuperTargetClassHasNoBaseClass => "Target class has no base class".to_string(),
            UndefinedInSuperclass{name} => format!("\"{name}\" undefined in superclass"),
            CallToAbstractMethodViaSuper { method_name, class_name } => format!(
                r#"Call to abstract method "{method_name}" of "{class_name}" with trivial body via super() is unsafe"#
            ),

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
            IncompatiblePropertySetterOverride {notes} => {
                additional_notes.extend_from_slice(notes);
                "Incompatible override of a setter type".to_string()
            }
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
                additional_notes.push(r#"Use "typing.Literal[False]" as the return type or change it to "None""#.to_string());
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
            CannotOverrideWritableWithFinalAttribute { name } => format!(
                r#"Cannot override writable attribute "{name}" with a final one"#
            ),
            CannotOverrideWritableAttributeWithReadOnlyProperty { name, base_class, other_class } => format!(
                r#"Cannot override writeable attribute "{name}" in base "{base_class}" with read-only property in base "{other_class}""#
            ),
            ExplicitOverrideFlagRequiresOverride { method, class } => format!(
                r#"Method "{method}" is not using @override but is overriding a method in class "{class}""#
            ),
            TotalOrderingMissingMethod => {
                r#"No ordering operation defined when using "functools.total_ordering": < > <= >="#.to_string()
            }

            BaseExceptionExpected =>
                "Exception type must be derived from BaseException (or be a \
                 tuple of exception classes)".to_string(),
            BaseExceptionExpectedForRaise { did_you_mean } => match did_you_mean {
                Some(did_you_mean) => format!(
                    r#"Exception must be derived from BaseException; did you mean "{did_you_mean}"?"#
                ),
                None => "Exception must be derived from BaseException".to_string(),
            },
            ExceptStarIsNotAllowedToBeAnExceptionGroup =>
                "Exception type in except* cannot derive from BaseExceptionGroup".to_string(),

            ClassHasNoMatchArgs { class } => format!(
                r#"Class "{class}" doesn't define "__match_args__""#
            ),
            TooManyPositionalPatternsForMatchArgs =>
                "Too many positional patterns for class pattern".to_string(),
            ExpectedTypeInClassPattern { got } => format!(
                r#"Expected type in class pattern; found "{got}""#
            ),
            InvalidDunderMatchArgs =>
                "__match_args__ must be a tuple containing string literals for \
                 checking of match statements to work".to_string(),
            DuplicateKeywordPattern { name } => format!(r#"Duplicate keyword pattern "{name}""#),

            IntersectionCannotExistDueToIncompatibleMethodSignatures { intersection } => format!(
                "Subclass of {intersection} cannot exist: would have incompatible method signatures"
            ),
            IntersectionCannotExistDueToFinalClass { intersection, final_class } => format!(
                r#"Subclass of {intersection} cannot exist: "{final_class}" is final"#
            ),
            IntersectionCannotExistDueToInconsistentMro { intersection } => format!(
                r#"Subclass of {intersection} cannot exist: would have inconsistent method resolution order"#
            ),

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
            NamedTupleFieldExpectsTupleOfStrAndType =>
                "NamedTuple field should be a tuple of a string literal and a type".to_string(),
            NamedTupleInvalidAttributeOverride { name } =>
                format!("Cannot overwrite NamedTuple attribute \"{name}\""),
            InvalidSecondArgumentToNamedTuple{name} =>
                format!("List or tuple literal expected as the second argument to \"{name}()\""),
            UnexpectedArgumentsTo{name} =>
                format!("Unexpected arguments to \"{name}()\""),
            UnexpectedArgumentTo{name} =>
                format!("Unexpected argument to \"{name}()\""),
            TupleExpectedAsNamedTupleField => "Tuple expected as \"NamedTuple()\" field".to_string(),
            FunctionalNamedTupleInvalidFieldName { name, field_name } => format!(
                r#""{name}()" field name "{field_name}" is not a valid identifier"#
            ),
            FunctionalNamedTupleNameUsedAKeyword { name, field_name } => format!(
                r#""{name}()" field name "{field_name}" is a keyword"#
            ),
            FunctionalNamedTupleNameCannotStartWithUnderscore{name, field_name} => format!(
                r#""{name}()" field name "{field_name}" starts with an underscore"#
            ),
            FunctionalNamedTupleDuplicateField { name, field_name } => format!(
                r#""{name}()" has duplicate field name "{field_name}""#
            ),
            NamedTupleNameCannotStartWithUnderscore{field_name} => format!(
                "NamedTuple field name cannot start with an underscore: {field_name}"),
            NamedTupleInvalidFieldName => "Invalid \"NamedTuple()\" field name".to_string(),
            NamedTupleFirstArgumentMismatch { should, is } => format!(
                r#"First argument to namedtuple() should be "{should}", not "{is}""#
            ),
            NamedTupleExpectedBoolForRenameArgument => r#"Boolean literal expected as the "rename" argument to namedtuple()"#.to_string(),
            NamedTupleUnexpectedKeywordArgument { keyword_name } => format!(
                r#"Unexpected keyword argument "{keyword_name}" for "namedtuple""#
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
            NamedTupleAttributeCannotBeDeleted => "NamedTuple attributes cannot be deleted".to_string(),

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

            TypedDictFieldModifierCannotBeNested { modifier } => format!(
                r#""{modifier}[]" type cannot be nested"#
            ),
            TypedDictSelfNotAllowed => "Self type cannot be used in TypedDict item type".to_string(),
            TypedDictNameMismatch { string_name, variable_name } => format!(
                r#"First argument "{string_name}" to TypedDict() does not match variable name "{variable_name}""#
            ),
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
            TypedDictReadOnlyKeyMutated { key } => format!(
                r#"ReadOnly TypedDict key "{key}" TypedDict is mutated"#
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
            ArgumentMustBeTrueOrFalse { key } => format!(
                r#""{key}" argument must be a True or False literal"#
            ),
            TypedDictCannotUseCloseIfSuperClassExtraItemsNonReadOnly =>
                r#"Cannot set "closed=True" when superclass has non-read-only "extra_items""#.to_string(),
            TypedDictCannotUseCloseFalseIfSuperClassClosed =>
                r#"Cannot set "closed=False" when superclass is "closed=True""#.to_string(),
            TypedDictCannotUseCloseFalseIfSuperClassHasExtraItems =>
                r#"Cannot set "closed=False" when superclass has "extra_items""#.to_string(),
            TypedDictExtraItemsCannotBe { kind } => format!(
                r#""extra_items" value cannot be "{kind}[...]""#
            ),
            TypedDictExtraItemsNonReadOnlyChangeDisallowed =>
                r#"Cannot change "extra_items" type unless it is "ReadOnly" in the superclass"#.to_string(),
            TypedDictExtraItemsIncompatibleTypes { in_super_class, in_sub_class } => format!(
                r#"Expected a subtype of "{in_super_class}", but got "{in_sub_class}""#
            ),
            TypedDictSetItemWithExtraItemsMismatch { got, expected } => format!(
                r#"For a TypedDict with only types "{got}", "{expected}" is expected"#
            ),
            TypedDictMemberRequiredButHasExtraItemsOfSuper { name } => format!(
                r#"TypedDict member "{name}" is required, but the extra_items of the super class are not"#
            ),
            TypedDictMemberReadOnlyButExtraItemsOfSuperClassIsNot { name } => format!(
                r#"TypedDict member "{name}" is read only, but the extra_items of the super class are"#
            ),
            TypedDictMemberNotAssignableToExtraItemsOfSuperClass { name, in_super_class, member_type } => format!(
                r#"TypedDict member "{name}" type "{member_type}" is not assignable, but the extra_items of the super class are of type "{in_super_class}""#
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
            OverloadImplementationParamsNotBroadEnough{signature_index} => format!(
                "Overloaded function implementation does not accept all possible arguments of signature {signature_index}"
            ),
            OverloadInconsistentKind { kind } => format!(
                "Overload does not consistently use the \"@{kind}\" decorator on all function signatures.",
            ),
            OverloadedPropertyNotSupported =>
                "An overload can not be a property".to_string(),
            OverloadWithAbstractAndNonAbstract =>
                "Overloaded method has both abstract and non-abstract variants".to_string(),
            OverloadTooManyUnions =>
                "Not all union combinations were tried because there are too many unions".to_string(),

            DecoratorOnTopOfPropertyNotSupported =>
                "Decorators on top of @property are not supported".to_string(),
            ReadOnlyPropertyCannotOverwriteReadWriteProperty =>
                "Read-only property cannot override read-write property".to_string(),
            ReadOnlyPropertyCannotOverwriteWritableAttribute =>
                "Cannot override writeable attribute with read-only property".to_string(),
            OnlyInstanceMethodsCanBeDecoratedWithProperty =>
                "Only instance methods can be decorated with @property".to_string(),
            OnlySupportedTopDecoratorSetter{name} =>
                format!("Only supported top decorator is @{name}.setter"),
            InvalidPropertySetterSignature => "Invalid property setter signature".to_string(),
            UnexpectedDefinitionForProperty{name} =>
                format!("Unexpected definition for property \"{name}\""),
            PropertyIsReadOnly{class_name, property_name} => format!(
                "Property \"{property_name}\" defined in \"{class_name}\" is read-only"
            ),

            InvariantNote{actual, maybe} => {
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
                "By default the bodies of untyped functions are not checked, \
                 consider using --check-untyped-defs".to_string()
            }
            Note(s) => {
                s.clone().into()
            }
        }
    }

    pub fn message(&self) -> String {
        let mut additional_notes = vec![];
        let mut msg = self.message_with_notes(&mut additional_notes);
        for additional_note in additional_notes {
            msg.push('\n');
            msg.push_str(&additional_note);
        }
        msg
    }

    fn message_formatting_options(&self, config: &DiagnosticConfig) -> MessageFormattingInfos<'db> {
        let original_file = self.file.original_file(self.db);
        let path = self
            .db
            .file_path(original_file.file_index)
            .trim_start_matches(&***original_file.file_entry(self.db).parent.workspace_path());
        let path = self
            .db
            .vfs
            .handler
            .strip_separator_prefix(path)
            .unwrap_or(path);
        let mut additional_notes = vec![];
        let error = self.message_with_notes(&mut additional_notes);

        let mut line_number_infos = String::with_capacity(32);
        let mut add_part = |n| line_number_infos.push_str(&format!(":{n}"));
        let start = self.start_position();
        let end = self.end_position();
        add_part(start.line_one_based());
        if config.show_column_numbers {
            add_part(start.code_points_column() + 1);
        }
        if config.show_error_end {
            add_part(end.line_one_based());
            if config.show_column_numbers {
                add_part(end.code_points_column() + 1);
            }
        }
        MessageFormattingInfos {
            error,
            additional_notes,
            kind: match self.is_note() {
                true => "note",
                false => "error",
            },
            path,
            line_number_infos,
        }
    }

    pub fn as_string(&self, config: &DiagnosticConfig) -> String {
        let opts = self.message_formatting_options(config);
        let fmt_line =
            |kind, error| format!("{}{}: {kind}: {error}", opts.path, opts.line_number_infos);
        let mut result = fmt_line(opts.kind, &opts.error);
        if config.show_error_codes
            && let Some(mypy_error_code) = self.issue.kind.mypy_error_code()
        {
            result += &format!("  [{mypy_error_code}]");
        }
        for note in &opts.additional_notes {
            result += "\n";
            result += &fmt_line("note", note);
        }
        if config.pretty {
            result += "\n";
            let mut buf: Vec<u8> = Vec::new();
            self.pretty_print_code_surrounding_issue(&mut buf, false)
                .unwrap();
            result += &String::from_utf8(buf).unwrap();
        }
        result
    }

    pub fn write_colored(
        &self,
        writer: &mut dyn Write,
        config: &DiagnosticConfig,
    ) -> std::io::Result<()> {
        let opts = self.message_formatting_options(config);
        let fmt_line = |writer: &mut dyn Write, kind: &str, error| {
            write!(writer, "{}{}: ", opts.path, opts.line_number_infos)?;
            if kind == "error" {
                write!(writer, "{}", "error: ".red().bold())?;
            } else {
                write!(writer, "{}", kind.blue())?;
                write!(writer, "{}", ": ".blue())?;
            }
            highlight_quote_groups(writer, error)
        };
        fmt_line(writer, opts.kind, &opts.error)?;
        if config.show_error_codes
            && let Some(mypy_error_code) = self.issue.kind.mypy_error_code()
        {
            let with_code = format!("  [{mypy_error_code}]").yellow();
            write!(writer, "{with_code}")?;
        }
        for note in &opts.additional_notes {
            write!(writer, "\n")?;
            fmt_line(writer, "note", note)?;
        }
        writeln!(writer)?;
        if config.pretty {
            self.pretty_print_code_surrounding_issue(writer, true)?;
            writeln!(writer)?;
        }
        Ok(())
    }

    fn pretty_print_code_surrounding_issue(
        &self,
        writer: &mut dyn Write,
        add_colors: bool,
    ) -> std::io::Result<()> {
        let start = self.start_position();
        let end = self.end_position();

        // Find the context -/+ 2 lines in front and after the error
        let start_line = start.line_zero_based();
        let end_line = end.line_zero_based();

        let lines_with_numbers = self
            .file
            .lines_context_around_range(self.db, start_line..end_line, 2)
            .collect::<Vec<_>>();
        let until_line_space_needed = format!("{}", lines_with_numbers.last().unwrap().0).len();

        let write_colored = |writer: &mut dyn Write, colored: ColoredString| {
            if add_colors {
                write!(writer, "{colored}")
            } else {
                write!(writer, "{}", colored.clear())
            }
        };

        // Empty |
        for _ in 0..until_line_space_needed {
            write!(writer, " ")?;
        }
        write_colored(writer, " |\n".blue())?;
        for (line_nr, line) in lines_with_numbers {
            write_colored(
                writer,
                format!(
                    "{:>width$} | ",
                    line_nr + 1,
                    width = until_line_space_needed
                )
                .blue(),
            )?;

            // On these lines there are errors, so "underline" them.
            if line_nr >= start_line && line_nr <= end_line {
                let start_column = if line_nr == start_line {
                    start.code_points_column()
                } else {
                    0
                };
                let end_column = if line_nr == end_line {
                    end.code_points_column()
                } else {
                    line.len()
                };
                if start_column > 0 {
                    write!(writer, "{}", &line[..start_column])?;
                }

                // Highlight the error
                write_colored(writer, line[start_column..end_column].bright_red())?;

                if end_column < line.len() {
                    write!(writer, "{}", &line[end_column..])?;
                }
                write!(writer, "\n")?;

                //writeln!(writer, "{}", format!("{:^>chars$}", "|", chars = x).bright_red());
            } else {
                writeln!(writer, "{line}")?;
            }
        }
        Ok(())
    }
}

fn highlight_quote_groups(out: &mut dyn Write, msg: &str) -> std::io::Result<()> {
    let mut in_quotes = false;

    for part in msg.split('"') {
        if in_quotes {
            write!(out, "{}", format!("\"{}\"", part).bold())?;
        } else {
            write!(out, "{}", part)?;
        }
        in_quotes = !in_quotes;
    }
    Ok(())
}

struct MessageFormattingInfos<'db> {
    error: String,
    additional_notes: Vec<String>,
    kind: &'static str,
    path: &'db str,
    line_number_infos: String,
}

impl std::fmt::Debug for Diagnostic<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", &self.as_string(&DiagnosticConfig::default()))
    }
}

#[derive(Default, Clone)]
pub(crate) struct Diagnostics(InsertOnlyVec<Issue>);

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
            self.0.push(Box::pin(Issue::from_start_stop(
                last_issue.start_position,
                last_issue.end_position,
                IssueKind::Note(
                    format!(r#"Error code "{s}" not covered by "type: ignore" comment"#).into(),
                ),
            )));
        }
        Ok(last_issue)
    }

    pub unsafe fn iter(&self) -> impl Iterator<Item = &Issue> {
        unsafe { self.0.iter() }
    }

    pub fn invalidate_non_name_binder_issues(&mut self) {
        self.0.as_vec_mut().retain(|issue| issue.from_name_binder)
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
            // Part of mypy.stubinfo.non_bundled_packages_flat
            ("_cffi_backend", "types-cffi"),
            ("_win32typing", "types-pywin32"),
            ("antlr4", "types-antlr4-python3-runtime"),
            ("assertpy", "types-assertpy"),
            ("atheris", "types-atheris"),
            ("authlib", "types-Authlib"),
            ("aws_xray_sdk", "types-aws-xray-sdk"),
            ("boltons", "types-boltons"),
            ("braintree", "types-braintree"),
            ("bs4", "types-beautifulsoup4"),
            ("bugbear", "types-flake8-bugbear"),
            ("caldav", "types-caldav"),
            ("capturer", "types-capturer"),
            ("cffi", "types-cffi"),
            ("chevron", "types-chevron"),
            ("click_default_group", "types-click-default-group"),
            ("click_log", "types-click-log"),
            ("click_web", "types-click-web"),
            ("colorama", "types-colorama"),
            ("commctrl", "types-pywin32"),
            ("commonmark", "types-commonmark"),
            ("consolemenu", "types-console-menu"),
            ("corus", "types-corus"),
            ("cronlog", "types-python-crontab"),
            ("crontab", "types-python-crontab"),
            ("crontabs", "types-python-crontab"),
            ("datemath", "types-python-datemath"),
            ("dateparser_data", "types-dateparser"),
            ("dde", "types-pywin32"),
            ("defusedxml", "types-defusedxml"),
            ("docker", "types-docker"),
            ("dockerfile_parse", "types-dockerfile-parse"),
            ("editdistance", "types-editdistance"),
            ("entrypoints", "types-entrypoints"),
            ("exifread", "types-ExifRead"),
            ("fanstatic", "types-fanstatic"),
            ("farmhash", "types-pyfarmhash"),
            ("flake8_builtins", "types-flake8-builtins"),
            ("flake8_docstrings", "types-flake8-docstrings"),
            ("flake8_rst_docstrings", "types-flake8-rst-docstrings"),
            ("flake8_simplify", "types-flake8-simplify"),
            ("flake8_typing_imports", "types-flake8-typing-imports"),
            ("flake8", "types-flake8"),
            ("flask_cors", "types-Flask-Cors"),
            ("flask_migrate", "types-Flask-Migrate"),
            ("flask_socketio", "types-Flask-SocketIO"),
            ("fpdf", "types-fpdf2"),
            ("gdb", "types-gdb"),
            ("gevent", "types-gevent"),
            ("greenlet", "types-greenlet"),
            ("hdbcli", "types-hdbcli"),
            ("html5lib", "types-html5lib"),
            ("httplib2", "types-httplib2"),
            ("humanfriendly", "types-humanfriendly"),
            ("hvac", "types-hvac"),
            ("ibm_db", "types-ibm-db"),
            ("icalendar", "types-icalendar"),
            ("import_export", "types-django-import-export"),
            ("influxdb_client", "types-influxdb-client"),
            ("inifile", "types-inifile"),
            ("isapi", "types-pywin32"),
            ("jack", "types-JACK-Client"),
            ("jenkins", "types-python-jenkins"),
            ("Jetson", "types-Jetson.GPIO"),
            ("jks", "types-pyjks"),
            ("jmespath", "types-jmespath"),
            ("jose", "types-python-jose"),
            ("jsonschema", "types-jsonschema"),
            ("jwcrypto", "types-jwcrypto"),
            ("keyboard", "types-keyboard"),
            ("ldap3", "types-ldap3"),
            ("lupa", "types-lupa"),
            ("lzstring", "types-lzstring"),
            ("m3u8", "types-m3u8"),
            ("mmapfile", "types-pywin32"),
            ("mmsystem", "types-pywin32"),
            ("mypy_extensions", "types-mypy-extensions"),
            ("MySQLdb", "types-mysqlclient"),
            ("nanoid", "types-nanoid"),
            ("nanoleafapi", "types-nanoleafapi"),
            ("netaddr", "types-netaddr"),
            ("netifaces", "types-netifaces"),
            ("networkx", "types-networkx"),
            ("nmap", "types-python-nmap"),
            ("ntsecuritycon", "types-pywin32"),
            ("oauthlib", "types-oauthlib"),
            ("objgraph", "types-objgraph"),
            ("odbc", "types-pywin32"),
            ("olefile", "types-olefile"),
            ("openpyxl", "types-openpyxl"),
            ("opentracing", "types-opentracing"),
            ("parsimonious", "types-parsimonious"),
            ("passlib", "types-passlib"),
            ("passpy", "types-passpy"),
            ("peewee", "types-peewee"),
            ("pep8ext_naming", "types-pep8-naming"),
            ("perfmon", "types-pywin32"),
            ("pexpect", "types-pexpect"),
            ("playhouse", "types-peewee"),
            ("portpicker", "types-portpicker"),
            ("psutil", "types-psutil"),
            ("psycopg2", "types-psycopg2"),
            ("pyasn1", "types-pyasn1"),
            ("pyaudio", "types-pyaudio"),
            ("pyautogui", "types-PyAutoGUI"),
            ("pycocotools", "types-pycocotools"),
            ("pyflakes", "types-pyflakes"),
            ("pygit2", "types-pygit2"),
            ("pygments", "types-Pygments"),
            ("pyi_splash", "types-pyinstaller"),
            ("PyInstaller", "types-pyinstaller"),
            ("pynput", "types-pynput"),
            ("pyscreeze", "types-PyScreeze"),
            ("pysftp", "types-pysftp"),
            ("pytest_lazyfixture", "types-pytest-lazy-fixture"),
            ("python_http_client", "types-python-http-client"),
            ("pythoncom", "types-pywin32"),
            ("pythonwin", "types-pywin32"),
            ("pywintypes", "types-pywin32"),
            ("qrbill", "types-qrbill"),
            ("qrcode", "types-qrcode"),
            ("regex", "types-regex"),
            ("regutil", "types-pywin32"),
            ("reportlab", "types-reportlab"),
            ("requests_oauthlib", "types-requests-oauthlib"),
            ("RPi", "types-RPi.GPIO"),
            ("s2clientprotocol", "types-s2clientprotocol"),
            ("sass", "types-libsass"),
            ("sassutils", "types-libsass"),
            ("seaborn", "types-seaborn"),
            ("send2trash", "types-Send2Trash"),
            ("serial", "types-pyserial"),
            ("servicemanager", "types-pywin32"),
            ("setuptools", "types-setuptools"),
            ("shapely", "types-shapely"),
            ("slumber", "types-slumber"),
            ("sspicon", "types-pywin32"),
            ("str2bool", "types-str2bool"),
            ("tensorflow", "types-tensorflow"),
            ("tgcrypto", "types-TgCrypto"),
            ("timer", "types-pywin32"),
            ("toposort", "types-toposort"),
            ("tqdm", "types-tqdm"),
            ("translationstring", "types-translationstring"),
            ("tree_sitter_languages", "types-tree-sitter-languages"),
            ("ttkthemes", "types-ttkthemes"),
            ("unidiff", "types-unidiff"),
            ("untangle", "types-untangle"),
            ("usersettings", "types-usersettings"),
            ("uwsgi", "types-uWSGI"),
            ("uwsgidecorators", "types-uWSGI"),
            ("vobject", "types-vobject"),
            ("webob", "types-WebOb"),
            ("whatthepatch", "types-whatthepatch"),
            ("win2kras", "types-pywin32"),
            ("win32", "types-pywin32"),
            ("win32api", "types-pywin32"),
            ("win32clipboard", "types-pywin32"),
            ("win32com", "types-pywin32"),
            ("win32comext", "types-pywin32"),
            ("win32con", "types-pywin32"),
            ("win32console", "types-pywin32"),
            ("win32cred", "types-pywin32"),
            ("win32crypt", "types-pywin32"),
            ("win32cryptcon", "types-pywin32"),
            ("win32event", "types-pywin32"),
            ("win32evtlog", "types-pywin32"),
            ("win32evtlogutil", "types-pywin32"),
            ("win32file", "types-pywin32"),
            ("win32gui_struct", "types-pywin32"),
            ("win32gui", "types-pywin32"),
            ("win32help", "types-pywin32"),
            ("win32inet", "types-pywin32"),
            ("win32inetcon", "types-pywin32"),
            ("win32job", "types-pywin32"),
            ("win32lz", "types-pywin32"),
            ("win32net", "types-pywin32"),
            ("win32netcon", "types-pywin32"),
            ("win32pdh", "types-pywin32"),
            ("win32pdhquery", "types-pywin32"),
            ("win32pipe", "types-pywin32"),
            ("win32print", "types-pywin32"),
            ("win32process", "types-pywin32"),
            ("win32profile", "types-pywin32"),
            ("win32ras", "types-pywin32"),
            ("win32security", "types-pywin32"),
            ("win32service", "types-pywin32"),
            ("win32serviceutil", "types-pywin32"),
            ("win32timezone", "types-pywin32"),
            ("win32trace", "types-pywin32"),
            ("win32transaction", "types-pywin32"),
            ("win32ts", "types-pywin32"),
            ("win32ui", "types-pywin32"),
            ("win32uiole", "types-pywin32"),
            ("win32verstamp", "types-pywin32"),
            ("win32wnet", "types-pywin32"),
            ("winerror", "types-pywin32"),
            ("winioctlcon", "types-pywin32"),
            ("winnt", "types-pywin32"),
            ("winperf", "types-pywin32"),
            ("winxpgui", "types-pywin32"),
            ("winxptheme", "types-pywin32"),
            ("workalendar", "types-workalendar"),
            ("wtforms", "types-WTForms"),
            ("wurlitzer", "types-wurlitzer"),
            ("xdg", "types-pyxdg"),
            ("xdgenvpy", "types-xdgenvpy"),
            ("Xlib", "types-python-xlib"),
            ("xmltodict", "types-xmltodict"),
            ("zstd", "types-zstd"),
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
