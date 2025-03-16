mod class;
mod named_tuple;
mod typed_dict;

pub(crate) use class::{
    linearize_mro_and_return_linearizable, ClassInitializer, ClassNodeRef,
    CLASS_TO_CLASS_INFO_DIFFERENCE, ORDERING_METHODS,
};
pub(crate) use named_tuple::execute_collections_named_tuple;

use std::{borrow::Cow, cell::Cell, rc::Rc};

use named_tuple::{
    new_collections_named_tuple, new_typing_named_tuple, new_typing_named_tuple_internal,
};
use parsa_python_cst::{SliceType as CSTSliceType, *};
use typed_dict::new_typed_dict_with_execution_syntax;

use super::{
    name_resolution::{NameResolution, PointResolution},
    utils::func_of_self_symbol,
    TypeVarFinder,
};
use crate::{
    arguments::{KnownArgsWithCustomAddIssue, SimpleArgs},
    database::{
        ComplexPoint, Database, Locality, Point, PointKind, PointLink, Specific, TypeAlias,
    },
    debug,
    diagnostics::{Issue, IssueKind},
    file::PythonFile,
    format_data::FormatData,
    getitem::{SliceOrSimple, SliceType, SliceTypeIterator},
    imports::{namespace_import, ImportResult},
    inference_state::InferenceState,
    inferred::Inferred,
    matching::{Generics, ResultContext},
    new_class,
    node_ref::NodeRef,
    recoverable_error,
    type_::{
        add_param_spec_to_params, AnyCause, CallableContent, CallableParam, CallableParams,
        CallableWithParent, ClassGenerics, Dataclass, DbBytes, DbString, Enum, EnumMember,
        FunctionKind, GenericClass, GenericItem, GenericsList, Literal, LiteralKind,
        MaybeUnpackGatherer, NamedTuple, Namespace, NeverCause, ParamSpecArg, ParamSpecUsage,
        ParamType, RecursiveType, StarParamType, StarStarParamType, StringSlice, Tuple, TupleArgs,
        TupleUnpack, Type, TypeArgs, TypeGuardInfo, TypeVar, TypeVarKind, TypeVarLike,
        TypeVarLikeUsage, TypeVarLikes, TypeVarManager, TypeVarTupleUsage, TypeVarUsage, TypedDict,
        TypedDictGenerics, UnionEntry, UnionType, WithUnpack,
    },
    type_helpers::{cache_class_name, Class, Function},
    utils::{debug_indent, rc_slice_into_vec, AlreadySeen},
};

const ASSIGNMENT_TYPE_CACHE_OFFSET: u32 = 1;
pub const ANNOTATION_TO_EXPR_DIFFERENCE: u32 = 2;

#[derive(Debug)]
pub(crate) enum TypeVarCallbackReturn {
    TypeVarLike(TypeVarLikeUsage),
    UnboundTypeVar,
    AddIssue(IssueKind),
    NotFound { allow_late_bound_callables: bool },
}

type MapAnnotationTypeCallback<'a> = Option<&'a dyn Fn(&mut TypeComputation, TypeContent) -> Type>;

type TypeVarCallback<'db, 'x> = &'x mut dyn FnMut(
    &InferenceState<'db, '_>,
    &TypeVarManager<PointLink>,
    TypeVarLike,
    Option<PointLink>, // current_callable
) -> TypeVarCallbackReturn;

#[derive(Debug, Clone)]
enum SpecialType {
    Protocol,
    ProtocolWithGenerics,
    Generic,
    GenericWithGenerics,
    Callable,
    BuiltinsType,
    TypingType,
    Tuple,
    Literal,
    LiteralString,
    Unpack,
    Concatenate,
}

#[derive(Debug, Clone)]
enum TypedDictFieldModifier {
    Required,
    NotRequired,
    ReadOnly,
}

impl TypedDictFieldModifier {
    fn name(&self) -> &'static str {
        match self {
            Self::Required => "Required[]",
            Self::NotRequired => "NotRequired[]",
            Self::ReadOnly => "ReadOnly[]",
        }
    }
}

#[derive(Debug, Clone)]
pub(super) enum InvalidVariableType<'a> {
    List,
    Tuple {
        tuple_length: usize,
    },
    Execution {
        was_class: bool,
    },
    Function {
        name: &'a str,
        qualified_name: String,
    },
    ParamNameAsBaseClassAny(NodeRef<'a>),
    Literal(&'a str),
    Variable(NodeRef<'a>),
    Float,
    Complex,
    Ellipsis,
    Other,
    Slice,
    InlineTypedDict,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum TypeComputationOrigin {
    AssignmentTypeCommentOrAnnotation {
        is_initialized: bool,
        type_comment: bool,
    },
    ParamTypeCommentOrAnnotation,
    TypedDictMember,
    TypeApplication,
    TypeAlias,
    CastTarget,
    NamedTupleMember,
    BaseClass,
    Other,
}

impl InvalidVariableType<'_> {
    fn add_issue(
        &self,
        db: &Database,
        add_issue: impl Fn(IssueKind),
        origin: TypeComputationOrigin,
    ) {
        add_issue(match self {
            Self::Variable(var_ref) | Self::ParamNameAsBaseClassAny(var_ref) => {
                add_issue(IssueKind::InvalidType(
                    format!(
                        "Variable \"{}.{}\" is not valid as a type",
                        var_ref.file.qualified_name(db),
                        var_ref.as_code().to_owned(),
                    )
                    .into(),
                ));
                IssueKind::Note(
                    Box::from("See https://mypy.readthedocs.io/en/stable/common_issues.html#variables-vs-type-aliases"),
                )
            }
            Self::Function {
                name,
                qualified_name,
            } => {
                add_issue(IssueKind::InvalidType(
                    format!("Function {:?} is not valid as a type", qualified_name,).into(),
                ));
                IssueKind::Note(Box::from(match *name {
                    "any" => "Perhaps you meant \"typing.Any\" instead of \"any\"?",
                    "callable" => "Perhaps you meant \"typing.Callable\" instead of \"callable\"?",
                    _ => "Perhaps you need \"Callable[...]\" or a callback protocol?",
                }))
            }
            Self::List => {
                add_issue(IssueKind::InvalidType(Box::from(
                    "Bracketed expression \"[...]\" is not valid as a type",
                )));
                IssueKind::Note(Box::from("Did you mean \"List[...]\"?"))
            }
            Self::Tuple { tuple_length } => {
                add_issue(IssueKind::InvalidType(Box::from(
                    "Syntax error in type annotation",
                )));
                if *tuple_length == 1 {
                    IssueKind::Note(Box::from("Suggestion: Is there a spurious trailing comma?"))
                } else {
                    IssueKind::Note(Box::from(
                        "Suggestion: Use Tuple[T1, ..., Tn] instead of (T1, ..., Tn)",
                    ))
                }
            }
            Self::Literal(s) => IssueKind::InvalidType(
                format!("Invalid type: try using Literal[{s}] instead?").into(),
            ),
            Self::Execution { .. } | Self::Other if origin == TypeComputationOrigin::CastTarget => {
                IssueKind::InvalidCastTarget
            }
            Self::Execution { .. } | Self::Other if origin == TypeComputationOrigin::TypeAlias => {
                IssueKind::InvalidType(Box::from(
                    "Invalid type alias: expression is not a valid type",
                ))
            }
            Self::Execution { was_class: true } => {
                add_issue(IssueKind::InvalidType(Box::from(
                    "Invalid type comment or annotation",
                )));
                IssueKind::Note(Box::from("Suggestion: use Foo[...] instead of Foo(...)"))
            }
            Self::Execution { .. } | Self::Other => {
                IssueKind::InvalidType(Box::from(if origin == TypeComputationOrigin::BaseClass {
                    "Type expected within [...]"
                } else {
                    "Invalid type comment or annotation"
                }))
            }
            Self::InlineTypedDict => IssueKind::InvalidType(Box::from(
                "Inline TypedDict types not supported; use assignment to define TypedDict",
            )),
            Self::Slice => {
                add_issue(IssueKind::InvalidType(Box::from(
                    "Invalid type comment or annotation",
                )));
                IssueKind::Note(Box::from("did you mean to use ',' instead of ':' ?"))
            }
            Self::Float => IssueKind::InvalidType(
                "Invalid type: float literals cannot be used as a type".into(),
            ),
            Self::Complex => IssueKind::InvalidType(
                "Invalid type: complex literals cannot be used as a type".into(),
            ),
            Self::Ellipsis => IssueKind::InvalidType("Unexpected \"...\"".into()),
        })
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeOrUnpack {
    Type(Type),
    TypeVarTuple(TypeVarTupleUsage),
    Unknown(UnknownCause),
}

#[derive(Debug, Clone, Default)]
struct TypedDictFieldModifiers {
    required: bool,
    not_required: bool,
    read_only: bool,
}

#[derive(Debug, Clone)]
enum TypeContent<'db, 'a> {
    Module(&'db PythonFile),
    Namespace(Rc<Namespace>),
    Class {
        node_ref: ClassNodeRef<'db>,
        has_type_vars: bool,
    },
    SimpleGeneric {
        node_ref: NodeRef<'db>,
        class_link: PointLink,
        generics: ClassGenerics,
    },
    Dataclass(Rc<Dataclass>),
    NamedTuple(Rc<NamedTuple>),
    TypedDictDefinition(Rc<TypedDict>),
    TypeAlias(&'db TypeAlias),
    Type(Type),
    SpecialType(SpecialType),
    SpecialCase(Specific),
    RecursiveAlias(PointLink),
    RecursiveClass(ClassNodeRef<'db>),
    InvalidVariable(InvalidVariableType<'a>),
    TypeVarTuple(TypeVarTupleUsage),
    ParamSpec(ParamSpecUsage),
    Unpacked(TypeOrUnpack),
    Concatenate(CallableParams),
    ClassVar(Type),
    EnumMember(EnumMember),
    TypedDictMemberModifiers(TypedDictFieldModifiers, Type),
    Final(Type),
    TypeGuardInfo(TypeGuardInfo),
    TypedDictFieldModifier(TypedDictFieldModifier),
    CallableParam(CallableParam),
    ParamSpecAttr {
        usage: ParamSpecUsage,
        name: &'a str,
    },
    Unknown(UnknownCause),
}

impl TypeContent<'_, '_> {
    const UNKNOWN_REPORTED: Self = Self::Unknown(UnknownCause::ReportedIssue);
}

enum ClassGetItemResult<'db> {
    GenericClass(GenericClass),
    SimpleGeneric {
        node_ref: NodeRef<'db>,
        class_link: PointLink,
        generics: ClassGenerics,
    },
    Invalid,
}

#[derive(Debug)]
enum Lookup<'db, 'a> {
    T(TypeContent<'db, 'a>),
    TypeVarLike(TypeVarLike),
}

impl Lookup<'_, '_> {
    const UNKNOWN_REPORTED: Self = Self::T(TypeContent::UNKNOWN_REPORTED);
}

#[derive(Debug)]
pub enum CalculatedBaseClass {
    Type(Type),
    Protocol,
    NamedTuple(Rc<NamedTuple>),
    TypedDict,
    NewNamedTuple,
    Generic,
    Invalid,
    InvalidEnum(Rc<Enum>),
    Unknown,
}

macro_rules! compute_type_application {
    ($self:ident, $slice_type:expr, $from_alias_definition:expr, $method:ident $args:tt) => {{
        let mut on_type_var = |i_s: &InferenceState, _: &_, type_var_like: TypeVarLike, current_callable: Option<_>| {
            if let Some(result) = i_s.find_parent_type_var(&type_var_like) {
                if $from_alias_definition {
                    $slice_type.as_node_ref().add_issue(
                        i_s,
                        IssueKind::BoundTypeVarInAlias{
                            name: Box::from(type_var_like.name(i_s.db))
                        },
                    );
                } else {
                    return result
                }
            }
            if $from_alias_definition || current_callable.is_some(){
                TypeVarCallbackReturn::NotFound { allow_late_bound_callables: !$from_alias_definition }
            } else {
                TypeVarCallbackReturn::UnboundTypeVar
            }
        };
        let mut tcomp = TypeComputation::new(
            $self.i_s,
            $self.file,
            $slice_type.as_node_ref().as_link(),
            &mut on_type_var,
            match $from_alias_definition {
                false => TypeComputationOrigin::TypeApplication,
                true => TypeComputationOrigin::TypeAlias,
            }
        );
        let t = tcomp.$method $args;
        match t {
            TypeContent::SimpleGeneric{class_link, generics, ..} => {
                Inferred::from_type(Type::Type(Rc::new(Type::new_class(class_link, generics))))
            }
            TypeContent::Type(mut type_) => {
                let type_var_likes = tcomp.into_type_vars(|_, recalculate_type_vars| {
                    type_ = recalculate_type_vars(&type_);
                });
                if type_var_likes.len() > 0 && $from_alias_definition  {
                    debug_assert!($from_alias_definition);
                    Inferred::new_unsaved_complex(ComplexPoint::TypeAlias(Box::new(TypeAlias::new_valid(
                        type_var_likes,
                        $slice_type.as_node_ref().as_link(),
                        None,
                        Rc::new(type_),
                        false,
                    ))))
                } else {
                    Inferred::from_type(Type::Type(Rc::new(type_)))
                }
            },
            TypeContent::Unknown(cause) => Inferred::new_any(cause.into()),
            TypeContent::InvalidVariable(var) => {
                var.add_issue(
                    $self.i_s.db,
                    |issue| $slice_type.as_node_ref().add_issue($self.i_s, issue),
                    tcomp.origin
                );
                Inferred::new_any_from_error()
            }
            _ => {
                // Currently this is only the case with Annotated. Not sure if this is correct in
                // the future, but for now returning typing._SpecialForm seems fine.
                Inferred::from_type($self.i_s.db.python_state.typing_special_form_type())
            }
        }
    }}
}

fn type_computation_for_variable_annotation(
    i_s: &InferenceState,
    _manager: &TypeVarManager<PointLink>,
    type_var_like: TypeVarLike,
    current_callable: Option<PointLink>,
) -> TypeVarCallbackReturn {
    if let Some(result) = i_s.find_parent_type_var(&type_var_like) {
        return result;
    }
    match current_callable {
        Some(_) => TypeVarCallbackReturn::NotFound {
            allow_late_bound_callables: true,
        },
        None => TypeVarCallbackReturn::UnboundTypeVar,
    }
}

pub struct TypeComputation<'db, 'file, 'i_s, 'c> {
    name_resolution: NameResolution<'db, 'file, 'i_s>,
    for_definition: PointLink,
    current_callable: Option<PointLink>,
    type_var_manager: TypeVarManager<PointLink>,
    type_var_callback: TypeVarCallback<'db, 'c>,
    // This is only for type aliases. Type aliases are also allowed to be used by Python itself.
    // It's therefore unclear if type inference or type computation is needed. So once we encounter
    // a type alias we check in the database if the error was already calculated and set the flag.
    errors_already_calculated: bool,
    pub has_type_vars_or_self: bool,
    origin: TypeComputationOrigin,
    is_recursive_alias: bool,
}

impl<'db: 'file, 'file, 'i_s> std::ops::Deref for TypeComputation<'db, 'file, 'i_s, '_> {
    type Target = NameResolution<'db, 'file, 'i_s>;

    fn deref(&self) -> &Self::Target {
        &self.name_resolution
    }
}

impl<'db: 'x + 'file, 'file, 'i_s, 'c, 'x> TypeComputation<'db, 'file, 'i_s, 'c> {
    pub fn new(
        i_s: &'i_s InferenceState<'db, 'i_s>,
        file: &'file PythonFile,
        for_definition: PointLink,
        type_var_callback: TypeVarCallback<'db, 'c>,
        origin: TypeComputationOrigin,
    ) -> Self {
        Self {
            name_resolution: file.name_resolution_for_types(i_s),
            for_definition,
            current_callable: None,
            type_var_manager: TypeVarManager::default(),
            type_var_callback,
            errors_already_calculated: false,
            has_type_vars_or_self: false,
            origin,
            is_recursive_alias: false,
        }
    }

    fn compute_forward_reference(
        &mut self,
        start: CodeIndex,
        code: Cow<str>,
    ) -> TypeContent<'db, 'db> {
        let f = self
            .file
            .ensure_forward_reference_file(self.i_s.db, start, code);
        if let Some(star_exprs) = f.tree.maybe_star_expressions() {
            let compute_type =
                |comp: &mut TypeComputation<'db, '_, '_, '_>| match star_exprs.unpack() {
                    StarExpressionContent::Expression(expr) => comp.compute_type(expr),
                    _ => TypeContent::InvalidVariable(InvalidVariableType::Other),
                };
            let old_manager = std::mem::take(&mut self.type_var_manager);
            let mut comp = TypeComputation {
                name_resolution: f.name_resolution_for_types(self.i_s),
                type_var_manager: old_manager,
                current_callable: self.current_callable,
                for_definition: self.for_definition,
                type_var_callback: self.type_var_callback,
                errors_already_calculated: self.errors_already_calculated,
                has_type_vars_or_self: false,
                origin: self.origin,
                is_recursive_alias: false,
            };
            let type_ = compute_type(&mut comp);
            self.type_var_manager = comp.type_var_manager;
            self.has_type_vars_or_self |= comp.has_type_vars_or_self;
            self.is_recursive_alias |= comp.is_recursive_alias;
            type_
        } else {
            debug!("Found non-expression in annotation: {}", f.tree.code());
            for s in f.tree.root().iter_stmt_likes() {
                if let StmtLikeContent::Error(_) = s.node {
                    // There is invalid syntax (issue added previously)
                    return TypeContent::UNKNOWN_REPORTED;
                }
            }
            self.file.add_issue(
                self.i_s,
                Issue {
                    start_position: start,
                    end_position: start + f.tree.code().len() as CodeIndex,
                    kind: IssueKind::InvalidSyntaxInTypeAnnotation,
                },
            );
            TypeContent::UNKNOWN_REPORTED
        }
    }

    pub fn compute_base_class(&mut self, expr: Expression) -> CalculatedBaseClass {
        let calculated = self.compute_type(expr);
        match calculated {
            TypeContent::SpecialType(SpecialType::GenericWithGenerics) => {
                CalculatedBaseClass::Generic
            }
            TypeContent::SpecialType(SpecialType::Protocol) => CalculatedBaseClass::Protocol,
            TypeContent::SpecialType(SpecialType::ProtocolWithGenerics) => {
                CalculatedBaseClass::Protocol
            }
            TypeContent::SpecialCase(Specific::TypingNamedTuple) => {
                CalculatedBaseClass::NewNamedTuple
            }
            TypeContent::SpecialCase(Specific::TypingTypedDict) => CalculatedBaseClass::TypedDict,
            TypeContent::SpecialType(SpecialType::BuiltinsType) => {
                CalculatedBaseClass::Type(Type::new_class(
                    self.i_s.db.python_state.bare_type_node_ref().as_link(),
                    ClassGenerics::None,
                ))
            }
            TypeContent::InvalidVariable(InvalidVariableType::ParamNameAsBaseClassAny(_)) => {
                // TODO what is this case?
                CalculatedBaseClass::Unknown
            }
            TypeContent::ParamSpec(_)
            | TypeContent::InvalidVariable(_)
            | TypeContent::SpecialType(SpecialType::TypingType) => CalculatedBaseClass::Invalid,
            TypeContent::Type(Type::Enum(e)) => CalculatedBaseClass::InvalidEnum(e),
            _ => {
                let type_ = self.as_type(calculated, NodeRef::new(self.file, expr.index()));
                self.compute_base_class_for_type(expr, type_)
            }
        }
    }

    fn compute_base_class_for_type(
        &mut self,
        expr: Expression,
        type_: Type,
    ) -> CalculatedBaseClass {
        match type_ {
            Type::Class(..) | Type::Tuple(_) | Type::TypedDict(_) | Type::Dataclass(_) => {
                CalculatedBaseClass::Type(type_)
            }
            Type::Type(t) if matches!(t.as_ref(), Type::Any(_)) => {
                CalculatedBaseClass::Type(Type::new_class(
                    self.i_s.db.python_state.bare_type_node_ref().as_link(),
                    ClassGenerics::None,
                ))
            }
            Type::NamedTuple(nt) => {
                // TODO performance: this is already an Rc and should not need to be
                // duplicated.
                CalculatedBaseClass::NamedTuple(nt)
            }
            Type::Any(_) => CalculatedBaseClass::Unknown,
            Type::NewType(_) => {
                self.add_issue_for_index(expr.index(), IssueKind::CannotSubclassNewType);
                CalculatedBaseClass::Unknown
            }
            Type::RecursiveType(t) => {
                self.compute_base_class_for_type(expr, t.calculated_type(self.i_s.db).clone())
            }
            _ => CalculatedBaseClass::Invalid,
        }
    }

    pub fn cache_param_annotation(
        &mut self,
        param_annotation: ParamAnnotation,
        param_kind: ParamKind,
        previous_param: Option<Param>,
        is_implicit_optional: bool,
    ) {
        match param_annotation.maybe_starred() {
            Ok(starred) => {
                let from = NodeRef::new(self.file, starred.index());
                self.cache_annotation_or_type_comment_detailed(
                    param_annotation.index(),
                    |slf| slf.compute_type_expression_part(starred.expression_part()),
                    from,
                    false,
                    Some(&|slf, tc| {
                        let wrapped = slf.wrap_in_unpack(tc, from);
                        Type::Tuple(Tuple::new(
                            slf.use_tuple_unpack(wrapped, from).into_tuple_args(),
                        ))
                    }),
                )
            }
            Err(expr) => match param_kind {
                ParamKind::Star => self.cache_annotation_or_type_comment(
                    param_annotation.index(),
                    expr,
                    false,
                    Some(&|slf, t| {
                        slf.wrap_star(t, NodeRef::new(self.name_resolution.file, expr.index()))
                    }),
                ),
                ParamKind::StarStar => self.cache_annotation_or_type_comment(
                    param_annotation.index(),
                    expr,
                    false,
                    Some(&|slf, t| slf.wrap_star_star(t, expr, previous_param)),
                ),
                _ => self.cache_annotation(param_annotation.index(), expr, is_implicit_optional),
            },
        }
    }

    fn cache_annotation(
        &mut self,
        annotation_index: NodeIndex,
        expr: Expression,
        is_implicit_optional: bool,
    ) {
        self.cache_annotation_or_type_comment(annotation_index, expr, is_implicit_optional, None)
    }

    fn wrap_star(&mut self, tc: TypeContent, from: NodeRef) -> Type {
        match tc {
            TypeContent::Unpacked(TypeOrUnpack::Type(t @ Type::Tuple(_))) => t,
            TypeContent::Unpacked(TypeOrUnpack::TypeVarTuple(tvt)) => {
                Type::Tuple(Tuple::new(TupleArgs::WithUnpack(WithUnpack {
                    before: Rc::from([]),
                    unpack: TupleUnpack::TypeVarTuple(tvt),
                    after: Rc::from([]),
                })))
            }
            TypeContent::Unpacked(TypeOrUnpack::Type(t)) => {
                self.add_issue(
                    from,
                    IssueKind::VariadicUnpackMustBeTupleLike {
                        actual: t.format_short(self.i_s.db),
                    },
                );
                Type::Tuple(Tuple::new_arbitrary_length_with_any_from_error())
            }
            TypeContent::Unpacked(TypeOrUnpack::Unknown(_)) => {
                Type::Tuple(Tuple::new_arbitrary_length_with_any())
            }
            TypeContent::ParamSpecAttr {
                usage,
                name: "args",
            } => Type::ParamSpecArgs(usage),
            TypeContent::ParamSpecAttr { usage, .. } => {
                self.add_issue(
                    from,
                    IssueKind::UseParamSpecArgs {
                        name: usage.param_spec.name(self.i_s.db).into(),
                    },
                );
                Type::ParamSpecArgs(usage)
            }
            _ => Type::Tuple(Tuple::new_arbitrary_length(self.as_type(tc, from))),
        }
    }

    fn wrap_star_star(
        &mut self,
        tc: TypeContent,
        expr: Expression,
        previous_param: Option<Param>,
    ) -> Type {
        let from = NodeRef::new(self.file, expr.index());
        let new_dct = |t| {
            new_class!(
                self.name_resolution
                    .i_s
                    .db
                    .python_state
                    .dict_node_ref()
                    .as_link(),
                self.name_resolution.i_s.db.python_state.str_type(),
                t,
            )
        };
        let param_spec_error = |usage: &ParamSpecUsage, name| {
            let n = usage.param_spec.name(self.i_s.db).into();
            let issue = if name == "kwargs" {
                IssueKind::ParamSpecParamsNeedBothStarAndStarStar { name: n }
            } else {
                IssueKind::UseParamSpecKwargs { name: n }
            };
            self.add_issue(from, issue);
            new_dct(Type::ERROR)
        };

        let previous_param_annotation = previous_param.and_then(|param| param.annotation());
        let cached_previous_param = previous_param_annotation
            .map(|annotation| self.use_cached_param_annotation_type(annotation));
        if let Some(Type::ParamSpecArgs(usage_before)) = cached_previous_param.as_deref() {
            match tc {
                TypeContent::ParamSpecAttr {
                    usage,
                    name: "kwargs",
                } if *usage_before == usage => {
                    return Type::ParamSpecKwargs(usage);
                }
                _ => {
                    // Now that we know we have a **P.kwargs, is there a P.args before it?
                    let new_t = Type::Tuple(Tuple::new_arbitrary_length(Type::ERROR));
                    let star_annotation = previous_param_annotation
                        .unwrap()
                        .maybe_starred()
                        .err()
                        .unwrap();
                    let overwrite = NodeRef::new(self.file, star_annotation.index());
                    overwrite.insert_type(new_t);
                    return param_spec_error(
                        usage_before,
                        match tc {
                            TypeContent::ParamSpecAttr { name, .. } => name,
                            _ => "kwargs",
                        },
                    );
                }
            }
        }
        match tc {
            TypeContent::Unpacked(TypeOrUnpack::Type(t @ Type::TypedDict(_))) => t,
            TypeContent::Unpacked(_) => {
                self.add_issue(from, IssueKind::UnpackItemInStarStarMustBeTypedDict);
                new_class!(
                    self.i_s.db.python_state.dict_node_ref().as_link(),
                    self.i_s.db.python_state.str_type(),
                    Type::ERROR,
                )
            }
            TypeContent::ParamSpecAttr { usage, name } => {
                if let Some(previous_param) = previous_param {
                    if previous_param.kind() == ParamKind::KeywordOnly {
                        // Things like *args: P.args, x: int, **kwargs: P.kwargs
                        self.add_issue(
                            NodeRef::new(self.file, previous_param.name_def().index()),
                            IssueKind::ParamSpecKwParamNotAllowed,
                        );
                        return new_dct(Type::ERROR);
                    }
                }
                param_spec_error(&usage, name)
            }
            _ => new_dct(self.as_type(tc, from)),
        }
    }

    pub fn cache_return_annotation(
        &mut self,
        annotation: ReturnAnnotation,
    ) -> Option<TypeGuardInfo> {
        let expr = annotation.expression();
        let mut type_guard = None;
        self.cache_annotation_or_type_comment_detailed(
            annotation.index(),
            |slf| match slf.compute_type(expr) {
                TypeContent::TypeGuardInfo(guard) => {
                    type_guard = Some(guard);
                    TypeContent::Type(self.name_resolution.i_s.db.python_state.bool_type())
                }
                type_content => type_content,
            },
            NodeRef::new(self.file, expr.index()),
            false,
            None,
        );
        type_guard
    }

    fn cache_annotation_or_type_comment(
        &mut self,
        annotation_index: NodeIndex,
        expr: Expression,
        is_implicit_optional: bool,
        map_type_callback: MapAnnotationTypeCallback,
    ) {
        self.cache_annotation_or_type_comment_detailed(
            annotation_index,
            |slf| slf.compute_type(expr),
            NodeRef::new(self.file, expr.index()),
            is_implicit_optional,
            map_type_callback,
        )
    }

    fn cache_annotation_or_type_comment_detailed<'tmp>(
        &mut self,
        annotation_index: NodeIndex,
        as_type: impl FnOnce(&mut Self) -> TypeContent<'db, 'tmp>,
        type_storage_node_ref: NodeRef,
        is_implicit_optional: bool,
        map_type_callback: MapAnnotationTypeCallback,
    ) {
        let annotation_node_ref = NodeRef::new(self.file, annotation_index);
        if annotation_node_ref.point().calculated() {
            return;
        }
        let type_ = as_type(self);

        let mut is_class_var = false;
        let mut is_final = false;
        let i_s = self.i_s;
        let uses_class_generics = |class: Class, t: &Type| {
            let mut uses_class_generics = false;
            t.search_type_vars(&mut |usage| {
                if usage.in_definition() == class.node_ref.as_link() {
                    uses_class_generics = true
                }
            });
            uses_class_generics
        };
        let mut type_ = match map_type_callback {
            Some(map_type_callback) => map_type_callback(self, type_),
            None => match type_ {
                TypeContent::SimpleGeneric { .. } | TypeContent::Class { .. }
                    if !is_implicit_optional =>
                {
                    debug_assert!(type_storage_node_ref.point().calculated());
                    // It might already have been calculated (because of recursions), in that case
                    // just don't set it. We only ever want to use this case when everything is
                    // clean (no recursions, type vars, etc.)
                    if !annotation_node_ref.point().calculated() {
                        annotation_node_ref.set_point(Point::new_specific(
                            Specific::AnnotationOrTypeCommentSimpleClassInstance,
                            Locality::Todo,
                        ));
                    }
                    return;
                }
                TypeContent::SpecialCase(Specific::TypingClassVar)
                    if !matches!(
                        self.origin,
                        TypeComputationOrigin::AssignmentTypeCommentOrAnnotation { .. }
                    ) || i_s.current_class().is_none()
                        || i_s.current_function().is_some() =>
                {
                    self.add_issue(
                        type_storage_node_ref,
                        IssueKind::ClassVarOnlyInAssignmentsInClass,
                    );
                    Type::ERROR
                }
                TypeContent::SpecialCase(
                    specific @ (Specific::TypingTypeAlias
                    | Specific::TypingFinal
                    | Specific::TypingClassVar),
                ) if matches!(
                    self.origin,
                    TypeComputationOrigin::AssignmentTypeCommentOrAnnotation { .. }
                ) =>
                {
                    debug_assert!(!is_implicit_optional);
                    let specific = match specific {
                        Specific::TypingTypeAlias => {
                            let TypeComputationOrigin::AssignmentTypeCommentOrAnnotation {
                                is_initialized,
                                type_comment,
                            } = self.origin
                            else {
                                unreachable!()
                            };
                            if !is_initialized {
                                // e.g. x: TypeAlias
                                self.add_issue(
                                    type_storage_node_ref,
                                    IssueKind::TypeAliasRightSideNeeded,
                                );
                                None
                            } else if type_comment {
                                // Simply ignore stuff like `x = int | str # type: TypeAlias` for now
                                self.add_issue(
                                    type_storage_node_ref,
                                    IssueKind::TypeAliasInTypeCommentNotSupported,
                                );
                                None
                            } else {
                                Some(Specific::AnnotationTypeAlias)
                            }
                        }
                        Specific::TypingFinal => {
                            self.add_issue_if_final_attribute_in_wrong_place(type_storage_node_ref);
                            Some(Specific::AnnotationOrTypeCommentFinal)
                        }
                        Specific::TypingClassVar => Some(Specific::AnnotationOrTypeCommentClassVar),
                        _ => unreachable!(),
                    };
                    if let Some(specific) = specific {
                        annotation_node_ref
                            .set_point(Point::new_specific(specific, Locality::Todo));
                        return;
                    } else {
                        Type::ERROR
                    }
                }
                TypeContent::ClassVar(t) => {
                    is_class_var = true;
                    if !matches!(
                        self.origin,
                        TypeComputationOrigin::AssignmentTypeCommentOrAnnotation { .. }
                    ) {
                        self.add_issue(
                            type_storage_node_ref,
                            IssueKind::ClassVarOnlyInAssignmentsInClass,
                        );
                        Type::ERROR
                    } else if self.has_type_vars_or_self {
                        let i_s = self.i_s;
                        let class = i_s.current_class().unwrap();
                        if uses_class_generics(class, &t) {
                            self.add_issue(
                                type_storage_node_ref,
                                IssueKind::ClassVarCannotContainTypeVariables,
                            );
                            Type::ERROR
                        } else if !class.type_vars(i_s).is_empty() && t.has_self_type(i_s.db) {
                            self.add_issue(
                                type_storage_node_ref,
                                IssueKind::ClassVarCannotContainSelfTypeInGenericClass,
                            );
                            t
                        } else {
                            t
                        }
                    } else {
                        t
                    }
                }
                TypeContent::Final(t) => {
                    if let TypeComputationOrigin::AssignmentTypeCommentOrAnnotation {
                        is_initialized,
                        ..
                    } = self.origin
                    {
                        is_final = true;
                        if !is_initialized
                            && !self.file.is_stub()
                            && !self.final_is_assigned_in_init(annotation_node_ref)
                        {
                            self.add_issue(
                                type_storage_node_ref,
                                IssueKind::FinalNameMustBeInitializedWithValue,
                            );
                        }
                        self.add_issue_if_final_attribute_in_wrong_place(type_storage_node_ref);
                        if i_s
                            .current_class()
                            .is_some_and(|class| uses_class_generics(class, &t))
                        {
                            self.add_issue(
                                type_storage_node_ref,
                                IssueKind::FinalInClassBodyCannotDependOnTypeVariables,
                            );
                            Type::ERROR
                        } else {
                            t
                        }
                    } else {
                        self.as_type(TypeContent::Final(t), type_storage_node_ref)
                    }
                }
                _ => self.as_type(type_, type_storage_node_ref),
            },
        };
        if is_implicit_optional {
            type_.make_optional()
        }
        type_storage_node_ref.insert_type(type_);
        annotation_node_ref.set_point(Point::new_specific(
            if is_class_var {
                Specific::AnnotationOrTypeCommentClassVar
            } else if is_final {
                Specific::AnnotationOrTypeCommentFinal
            } else if self.has_type_vars_or_self {
                Specific::AnnotationOrTypeCommentWithTypeVars
            } else {
                Specific::AnnotationOrTypeCommentWithoutTypeVars
            },
            Locality::Todo,
        ));
    }

    fn add_issue_if_final_attribute_in_wrong_place(&self, from: NodeRef) {
        if self
            .i_s
            .current_function()
            .is_some_and(|func| func.class.is_some() && func.name() != "__init__")
        {
            self.add_issue(from, IssueKind::FinalAttributeOnlyValidInClassBodyOrInit);
        }
    }

    fn final_is_assigned_in_init(&self, annotation_node_ref: NodeRef) -> bool {
        let Some(class) = self.i_s.in_class_scope() else {
            return false;
        };
        let Some(name_def) = annotation_node_ref.as_annotation().maybe_assignment_name() else {
            return false;
        };
        // TODO this is not correctly looking up Final assignments. To do this correctly we would
        // probably need to check if we are in __init__.
        class
            .class_storage
            .self_symbol_table
            .lookup_symbol(name_def.as_code())
            .is_some_and(|symbol| {
                func_of_self_symbol(class.node_ref.file, symbol)
                    .name_def()
                    .as_code()
                    == "__init__"
            })
    }

    fn as_type(&mut self, type_: TypeContent, node_ref: NodeRef) -> Type {
        self.as_type_or_error(type_, node_ref)
            .unwrap_or(Type::ERROR)
    }

    fn as_type_or_error(&mut self, type_: TypeContent, node_ref: NodeRef) -> Option<Type> {
        let db = self.i_s.db;
        match type_ {
            TypeContent::Class {
                node_ref: class_node_ref,
                ..
            } => {
                let cls = Class::with_undefined_generics(class_node_ref);
                if self.flags().disallow_any_generics
                    && cls.type_vars(self.i_s).contains_non_default()
                {
                    self.add_issue(
                        node_ref,
                        IssueKind::MissingTypeParameters {
                            name: cls.name().into(),
                        },
                    );
                }
                return Some(cls.as_type(db));
            }
            TypeContent::SimpleGeneric {
                class_link,
                generics,
                ..
            } => return Some(Type::new_class(class_link, generics)),
            TypeContent::Type(d) => return Some(d),
            TypeContent::Dataclass(d) => {
                return Some(Type::Dataclass({
                    let class = d.class(db);
                    if class.use_cached_type_vars(db).is_empty() {
                        d
                    } else {
                        Dataclass::new(
                            class.as_generic_class(db), // We need to make all the generics Any
                            d.options.clone(),
                        )
                    }
                }));
            }
            TypeContent::NamedTuple(nt) => {
                return {
                    if nt.__new__.type_vars.is_empty() {
                        Some(Type::NamedTuple(nt))
                    } else {
                        let defined_at = nt.__new__.defined_at;
                        Type::NamedTuple(nt).replace_type_var_likes(db, &mut |usage| {
                            (usage.in_definition() == defined_at)
                                .then(|| usage.as_any_generic_item(db))
                        })
                    }
                };
            }
            TypeContent::TypedDictDefinition(td) => {
                return match &td.generics {
                    TypedDictGenerics::None => Some(Type::TypedDict(td)),
                    TypedDictGenerics::NotDefinedYet(_) => {
                        if self.flags().disallow_any_generics {
                            self.add_issue(
                                node_ref,
                                IssueKind::MissingTypeParameters {
                                    name: td.name.unwrap().as_str(db).into(),
                                },
                            );
                        }
                        Type::TypedDict(td).replace_type_var_likes(db, &mut |usage| {
                            Some(usage.as_any_generic_item(db))
                        })
                    }
                    TypedDictGenerics::Generics(_) => unreachable!(),
                }
            }
            TypeContent::Module(file) => {
                self.add_module_issue(node_ref, &file.qualified_name(db));
            }
            TypeContent::Namespace(n) => {
                self.add_module_issue(node_ref, &n.qualified_name());
            }
            TypeContent::TypeAlias(a) => {
                if self.flags().disallow_any_generics && a.type_vars.contains_non_default() {
                    self.add_issue(
                        node_ref,
                        IssueKind::MissingTypeParameters {
                            name: a.name(db).unwrap().into(),
                        },
                    );
                }
                self.is_recursive_alias |= a.is_recursive();
                return Some(a.as_type_and_set_type_vars_any(db));
            }
            TypeContent::SpecialType(m) => match m {
                SpecialType::Callable => {
                    if self.flags().disallow_any_generics {
                        self.add_issue(
                            node_ref,
                            IssueKind::MissingTypeParameters {
                                name: "Callable".into(),
                            },
                        );
                    }
                    return Some(Type::Callable(
                        self.i_s.db.python_state.any_callable_from_error.clone(),
                    ));
                }
                SpecialType::BuiltinsType | SpecialType::TypingType => {
                    if self.flags().disallow_any_generics && matches!(m, SpecialType::TypingType) {
                        self.add_issue(
                            node_ref,
                            IssueKind::MissingTypeParameters {
                                name: "Type".into(),
                            },
                        );
                    }
                    return Some(db.python_state.type_of_any.clone());
                }
                SpecialType::Tuple => {
                    if self.flags().disallow_any_generics {
                        self.add_issue(
                            node_ref,
                            IssueKind::MissingTypeParameters {
                                name: "Tuple".into(),
                            },
                        );
                    }
                    return Some(Type::Tuple(Tuple::new_arbitrary_length_with_any()));
                }
                SpecialType::LiteralString => {
                    return Some(Type::new_class(
                        db.python_state.str_node_ref().as_link(),
                        ClassGenerics::None,
                    ))
                }
                SpecialType::Literal => {
                    self.add_issue(
                        node_ref,
                        IssueKind::InvalidType(Box::from(
                            "Literal[...] must have at least one parameter",
                        )),
                    );
                }
                SpecialType::Unpack => {
                    self.add_issue(node_ref, IssueKind::UnpackRequiresExactlyOneArgument);
                }
                _ => {
                    self.add_issue(node_ref, IssueKind::InvalidType(Box::from("Invalid type")));
                }
            },
            TypeContent::SpecialCase(specific) => match specific {
                Specific::TypingAny => return Some(Type::Any(AnyCause::Explicit)),
                Specific::TypingNeverOrNoReturn => return Some(Type::Never(NeverCause::Explicit)),
                Specific::TypingSelf => self.add_issue(
                    node_ref,
                    match self.origin {
                        TypeComputationOrigin::TypedDictMember => {
                            IssueKind::TypedDictSelfNotAllowed
                        }
                        TypeComputationOrigin::NamedTupleMember => {
                            IssueKind::NamedTupleSelfNotAllowed
                        }
                        TypeComputationOrigin::TypeApplication
                        | TypeComputationOrigin::TypeAlias => IssueKind::SelfTypeInTypeAliasTarget,
                        TypeComputationOrigin::Other | TypeComputationOrigin::BaseClass => {
                            IssueKind::SelfTypeOutsideOfClass
                        }
                        _ => {
                            if let Some(class) = self.i_s.current_class() {
                                if class.is_metaclass(db) {
                                    IssueKind::SelfTypeInMetaclass
                                } else {
                                    self.has_type_vars_or_self = true;
                                    return Some(Type::Self_);
                                }
                            } else {
                                IssueKind::SelfTypeOutsideOfClass
                            }
                        }
                    },
                ),
                Specific::TypingNamedTuple => {
                    return Some(db.python_state.typing_named_tuple_type())
                }
                Specific::TypingOptional => {
                    self.add_issue(
                        node_ref,
                        IssueKind::MustHaveOneArgument {
                            name: "Optional[...]",
                        },
                    );
                }
                Specific::TypingClassVar => {
                    self.add_issue(node_ref, IssueKind::ClassVarNestedInsideOtherType);
                }
                Specific::TypingFinal => self.add_issue(node_ref, IssueKind::FinalInWrongPlace),
                Specific::TypingAnnotated => {
                    self.add_issue(
                        node_ref,
                        IssueKind::InvalidType(Box::from(
                            "Annotated[...] must have exactly one type argument and at least one annotation",
                        )),
                    );
                }
                Specific::TypingTypeGuard => self.add_issue(
                    node_ref,
                    IssueKind::MustHaveOneArgument { name: "TypeGuard" },
                ),
                Specific::TypingTypeIs => {
                    self.add_issue(node_ref, IssueKind::MustHaveOneArgument { name: "TypeIs" })
                }
                _ => self.add_issue(node_ref, IssueKind::InvalidType(Box::from("Invalid type"))),
            },
            TypeContent::TypeVarTuple(t) => self.add_issue(
                node_ref,
                IssueKind::InvalidType(
                    format!(
                        "TypeVarTuple \"{}\" is only valid with an unpack",
                        t.type_var_tuple.name(self.i_s.db),
                    )
                    .into(),
                ),
            ),
            TypeContent::ParamSpec(p) => {
                self.add_issue(
                    node_ref,
                    IssueKind::InvalidType(
                        format!(
                            "Invalid location for ParamSpec \"{}\"",
                            p.param_spec.name(self.i_s.db),
                        )
                        .into(),
                    ),
                );
                self.add_issue(
                    node_ref,
                    IssueKind::Note(Box::from(
                        "You can use ParamSpec as the first \
                                              argument to Callable, e.g., \"Callable[P, int]\"",
                    )),
                );
            }
            TypeContent::Unpacked(t) => {
                if !matches!(t, TypeOrUnpack::Unknown(_)) {
                    self.add_issue(node_ref, IssueKind::UnpackOnlyValidInVariadicPosition);
                }
            }
            TypeContent::Concatenate(_) => {
                self.add_issue(
                    node_ref,
                    IssueKind::InvalidType(Box::from("Invalid location for Concatenate")),
                );
                self.add_issue(
                    node_ref,
                    IssueKind::Note(Box::from(
                        "You can use Concatenate as the first argument to Callable",
                    )),
                );
            }
            // TODO here we would need to check if the generics are actually valid.
            TypeContent::RecursiveAlias(link) => {
                self.is_recursive_alias = true;
                let type_var_likes = &NodeRef::from_link(db, link)
                    .maybe_alias()
                    .unwrap()
                    .type_vars;
                return Some(Type::RecursiveType(Rc::new(RecursiveType::new(
                    link,
                    (!type_var_likes.is_empty())
                        .then(|| type_var_likes.as_any_generic_list(self.i_s.db)),
                ))));
            }
            TypeContent::RecursiveClass(class_ref) => {
                self.is_recursive_alias = true;
                let type_var_likes = class_ref.type_vars(self.i_s);
                return Some(Type::RecursiveType(Rc::new(RecursiveType::new(
                    class_ref.as_link(),
                    (!type_var_likes.is_empty())
                        .then(|| type_var_likes.as_any_generic_list(self.i_s.db)),
                ))));
            }
            TypeContent::TypeGuardInfo(_) => return Some(self.i_s.db.python_state.bool_type()),
            TypeContent::Unknown(_) => (),
            TypeContent::ClassVar(_) => {
                self.add_issue(node_ref, IssueKind::ClassVarNestedInsideOtherType);
            }
            TypeContent::EnumMember(m) => {
                let format_data = FormatData::new_short(self.i_s.db);
                self.add_issue(
                    node_ref,
                    IssueKind::InvalidType(
                        format!(
                            "Invalid type: try using {} instead?",
                            m.format(&format_data)
                        )
                        .into(),
                    ),
                );
            }
            TypeContent::Final(_) => self.add_issue(node_ref, IssueKind::FinalInWrongPlace),
            TypeContent::InvalidVariable(t) => {
                t.add_issue(self.i_s.db, |t| self.add_issue(node_ref, t), self.origin);
            }
            TypeContent::TypedDictMemberModifiers(m, _) => {
                let s = if m.required {
                    "Required"
                } else if m.not_required {
                    "NotRequired"
                } else if m.read_only {
                    "ReadOnly"
                } else {
                    unreachable!("The default case should never happen")
                };
                self.add_issue(
                    node_ref,
                    IssueKind::InvalidType(
                        format!("{s}[] can be only used in a TypedDict definition").into(),
                    ),
                );
            }
            TypeContent::ParamSpecAttr { usage, name } => {
                match name {
                    "args" => return Some(Type::ParamSpecArgs(usage)),
                    "kwargs" => return Some(Type::ParamSpecKwargs(usage)),
                    _ => (), // Error was added earlier
                }
            }
            TypeContent::TypedDictFieldModifier(m) => {
                self.add_issue(node_ref, IssueKind::MustHaveOneArgument { name: m.name() })
            }
            TypeContent::CallableParam(_) => {
                self.add_issue(node_ref, IssueKind::InvalidType(Box::from("Invalid type")))
            }
        }
        None
    }

    fn compute_named_expr_type(&mut self, named_expr: NamedExpression) -> Type {
        let t = self.compute_type(named_expr.expression());
        self.as_type(t, NodeRef::new(self.file, named_expr.index()))
    }

    fn compute_type(&mut self, expr: Expression<'x>) -> TypeContent<'db, 'x> {
        let type_content = match expr.unpack() {
            ExpressionContent::ExpressionPart(n) => self.compute_type_expression_part(n),
            _ => TypeContent::InvalidVariable(InvalidVariableType::Other),
        };
        if !self.file.points.get(expr.index()).calculated() {
            match &type_content {
                TypeContent::Class {
                    has_type_vars: true,
                    ..
                } => {
                    // This essentially means we have a class with Any generics. This is not what
                    // we want to be defined as a redirect and therefore we calculate Foo[Any, ...]
                    return TypeContent::Type(
                        self.as_type(type_content, NodeRef::new(self.file, expr.index())),
                    );
                }
                TypeContent::Class { node_ref, .. } => {
                    Inferred::from_saved_node_ref((*node_ref).into()).save_redirect(
                        self.i_s,
                        self.file,
                        expr.index(),
                    );
                }
                TypeContent::SimpleGeneric { node_ref, .. } => {
                    Inferred::from_saved_node_ref(*node_ref).save_redirect(
                        self.i_s,
                        self.file,
                        expr.index(),
                    );
                }
                _ => (),
            }
        }
        type_content
    }

    fn compute_slice_type_content(&mut self, slice: SliceOrSimple<'x>) -> TypeContent<'db, 'x> {
        match slice {
            SliceOrSimple::Simple(s) => self.compute_type(s.named_expr.expression()),
            SliceOrSimple::Slice(_) => TypeContent::InvalidVariable(InvalidVariableType::Slice),
            SliceOrSimple::Starred(s) => {
                let tc = self.compute_type(s.starred_expr.expression());
                TypeContent::Unpacked(self.wrap_in_unpack(tc, slice.as_node_ref()))
            }
        }
    }

    fn compute_slice_type(&mut self, slice: SliceOrSimple) -> Type {
        let t = self.compute_slice_type_content(slice);
        self.as_type(t, slice.as_node_ref())
    }

    fn use_tuple_unpack(
        &mut self,
        type_or_unpack: TypeOrUnpack,
        from: NodeRef,
    ) -> TypeCompTupleUnpack {
        match type_or_unpack {
            TypeOrUnpack::TypeVarTuple(tvt) => TypeCompTupleUnpack::TypeVarTuple(tvt),
            TypeOrUnpack::Type(Type::Tuple(tup)) => match Rc::unwrap_or_clone(tup).args {
                TupleArgs::WithUnpack(w) => TypeCompTupleUnpack::WithUnpack(w),
                TupleArgs::ArbitraryLen(t) => TypeCompTupleUnpack::ArbitraryLen(t),
                TupleArgs::FixedLen(ts) => TypeCompTupleUnpack::FixedLen(rc_slice_into_vec(ts)),
            },
            TypeOrUnpack::Unknown(cause) => {
                TypeCompTupleUnpack::ArbitraryLen(Box::new(Type::Any(cause.into())))
            }
            TypeOrUnpack::Type(t) => {
                self.add_issue(
                    from,
                    IssueKind::VariadicUnpackMustBeTupleLike {
                        actual: t.format_short(self.i_s.db),
                    },
                );
                TypeCompTupleUnpack::ArbitraryLen(Box::new(Type::ERROR))
            }
        }
    }

    fn convert_slice_type_or_tuple_unpack(&mut self, t: TypeContent, from: NodeRef) -> TuplePart {
        match t {
            TypeContent::Unpacked(unpacked) => {
                TuplePart::TupleUnpack(self.use_tuple_unpack(unpacked, from))
            }
            t => TuplePart::Type(self.as_type(t, from)),
        }
    }

    fn compute_type_expression_part(&mut self, node: ExpressionPart<'x>) -> TypeContent<'db, 'x> {
        match node {
            ExpressionPart::Atom(atom) => self.compute_type_atom(atom),
            ExpressionPart::Primary(primary) => self.compute_type_primary(primary),
            ExpressionPart::BitwiseOr(bitwise_or) => {
                let (a, b) = bitwise_or.unpack();
                let first = self.compute_type_expression_part(a);
                let second = self.compute_type_expression_part(b);

                let node_ref_a = NodeRef::new(self.file, a.index());
                let node_ref_b = NodeRef::new(self.file, b.index());
                if self.errors_already_calculated {
                    if self.flags().disallow_any_explicit {
                        if matches!(first, TypeContent::SpecialCase(Specific::TypingAny)) {
                            node_ref_a.add_issue(self.i_s, IssueKind::DisallowedAnyExplicit)
                        }
                        if matches!(second, TypeContent::SpecialCase(Specific::TypingAny)) {
                            node_ref_b.add_issue(self.i_s, IssueKind::DisallowedAnyExplicit)
                        }
                    }
                    if let Some(first) = self.as_type_or_error(first, node_ref_a) {
                        if let Some(second) = self.as_type_or_error(second, node_ref_b) {
                            return TypeContent::Type(first.union(second));
                        }
                    }
                    // We need to somehow track that it was an invalid union for checking aliases.
                    return TypeContent::InvalidVariable(InvalidVariableType::Other);
                }

                let first = self.as_type(first, node_ref_a);
                // TODO this should only merge in annotation contexts
                let second = self.as_type(second, node_ref_b);
                TypeContent::Type(first.union(second))
            }
            _ => TypeContent::InvalidVariable(InvalidVariableType::Other),
        }
    }

    fn compute_type_primary(&mut self, primary: Primary<'x>) -> TypeContent<'db, 'x> {
        let base = self.compute_type_primary_or_atom(primary.first());
        match primary.second() {
            PrimaryContent::Attribute(name) => self.compute_type_attribute(primary, base, name),
            PrimaryContent::Execution(details) => match base {
                TypeContent::SpecialCase(Specific::TypingNamedTuple) => {
                    let args = SimpleArgs::from_primary(*self.i_s, self.file, primary);
                    TypeContent::Type(match new_typing_named_tuple(self.i_s, &args, true) {
                        Some(rc) => Type::NamedTuple(rc),
                        None => Type::ERROR,
                    })
                }
                TypeContent::SpecialCase(Specific::CollectionsNamedTuple) => {
                    let args = SimpleArgs::from_primary(*self.i_s, self.file, primary);
                    TypeContent::Type(match new_collections_named_tuple(self.i_s, &args) {
                        Some(rc) => Type::NamedTuple(rc),
                        None => Type::ERROR,
                    })
                }
                TypeContent::SpecialCase(Specific::TypingTypedDict) => {
                    TypeContent::InvalidVariable(InvalidVariableType::InlineTypedDict)
                }
                TypeContent::Unknown(cause) => TypeContent::Unknown(cause),
                TypeContent::SpecialCase(
                    s @ (Specific::MypyExtensionsArg
                    | Specific::MypyExtensionsDefaultArg
                    | Specific::MypyExtensionsNamedArg
                    | Specific::MypyExtensionsDefaultNamedArg
                    | Specific::MypyExtensionsVarArg
                    | Specific::MypyExtensionsKwArg),
                ) => self.execute_mypy_extension_param(primary, s, details),
                _ => {
                    debug!("Invalid type execution: {base:?}");
                    TypeContent::InvalidVariable(InvalidVariableType::Execution {
                        was_class: matches!(
                            base,
                            TypeContent::SimpleGeneric { .. } | TypeContent::Class { .. }
                        ),
                    })
                }
            },
            PrimaryContent::GetItem(slice_type) => {
                let s = SliceType::new(self.file, primary.index(), slice_type);
                match base {
                    TypeContent::Class { node_ref, .. } => self.compute_type_get_item_on_class(
                        Class::with_undefined_generics(node_ref),
                        s,
                        Some(primary),
                    ),
                    TypeContent::Dataclass(d) => {
                        self.compute_type_get_item_on_dataclass(&d, s, Some(primary))
                    }
                    TypeContent::NamedTuple(nt) => self.compute_type_get_item_on_named_tuple(nt, s),
                    TypeContent::TypedDictDefinition(td) => {
                        self.compute_type_get_item_on_typed_dict(&td, s)
                    }
                    TypeContent::Type(d) => match d {
                        Type::Any(_) => TypeContent::Type(d),
                        _ => {
                            debug!("Invalid getitem used on {}", d.format_short(self.i_s.db));
                            TypeContent::InvalidVariable(InvalidVariableType::Other)
                        }
                    },
                    TypeContent::TypeAlias(m) => self.compute_type_get_item_on_alias(m, s),
                    TypeContent::SpecialType(special) => match special {
                        SpecialType::BuiltinsType | SpecialType::TypingType => {
                            self.compute_type_get_item_on_type(s)
                        }
                        SpecialType::Tuple => self.compute_type_get_item_on_tuple(s),
                        SpecialType::Protocol => {
                            self.expect_type_var_like_args(s, "Protocol");
                            TypeContent::SpecialType(SpecialType::ProtocolWithGenerics)
                        }
                        SpecialType::Generic => {
                            self.expect_type_var_like_args(s, "Generic");
                            TypeContent::SpecialType(SpecialType::GenericWithGenerics)
                        }
                        SpecialType::Callable => self.compute_type_get_item_on_callable(s),
                        SpecialType::Literal => self.compute_get_item_on_literal(s),
                        SpecialType::Unpack => self.compute_type_get_item_on_unpack(s),
                        SpecialType::Concatenate => self.compute_type_get_item_on_concatenate(s),
                        _ => TypeContent::InvalidVariable(InvalidVariableType::Other),
                    },
                    TypeContent::SpecialCase(specific) => match specific {
                        Specific::TypingUnion => self.compute_type_get_item_on_union(s),
                        Specific::TypingOptional => self.compute_type_get_item_on_optional(s),
                        Specific::TypingFinal => self.compute_type_get_item_on_final(s),
                        Specific::TypingClassVar => self.compute_get_item_on_class_var(s),
                        Specific::TypingAnnotated => self.compute_get_item_on_annotated(s),
                        Specific::TypingTypeGuard => self.compute_get_item_on_type_guard(s, false),
                        Specific::TypingTypeIs => self.compute_get_item_on_type_guard(s, true),
                        Specific::MypyExtensionsFlexibleAlias => {
                            self.compute_get_item_on_flexible_alias(s)
                        }
                        Specific::TypingSelf => {
                            self.add_issue(
                                s.as_node_ref(),
                                IssueKind::InvalidType(Box::from(
                                    "Self type cannot have type arguments",
                                )),
                            );
                            TypeContent::Type(Type::ERROR)
                        }
                        _ => TypeContent::InvalidVariable(InvalidVariableType::Other),
                    },
                    TypeContent::RecursiveAlias(link) => {
                        self.is_recursive_alias = true;
                        let alias = &NodeRef::from_link(self.i_s.db, link).maybe_alias().unwrap();
                        let generics = self.compute_generics_for_alias(s, alias);
                        TypeContent::Type(Type::RecursiveType(Rc::new(RecursiveType::new(
                            link,
                            (!generics.is_empty())
                                .then(|| GenericsList::generics_from_vec(generics)),
                        ))))
                    }
                    TypeContent::RecursiveClass(class_node_ref) => {
                        let type_var_likes = class_node_ref.type_vars(self.i_s);
                        let mut generics = vec![];
                        self.compute_get_item_generics_on_class(
                            s,
                            s.iter(),
                            class_node_ref.name(),
                            type_var_likes,
                            &mut generics,
                        );
                        TypeContent::Type(Type::RecursiveType(Rc::new(RecursiveType::new(
                            class_node_ref.as_link(),
                            (!type_var_likes.is_empty())
                                .then(|| GenericsList::generics_from_vec(generics)),
                        ))))
                    }
                    TypeContent::InvalidVariable(t) => {
                        t.add_issue(
                            self.i_s.db,
                            |t| self.add_issue(s.as_node_ref(), t),
                            self.origin,
                        );
                        TypeContent::UNKNOWN_REPORTED
                    }
                    TypeContent::Unknown(cause) => TypeContent::Unknown(cause),
                    TypeContent::TypedDictFieldModifier(m) => {
                        self.compute_type_get_item_on_typed_dict_field_modifier(s, m)
                    }
                    _ => TypeContent::InvalidVariable(InvalidVariableType::Other),
                }
            }
        }
    }

    fn compute_type_attribute(
        &mut self,
        primary: Primary,
        base: TypeContent<'db, 'x>,
        name: Name<'x>,
    ) -> TypeContent<'db, 'x> {
        let db = self.i_s.db;
        match base {
            TypeContent::Module(f) => {
                if let Some((resolved, _)) = f
                    .name_resolution_for_types(&InferenceState::new(db))
                    .resolve_module_access(name.as_str(), |k| {
                        self.add_issue_for_index(name.index(), k)
                    })
                {
                    let result = self.point_resolution_to_type_name_lookup(resolved);
                    let tc = self.resolve_type_name_lookup(result, name.index());
                    debug!("Point resolution for module: {tc:?}");
                    tc
                } else {
                    self.add_issue_for_index(primary.index(), IssueKind::TypeNotFound);
                    self.file.points.set(
                        name.index(),
                        Point::new_specific(Specific::AnyDueToError, Locality::Todo),
                    );
                    TypeContent::UNKNOWN_REPORTED
                }
            }
            TypeContent::Namespace(n) => match namespace_import(db, self.file, &n, name.as_str()) {
                Some(ImportResult::File(file_index)) => {
                    let file = db.loaded_python_file(file_index);
                    TypeContent::Module(file)
                }
                Some(ImportResult::Namespace(ns)) => TypeContent::Namespace(ns),
                Some(ImportResult::PyTypedMissing) => TypeContent::UNKNOWN_REPORTED,
                None => {
                    self.add_issue_for_index(primary.index(), IssueKind::TypeNotFound);
                    TypeContent::UNKNOWN_REPORTED
                }
            },
            TypeContent::Class { node_ref, .. } => {
                let cls = ClassInitializer::from_node_ref(node_ref);
                self.check_attribute_on_class(cls, primary, name)
            }
            TypeContent::SimpleGeneric { class_link, .. } => {
                let cls = ClassInitializer::from_link(db, class_link);
                self.check_attribute_on_class(cls, primary, name)
            }
            TypeContent::Type(t) => match t {
                Type::Any(cause) => TypeContent::Type(Type::Any(cause)),
                Type::Enum(e) => match Enum::lookup(&e, db, name.as_str(), false) {
                    Some(m) => TypeContent::EnumMember(m),
                    _ => {
                        let content = TypeContent::Class {
                            node_ref: ClassNodeRef::from_link(db, e.class),
                            has_type_vars: false, // Enums have no type vars ever.
                        };
                        self.compute_type_attribute(primary, content, name)
                    }
                },
                _ => TypeContent::InvalidVariable(InvalidVariableType::Other),
            },
            TypeContent::ParamSpec(usage) => {
                if !matches!(name.as_code(), "args" | "kwargs") {
                    self.add_issue_for_index(primary.index(), IssueKind::TypeNotFound);
                }
                // Return even the error cases to be able to give more hints later.
                TypeContent::ParamSpecAttr {
                    usage,
                    name: name.as_code(),
                }
            }
            TypeContent::InvalidVariable(t) => TypeContent::InvalidVariable(t),
            TypeContent::Unknown(cause) => TypeContent::Unknown(cause),
            _ => TypeContent::InvalidVariable(InvalidVariableType::Other),
        }
    }

    fn check_attribute_on_class(
        &mut self,
        cls: ClassInitializer,
        primary: Primary,
        name: Name<'x>,
    ) -> TypeContent<'db, 'x> {
        if let Some(pr) = self.lookup_type_name_on_class(cls, name) {
            let tnl = self.point_resolution_to_type_name_lookup(pr);
            self.resolve_type_name_lookup(tnl, name.index())
        } else {
            self.add_issue_for_index(primary.index(), IssueKind::TypeNotFound);
            TypeContent::UNKNOWN_REPORTED
        }
    }

    fn compute_generics_for_alias(
        &mut self,
        slice_type: SliceType,
        alias: &TypeAlias,
    ) -> Vec<GenericItem> {
        let mut generics = vec![];
        self.calculate_type_arguments(
            slice_type,
            &mut generics,
            slice_type.iter(),
            &alias.type_vars,
            &|| {
                alias
                    .name(self.name_resolution.i_s.db)
                    .unwrap_or("<Alias>")
                    .into()
            },
            |slf: &mut Self, counts| {
                slf.add_issue(
                    slice_type.as_node_ref(),
                    IssueKind::TypeAliasArgumentIssue { counts },
                );
            },
        );
        generics
    }

    #[inline]
    fn check_constraints(
        &mut self,
        type_var: &TypeVar,
        node_ref: NodeRef,
        as_type: impl Fn(&mut Self) -> Type,
        get_of: impl FnOnce() -> Box<str>,
    ) {
        let i_s = self.i_s;
        match type_var.kind(i_s.db) {
            TypeVarKind::Unrestricted => (),
            TypeVarKind::Bound(bound) => {
                let actual = as_type(self);
                if !bound.is_simple_super_type_of(i_s, &actual).bool() {
                    node_ref.add_issue(
                        i_s,
                        IssueKind::TypeVarBoundViolation {
                            actual: actual.format_short(i_s.db),
                            of: get_of(),
                            expected: bound.format_short(i_s.db),
                        },
                    );
                }
            }
            TypeVarKind::Constraints(mut constraints) => {
                let t2 = as_type(self);
                if let Type::TypeVar(usage) = &t2 {
                    if let TypeVarKind::Constraints(mut constraints2) = usage.type_var.kind(i_s.db)
                    {
                        if constraints2.all(|t2| {
                            constraints
                                .clone()
                                .any(|t| t.is_simple_super_type_of(i_s, t2).bool())
                        }) {
                            // The provided type_var2 is a subset of the type_var constraints.
                            return;
                        }
                    }
                }
                if !constraints.any(|t| t.is_simple_super_type_of(i_s, &t2).bool()) {
                    node_ref.add_issue(
                        i_s,
                        IssueKind::InvalidTypeVarValue {
                            type_var_name: Box::from(type_var.name(i_s.db)),
                            of: format!("\"{}\"", get_of()).into(),
                            actual: t2.format_short(i_s.db),
                        },
                    );
                }
            }
        }
    }

    fn compute_type_get_item_on_dataclass(
        &mut self,
        dataclass: &Dataclass,
        slice_type: SliceType,
        primary: Option<Primary>,
    ) -> TypeContent<'db, 'db> {
        let db = self.i_s.db;
        let c = match self.compute_type_get_item_on_class_inner(
            Class::with_undefined_generics(ClassNodeRef::from_link(db, dataclass.class.link)),
            slice_type,
            primary,
        ) {
            ClassGetItemResult::GenericClass(c) => c,
            ClassGetItemResult::SimpleGeneric { generics, .. } => GenericClass {
                link: dataclass.class.link,
                generics,
            },
            ClassGetItemResult::Invalid => {
                return TypeContent::InvalidVariable(InvalidVariableType::Other)
            }
        };
        TypeContent::Type(Type::Dataclass(Dataclass::new(
            c,
            dataclass.options.clone(),
        )))
    }

    fn compute_type_get_item_on_class(
        &mut self,
        class: Class,
        slice_type: SliceType,
        primary: Option<Primary>,
    ) -> TypeContent<'db, 'db> {
        match self.compute_type_get_item_on_class_inner(class, slice_type, primary) {
            ClassGetItemResult::GenericClass(c) => TypeContent::Type(Type::Class(c)),
            ClassGetItemResult::SimpleGeneric {
                node_ref,
                class_link,
                generics,
            } => TypeContent::SimpleGeneric {
                node_ref,
                class_link,
                generics,
            },
            ClassGetItemResult::Invalid => TypeContent::InvalidVariable(InvalidVariableType::Other),
        }
    }

    fn compute_type_get_item_on_class_inner(
        &mut self,
        class: Class,
        slice_type: SliceType,
        primary: Option<Primary>,
    ) -> ClassGetItemResult<'db> {
        if !matches!(
            class.generics(),
            Generics::None | Generics::NotDefinedYet { .. }
        ) {
            return ClassGetItemResult::Invalid;
        }
        let type_var_likes = class.type_vars(self.i_s);

        let mut iterator = slice_type.iter();
        let mut generics = vec![];

        if !type_var_likes.is_empty()
            && type_var_likes
                .iter()
                .all(|t| matches!(t, TypeVarLike::TypeVar(_)))
        {
            // First check if we can make a SimpleGeneric. This happens if all generics are
            // SimpleGeneric or classes.
            if let Some((node_ref, generics)) = self.maybe_generic_class_without_type_var(
                class,
                slice_type,
                &mut generics,
                &mut iterator,
                type_var_likes,
                primary,
            ) {
                return ClassGetItemResult::SimpleGeneric {
                    node_ref,
                    class_link: class.node_ref.as_link(),
                    generics,
                };
            }
            if generics.is_empty() {
                // If some generics are given we just continue the iterator, otherwise we start
                // fresh. This is a bit weird but helps us avoid recalculating db types that have
                // already been calculated.
                iterator = slice_type.iter();
            }
        };
        self.compute_get_item_generics_on_class(
            slice_type,
            iterator,
            class.name(),
            type_var_likes,
            &mut generics,
        );
        ClassGetItemResult::GenericClass(GenericClass {
            link: class.node_ref.as_link(),
            generics: match type_var_likes.is_empty() {
                true => ClassGenerics::None,
                false => ClassGenerics::List(GenericsList::generics_from_vec(generics)),
            },
        })
    }

    fn compute_get_item_generics_on_class(
        &mut self,
        slice_type: SliceType,
        iterator: SliceTypeIterator,
        class_name: &str,
        type_var_likes: &TypeVarLikes,
        generics: &mut Vec<GenericItem>,
    ) {
        self.calculate_type_arguments(
            slice_type,
            generics,
            iterator,
            type_var_likes,
            &|| Box::from(class_name),
            |slf: &mut Self, counts| {
                slf.add_issue(
                    slice_type.as_node_ref(),
                    IssueKind::TypeArgumentIssue {
                        class: Box::from(class_name),
                        counts,
                    },
                );
            },
        );
    }

    #[inline]
    fn maybe_generic_class_without_type_var(
        &mut self,
        class: Class,
        slice_type: SliceType,
        generics: &mut Vec<GenericItem>,
        iterator: &mut SliceTypeIterator,
        tvs: &TypeVarLikes,
        primary: Option<Primary>,
    ) -> Option<(NodeRef<'db>, ClassGenerics)> {
        let primary = primary?;
        if self.origin != TypeComputationOrigin::ParamTypeCommentOrAnnotation {
            return None;
        }
        for (i, type_var_like) in tvs.iter().enumerate() {
            let TypeVarLike::TypeVar(type_var) = type_var_like else {
                unreachable!("Should have been checked before")
            };
            if let Some(slice_content) = iterator.next() {
                let t = self.compute_slice_type_content(slice_content);
                // Performance: This could be optimized to not create new objects all the time.
                self.check_constraints(
                    type_var,
                    slice_content.as_node_ref(),
                    |slf| slf.as_type(t.clone(), slice_content.as_node_ref()),
                    || Box::from(class.name()),
                );
                if !matches!(
                    t,
                    TypeContent::SimpleGeneric { .. }
                        | TypeContent::Class {
                            has_type_vars: false,
                            ..
                        }
                ) {
                    // Backfill the generics
                    for slice_content in slice_type.iter().take(i) {
                        generics.push(GenericItem::TypeArg(self.compute_slice_type(slice_content)));
                    }
                    generics.push(GenericItem::TypeArg(
                        self.as_type(t, slice_content.as_node_ref()),
                    ));
                    return None;
                }
            } else {
                return None;
            }
        }
        if iterator.next().is_none() {
            // We have no unfinished iterator and can therefore safely return.
            let node_ref = NodeRef::new(self.file, primary.index()).to_db_lifetime(self.i_s.db);
            let redirect_node_ref = NodeRef::new(self.file, primary.first_child_index());
            debug_assert!(
                !redirect_node_ref.point().calculated(),
                "For now nothing sets this, but this could change"
            );
            redirect_node_ref.set_point(class.node_ref.as_redirection_point(Locality::Todo));
            node_ref.set_point(Point::new_specific(Specific::SimpleGeneric, Locality::Todo));
            Some((
                node_ref,
                match slice_type.cst_node {
                    CSTSliceType::NamedExpression(n) => ClassGenerics::ExpressionWithClassType(
                        PointLink::new(node_ref.file_index(), n.expression().index()),
                    ),
                    CSTSliceType::Slices(slices) => ClassGenerics::SlicesWithClassTypes(
                        PointLink::new(node_ref.file_index(), slices.index()),
                    ),
                    CSTSliceType::StarredExpression(_) => return None,
                    CSTSliceType::Slice(_) => unreachable!(),
                },
            ))
        } else {
            None
        }
    }

    #[inline]
    fn calculate_type_arguments(
        &mut self,
        slice_type: SliceType,
        generics: &mut Vec<GenericItem>,
        iterator: SliceTypeIterator,
        type_var_likes: &TypeVarLikes,
        get_of: &impl Fn() -> Box<str>,
        on_count_mismatch: impl FnOnce(&mut Self, GenericCounts),
    ) {
        let mut given = generics.len();
        let expected = type_var_likes.len();
        let has_type_var_tuple = type_var_likes
            .iter()
            .any(|tvl| matches!(tvl, TypeVarLike::TypeVarTuple(_)));

        let mut type_args = TypeArgIterator::new(iterator);
        let mut type_var_iterator = type_var_likes.iter().enumerate().skip(generics.len());
        let mut is_single_param_spec = false;
        'outer: for (i, type_var_like) in type_var_iterator.by_ref() {
            let generic_item = match type_var_like {
                TypeVarLike::TypeVar(type_var) => {
                    if let Some((node_ref, t)) =
                        type_args.next_type_argument(self, has_type_var_tuple)
                    {
                        given += 1;
                        self.check_constraints(type_var, node_ref, |_| t.clone(), get_of);
                        GenericItem::TypeArg(t)
                    } else if let Some(default) = type_var.default(self.i_s.db) {
                        GenericItem::TypeArg(default.clone())
                    } else {
                        break;
                    }
                }
                TypeVarLike::TypeVarTuple(tvt) => {
                    for (i, type_var_like) in type_var_iterator.by_ref().rev() {
                        let generic_item = match type_var_like {
                            TypeVarLike::TypeVar(type_var) => {
                                if let Some((from, t)) = type_args.next_type_argument_back(self) {
                                    given += 1;
                                    self.check_constraints(type_var, from, |_| t.clone(), get_of);
                                    GenericItem::TypeArg(t)
                                } else if let Some(default) = type_var.default(self.i_s.db) {
                                    GenericItem::TypeArg(default.clone())
                                } else {
                                    break 'outer;
                                }
                            }
                            TypeVarLike::ParamSpec(param_spec) => {
                                if let Some(spec) = type_args.next_param_spec_back(self) {
                                    given += 1;
                                    GenericItem::ParamSpecArg(spec)
                                } else if let Some(default) = &param_spec.default {
                                    GenericItem::ParamSpecArg(ParamSpecArg::new(
                                        default.clone(),
                                        None,
                                    ))
                                } else {
                                    break 'outer;
                                }
                            }
                            TypeVarLike::TypeVarTuple(_) => unreachable!(),
                        };

                        generics.insert(i - 1, generic_item);
                    }
                    given += 1;
                    let args = type_args.as_type_arguments(
                        self,
                        type_var_likes.len() == 1 && slice_type.iter().count() == 1,
                    );
                    generics.insert(
                        i,
                        GenericItem::TypeArgs(
                            if let Some(default) =
                                tvt.default.as_ref().filter(|_| args.empty_not_explicit)
                            {
                                default.clone()
                            } else {
                                TypeArgs { args: args.args }
                            },
                        ),
                    );
                    break;
                }
                TypeVarLike::ParamSpec(param_spec) => {
                    given += 1;
                    if expected == 1 && slice_type.iter().count() != 1 {
                        // PEP 612 allows us to write C[int, str] instead of C[[int, str]],
                        // because "for aesthetic purposes we allow these to be omitted".
                        let params =
                            self.calculate_simplified_param_spec_generics(&mut slice_type.iter());
                        is_single_param_spec = true;
                        GenericItem::ParamSpecArg(ParamSpecArg::new(params, None))
                    } else if let Some(spec) = type_args.next_param_spec(self, expected == 1) {
                        GenericItem::ParamSpecArg(spec)
                    } else if let Some(default) = &param_spec.default {
                        GenericItem::ParamSpecArg(ParamSpecArg::new(default.clone(), None))
                    } else {
                        break;
                    }
                }
            };
            generics.push(generic_item);
        }
        if !is_single_param_spec {
            while type_args
                .next_type_argument(self, has_type_var_tuple)
                .is_some()
            {
                // Still calculate errors for the rest of the types given. After all they are still
                // expected to be types.
                given += 1;
            }
        }
        let default_count = type_var_likes
            .iter()
            .filter(|tvl| tvl.has_default() && !matches!(tvl, TypeVarLike::TypeVarTuple(_)))
            .count();
        let mut expected_minimum = None;
        let mismatch = if has_type_var_tuple {
            given < expected - default_count
        } else if default_count > 0 {
            expected_minimum = Some(expected - has_type_var_tuple as usize - default_count);
            !((expected - default_count) <= given && given <= expected)
        } else {
            given != expected
        };
        if mismatch {
            on_count_mismatch(
                self,
                GenericCounts {
                    given,
                    expected: expected - has_type_var_tuple as usize,
                    expected_minimum,
                    at_least_expected: has_type_var_tuple,
                },
            );
            generics.clear();
            for missing_type_var in type_var_likes.iter() {
                generics.push(missing_type_var.as_any_generic_item(self.i_s.db))
            }
        }
    }

    fn compute_type_get_item_on_tuple(&mut self, slice_type: SliceType) -> TypeContent<'db, 'db> {
        let mut iterator = slice_type.iter();
        let first = iterator.next().unwrap();
        if let Some(SliceOrSimple::Simple(s)) = iterator.next() {
            if s.named_expr.is_ellipsis_literal() {
                let t = self.compute_slice_type(first);
                return TypeContent::Type(Type::Tuple(Tuple::new_arbitrary_length(t)));
            }
        }
        TypeContent::Type(Type::Tuple(Tuple::new(
            TypeArgIterator::new(slice_type.iter())
                .as_type_arguments(self, slice_type.iter().count() == 1)
                .args,
        )))
    }

    fn calculate_simplified_param_spec_generics<'y, I: Iterator<Item = SliceOrSimple<'y>>>(
        &mut self,
        iterator: &mut I,
    ) -> CallableParams {
        let mut params = vec![];
        let mut had_issue = false;
        for s in iterator.by_ref() {
            let t = self.compute_slice_type_content(s);
            match t {
                TypeContent::InvalidVariable(InvalidVariableType::List) => {
                    self.add_issue(
                        s.as_node_ref(),
                        IssueKind::ParamSpecNestedSpecificationsNotAllowed,
                    );
                    had_issue = true;
                }
                _ => self.add_param(&mut params, t, s.as_node_ref().node_index),
            }
        }
        if had_issue {
            CallableParams::Any(AnyCause::FromError)
        } else {
            CallableParams::new_simple(Rc::from(params))
        }
    }

    fn check_param(&mut self, t: TypeContent, from: NodeRef) -> CallableParam {
        let param_type = match t {
            TypeContent::CallableParam(p) => return p,
            TypeContent::Unpacked(TypeOrUnpack::Type(Type::TypedDict(td))) => {
                ParamType::StarStar(StarStarParamType::UnpackTypedDict(td))
            }
            TypeContent::Unpacked(TypeOrUnpack::TypeVarTuple(tvt)) => ParamType::Star(
                StarParamType::UnpackedTuple(Tuple::new(TupleArgs::WithUnpack(WithUnpack {
                    before: Rc::from([]),
                    unpack: TupleUnpack::TypeVarTuple(tvt),
                    after: Rc::from([]),
                }))),
            ),
            TypeContent::Unpacked(TypeOrUnpack::Type(t)) => {
                let any_cause = match t {
                    Type::Any(cause) => cause,
                    _ => {
                        self.add_issue(
                            from,
                            IssueKind::VariadicUnpackMustBeTupleLike {
                                actual: t.format_short(self.i_s.db),
                            },
                        );
                        AnyCause::FromError
                    }
                };
                ParamType::Star(StarParamType::ArbitraryLen(Type::Any(any_cause)))
            }
            TypeContent::SpecialType(SpecialType::Unpack) => {
                ParamType::Star(StarParamType::ArbitraryLen(
                    // Creates an Any.
                    self.as_type(t, from),
                ))
            }
            _ => ParamType::PositionalOnly(self.as_type(t, from)),
        };
        CallableParam::new_anonymous(param_type)
    }

    fn add_param(&mut self, params: &mut Vec<CallableParam>, t: TypeContent, index: NodeIndex) {
        let p = match t {
            TypeContent::Unpacked(TypeOrUnpack::Type(Type::Tuple(tup))) => match &tup.args {
                TupleArgs::WithUnpack(_) => {
                    CallableParam::new_anonymous(ParamType::Star(StarParamType::UnpackedTuple(tup)))
                }
                TupleArgs::ArbitraryLen(_) => {
                    let TupleArgs::ArbitraryLen(t) = Rc::unwrap_or_clone(tup).args else {
                        unreachable!();
                    };
                    CallableParam::new_anonymous(ParamType::Star(StarParamType::ArbitraryLen(*t)))
                }
                TupleArgs::FixedLen(ts) => {
                    // TODO these should also be checked.
                    for t in ts.iter() {
                        params.push(CallableParam::new_anonymous(ParamType::PositionalOnly(
                            t.clone(),
                        )));
                    }
                    return;
                }
            },
            _ => self.check_param(t, NodeRef::new(self.file, index)),
        };
        if let Some(previous) = params.last() {
            let prev_kind = previous.type_.param_kind();
            let current_kind = p.type_.param_kind();
            let msg = match current_kind {
                ParamKind::PositionalOnly
                    if current_kind < prev_kind || previous.has_default && !p.has_default =>
                {
                    if let ParamType::Star(
                        StarParamType::UnpackedTuple(_) | StarParamType::ArbitraryLen(_),
                    ) = &previous.type_
                    {
                        let previous = params.pop().unwrap();
                        let tup_args = match previous.type_ {
                            ParamType::Star(StarParamType::UnpackedTuple(tup)) => {
                                Rc::unwrap_or_clone(tup).args
                            }
                            ParamType::Star(StarParamType::ArbitraryLen(t)) => {
                                TupleArgs::ArbitraryLen(Box::new(t))
                            }
                            _ => unreachable!(),
                        };
                        let ParamType::PositionalOnly(new) = p.type_ else {
                            unreachable!();
                        };
                        let with_unpack = match tup_args {
                            TupleArgs::WithUnpack(mut with_unpack) => {
                                let mut after = rc_slice_into_vec(with_unpack.after);
                                after.push(new);
                                with_unpack.after = after.into();
                                with_unpack
                            }
                            TupleArgs::ArbitraryLen(t) => WithUnpack {
                                before: Rc::from([]),
                                unpack: TupleUnpack::ArbitraryLen(*t),
                                after: Rc::from([new]),
                            },
                            TupleArgs::FixedLen(_) => unreachable!(),
                        };
                        let tup = Tuple::new(TupleArgs::WithUnpack(with_unpack));
                        params.push(CallableParam {
                            type_: ParamType::Star(StarParamType::UnpackedTuple(tup)),
                            name: previous.name,
                            has_default: previous.has_default,
                            might_have_type_vars: true,
                        });
                        return;
                    }
                    Some("Required positional args may not appear after default, named or var args")
                }
                ParamKind::PositionalOrKeyword => {
                    if previous.has_default && !p.has_default {
                        Some("Required positional args may not appear after default, named or var args")
                    } else if current_kind < prev_kind {
                        if p.has_default {
                            Some("Positional default args may not appear after named or var args")
                        } else {
                            Some("Required positional args may not appear after default, named or var args")
                        }
                    } else {
                        None
                    }
                }
                ParamKind::Star if current_kind <= prev_kind => {
                    if matches!(
                        previous.type_,
                        ParamType::Star(StarParamType::UnpackedTuple(_))
                    ) {
                        self.add_issue_for_index(
                            index,
                            IssueKind::MoreThanOneUnpackTypeIsNotAllowed,
                        );
                        return;
                    }
                    Some("Var args may not appear after named or var args")
                }
                ParamKind::KeywordOnly if current_kind <= prev_kind => {
                    Some("A **kwargs argument must be the last argument")
                }
                ParamKind::StarStar if current_kind == prev_kind => {
                    Some("You may only have one **kwargs argument")
                }
                _ => None,
            };
            if let Some(msg) = msg {
                self.add_issue_for_index(index, IssueKind::InvalidType(Box::from(msg)));
                return;
            }

            if let Some(param_name) = p.name.as_ref() {
                let param_name = param_name.as_str(self.i_s.db);
                for other in params.iter() {
                    if let Some(other_name) = other.name.as_ref() {
                        let other_name = other_name.as_str(self.i_s.db);
                        if param_name == other_name {
                            self.add_issue_for_index(
                                index,
                                IssueKind::InvalidType(
                                    format!("Duplicate argument \"{param_name}\" in Callable",)
                                        .into(),
                                ),
                            );
                            return;
                        }
                    }
                }
            }
        }
        params.push(p);
    }

    fn calculate_callable_params(
        &mut self,
        first: SliceOrSimple,
        from_class_generics: bool,
        allow_aesthetic_class_simplification: bool,
    ) -> CallableParams {
        let SliceOrSimple::Simple(n) = first else {
            self.add_issue(
                first.as_node_ref(),
                IssueKind::InvalidType("Invalid callable params".into()),
            );
            return CallableParams::Any(AnyCause::FromError);
        };
        self.calculate_callable_params_for_expr(
            n.named_expr.expression(),
            from_class_generics,
            allow_aesthetic_class_simplification,
        )
        .unwrap_or_else(|| {
            if from_class_generics {
                self.add_issue(
                    n.as_node_ref(),
                    IssueKind::InvalidParamSpecGenerics {
                        got: Box::from(n.named_expr.as_code()),
                    },
                );
            } else {
                self.add_issue(n.as_node_ref(), IssueKind::InvalidCallableParams);
            }
            CallableParams::Any(AnyCause::FromError)
        })
    }

    fn calculate_callable_params_for_expr(
        &mut self,
        expr: Expression,
        from_class_generics: bool,
        allow_aesthetic_class_simplification: bool,
    ) -> Option<CallableParams> {
        Some(match expr.maybe_unpacked_atom() {
            Some(AtomContent::List(list)) => {
                let mut params = vec![];
                for i in list.unpack() {
                    match i {
                        StarLikeExpression::NamedExpression(n) => {
                            let t = self.compute_type(n.expression());
                            self.add_param(&mut params, t, n.index())
                        }
                        StarLikeExpression::StarNamedExpression(star_expr) => {
                            let t = self.compute_type_expression_part(star_expr.expression_part());
                            let new_t = match t {
                                TypeContent::TypeVarTuple(tvt) => TypeOrUnpack::TypeVarTuple(tvt),
                                _ => {
                                    let node_ref = NodeRef::new(self.file, star_expr.index());
                                    let mut t = self.as_type(t, node_ref);
                                    if !matches!(t, Type::Tuple(_)) {
                                        if !t.is_any() {
                                            self.add_issue(
                                                node_ref,
                                                IssueKind::VariadicUnpackMustBeTupleLike {
                                                    actual: t.format_short(self.i_s.db),
                                                },
                                            );
                                        }
                                        t = Type::Tuple(Tuple::new_arbitrary_length_with_any());
                                    }
                                    TypeOrUnpack::Type(t)
                                }
                            };
                            self.add_param(
                                &mut params,
                                TypeContent::Unpacked(new_t),
                                star_expr.index(),
                            )
                        }
                        _ => unreachable!(),
                    }
                }
                CallableParams::new_simple(Rc::from(params))
            }
            Some(AtomContent::Ellipsis) => CallableParams::Any(AnyCause::Explicit),
            _ => match self.compute_type(expr) {
                TypeContent::ParamSpec(p) => CallableParams::new_param_spec(p),
                TypeContent::SpecialCase(Specific::TypingAny) if from_class_generics => {
                    CallableParams::Any(AnyCause::Explicit)
                }
                TypeContent::Unknown(cause) => CallableParams::Any(cause.into()),
                TypeContent::Concatenate(p) => p,
                t if allow_aesthetic_class_simplification => CallableParams::new_simple(Rc::new([
                    self.check_param(t, NodeRef::new(self.file, expr.index())),
                ])),
                _ => return None,
            },
        })
    }

    fn compute_type_get_item_on_callable(
        &mut self,
        slice_type: SliceType,
    ) -> TypeContent<'db, 'db> {
        let defined_at = slice_type.as_node_ref().as_link();
        self.type_var_manager.register_callable(CallableWithParent {
            defined_at,
            parent_callable: self.current_callable,
        });
        let old = std::mem::replace(&mut self.current_callable, Some(defined_at));

        let db = self.i_s.db;
        let content = if slice_type.iter().count() == 2 {
            let mut iterator = slice_type.iter();
            let params = self.calculate_callable_params(iterator.next().unwrap(), false, false);
            let mut guard = None;
            let return_type = if let Some(s) = iterator.next() {
                match self.compute_slice_type_content(s) {
                    TypeContent::TypeGuardInfo(g) => {
                        guard = Some(g);
                        db.python_state.bool_type()
                    }
                    type_content => self.as_type(type_content, s.as_node_ref()),
                }
            } else {
                Type::Any(AnyCause::Todo)
            };
            Rc::new(CallableContent {
                name: None,
                class_name: None,
                defined_at,
                kind: FunctionKind::Function {
                    had_first_self_or_class_annotation: true,
                },
                type_vars: self.i_s.db.python_state.empty_type_var_likes.clone(),
                guard,
                is_abstract: false,
                is_final: false,
                no_type_check: false,
                params,
                return_type,
            })
        } else {
            self.add_issue(slice_type.as_node_ref(), IssueKind::InvalidCallableArgCount);
            self.i_s.db.python_state.any_callable_from_error.clone()
        };
        self.current_callable = old;
        TypeContent::Type(Type::Callable(content))
    }

    fn compute_type_get_item_on_union(
        &mut self,
        slice_type: SliceType,
    ) -> TypeContent<'static, 'static> {
        let mut entries = vec![];
        let mut format_index = 0;
        for slice_or_simple in slice_type.iter() {
            let t = self.compute_slice_type_content(slice_or_simple);
            let type_ = self.as_type(t, slice_or_simple.as_node_ref());
            match type_ {
                Type::Never(_) => continue,
                Type::Union(u) => {
                    let length = u.entries.len();
                    for mut new_entry in u.entries.into_vec() {
                        new_entry.format_index += format_index;
                        entries.push(new_entry);
                    }
                    format_index += length;
                }
                _ => {
                    entries.push(UnionEntry {
                        type_,
                        format_index,
                    });
                    format_index += 1;
                }
            }
        }
        TypeContent::Type(match entries.len() {
            0 => Type::Never(NeverCause::Explicit),
            1 => entries.into_iter().next().unwrap().type_,
            _ => {
                let mut t = UnionType::new(entries);
                t.sort_for_priority();
                Type::Union(t)
            }
        })
    }

    fn compute_type_get_item_on_optional(
        &mut self,
        slice_type: SliceType,
    ) -> TypeContent<'db, 'db> {
        let mut iterator = slice_type.iter();
        let first = iterator.next().unwrap();
        if let Some(next) = iterator.next() {
            self.add_issue(
                next.as_node_ref(),
                IssueKind::MustHaveOneArgument {
                    name: "Optional[...]",
                },
            );
        }
        let t = self.compute_slice_type(first);
        let mut t = t.union(Type::None);
        if let Type::Union(union_type) = &mut t {
            union_type.sort_for_priority();
        };
        TypeContent::Type(t)
    }

    fn compute_type_get_item_on_type(&mut self, slice_type: SliceType) -> TypeContent<'db, 'db> {
        let mut iterator = slice_type.iter();
        let content = iterator.next().unwrap();
        if iterator.count() > 0 {
            return TypeContent::InvalidVariable(InvalidVariableType::Other);
        }
        let t = match self.compute_slice_type_content(content) {
            TypeContent::SpecialType(SpecialType::BuiltinsType | SpecialType::TypingType) => {
                self.i_s.db.python_state.bare_type_type()
            }
            t => self.as_type(t, content.as_node_ref()),
        };
        let ret = |t| TypeContent::Type(Type::Type(Rc::new(t)));
        for inner in t.iter_with_unpacked_unions_without_unpacking_recursive_types() {
            let name = match inner {
                Type::Type(_) => "Type",
                Type::Literal(_) => "Literal",
                _ => continue,
            };
            self.add_issue(
                slice_type.as_node_ref(),
                IssueKind::CannotContainType { name },
            );
            return ret(Type::ERROR);
        }
        ret(t)
    }

    fn compute_type_get_item_on_alias(
        &mut self,
        alias: &TypeAlias,
        slice_type: SliceType,
    ) -> TypeContent<'db, 'db> {
        let generics = self.compute_generics_for_alias(slice_type, alias);
        self.is_recursive_alias |= alias.is_recursive();
        TypeContent::Type(
            alias
                .replace_type_var_likes(self.i_s.db, false, &mut |usage| {
                    if let Some(generic) = generics.get(usage.index().as_usize()) {
                        generic.clone()
                    } else {
                        // Can happen when a generic is not available, because it's defined in e.g.
                        // X = dict[T1, T2], where T2 has a default, but T1 has not.
                        usage.as_any_generic_item(self.i_s.db)
                    }
                })
                .into_owned(),
        )
    }

    fn compute_type_get_item_on_final(&mut self, slice_type: SliceType) -> TypeContent<'db, 'db> {
        let mut iterator = slice_type.iter();
        let first = iterator.next().unwrap();
        if iterator.count() != 0 {
            self.add_issue(slice_type.as_node_ref(), IssueKind::FinalTooManyArguments);
        }
        match self.compute_slice_type_content(first) {
            TypeContent::ClassVar(_) => {
                slice_type
                    .as_node_ref()
                    .add_issue(self.i_s, IssueKind::FinalAndClassVarUsedBoth);
                TypeContent::UNKNOWN_REPORTED
            }
            t => TypeContent::Final(self.as_type(t, slice_type.as_node_ref())),
        }
    }

    fn wrap_in_unpack(&mut self, tc: TypeContent, from: NodeRef) -> TypeOrUnpack {
        match tc {
            TypeContent::TypeVarTuple(t) => TypeOrUnpack::TypeVarTuple(t),
            TypeContent::Unknown(cause) => TypeOrUnpack::Unknown(cause),
            t => TypeOrUnpack::Type(self.as_type(t, from)),
        }
    }

    fn compute_type_get_item_on_unpack(&mut self, slice_type: SliceType) -> TypeContent<'db, 'db> {
        let mut iterator = slice_type.iter();
        let first = iterator.next().unwrap();
        if iterator.count() == 0 {
            let tc = self.compute_slice_type_content(first);
            TypeContent::Unpacked(self.wrap_in_unpack(tc, first.as_node_ref()))
        } else {
            self.add_issue(
                slice_type.as_node_ref(),
                IssueKind::UnpackRequiresExactlyOneArgument,
            );
            TypeContent::UNKNOWN_REPORTED
        }
    }

    fn compute_type_get_item_on_concatenate(
        &mut self,
        slice_type: SliceType,
    ) -> TypeContent<'db, 'db> {
        let count = slice_type.iter().count();
        let mut iterator = slice_type.iter();
        let mut params: Vec<_> = iterator
            .by_ref()
            .take(count - 1)
            .map(|s| {
                CallableParam::new_anonymous(ParamType::PositionalOnly(self.compute_slice_type(s)))
            })
            .collect();
        match self.compute_slice_type_content(iterator.next().unwrap()) {
            TypeContent::ParamSpec(p) => {
                add_param_spec_to_params(&mut params, p);
                TypeContent::Concatenate(CallableParams::Simple(params.into()))
            }
            TypeContent::Concatenate(_) => {
                self.add_issue(slice_type.as_node_ref(), IssueKind::NestedConcatenate);
                TypeContent::UNKNOWN_REPORTED
            }
            TypeContent::Unknown(cause) => TypeContent::Unknown(cause),
            TypeContent::InvalidVariable(InvalidVariableType::Ellipsis) => {
                params.push(CallableParam::new_anonymous(ParamType::Star(
                    StarParamType::ArbitraryLen(Type::Any(AnyCause::Explicit)),
                )));
                params.push(CallableParam::new_anonymous(ParamType::StarStar(
                    StarStarParamType::ValueType(Type::Any(AnyCause::Explicit)),
                )));
                TypeContent::Concatenate(CallableParams::new_simple(params.into()))
            }
            _ => {
                self.add_issue(
                    slice_type.as_node_ref(),
                    IssueKind::ConcatenateLastParamNeedsToBeParamSpec,
                );
                TypeContent::UNKNOWN_REPORTED
            }
        }
    }

    fn compute_get_item_on_literal(&mut self, slice_type: SliceType) -> TypeContent<'db, 'db> {
        let mut iterator = slice_type.iter();
        let first = iterator.next().unwrap();
        if iterator.next().is_some() {
            TypeContent::Type(Type::Union(UnionType::new(
                slice_type
                    .iter()
                    .enumerate()
                    .map(|(i, s)| UnionEntry {
                        type_: {
                            let t = self.compute_get_item_on_literal_item(s, i + 1);
                            self.as_type(t, s.as_node_ref())
                        },
                        format_index: i,
                    })
                    .collect(),
            )))
        } else {
            self.compute_get_item_on_literal_item(first, 1)
        }
    }

    fn compute_get_item_on_literal_item(
        &mut self,
        slice: SliceOrSimple,
        index: usize,
    ) -> TypeContent<'db, 'db> {
        if let SliceOrSimple::Simple(s) = slice {
            let expr_not_allowed = |slf: &Self| {
                slf.add_issue(
                    slice.as_node_ref(),
                    IssueKind::InvalidType(
                        "Invalid type: Literal[...] cannot contain arbitrary expressions".into(),
                    ),
                );
                TypeContent::UNKNOWN_REPORTED
            };
            match s.named_expr.expression().unpack() {
                ExpressionContent::ExpressionPart(ExpressionPart::Atom(atom)) => {
                    let maybe = match atom.unpack() {
                        AtomContent::Int(i) => Some(LiteralKind::Int(
                            i.parse().unwrap_or_else(|| unimplemented!()),
                        )),
                        AtomContent::Bytes(b) => Some(LiteralKind::Bytes(
                            if let Some(b) = b.maybe_single_bytes_literal() {
                                DbBytes::Link(PointLink::new(self.file.file_index, b.index()))
                            } else {
                                self.add_issue(
                                    NodeRef::new(self.file, b.index()),
                                    IssueKind::InvalidType(
                                        "Literals with chained bytes are not supported".into(),
                                    ),
                                );
                                return TypeContent::UNKNOWN_REPORTED;
                            },
                        )),
                        AtomContent::Strings(s) => s.maybe_single_string_literal().map(|s| {
                            LiteralKind::String(
                                DbString::from_python_string(
                                    self.file.file_index,
                                    s.as_python_string(),
                                )
                                .unwrap(),
                            )
                        }),
                        AtomContent::Bool(keyword) => {
                            Some(LiteralKind::Bool(keyword.as_code() == "True"))
                        }
                        AtomContent::Float(_) => {
                            self.add_issue(
                                slice.as_node_ref(),
                                IssueKind::InvalidType(
                                    format!(
                                        "Parameter {} of Literal[...] cannot be of type \"float\"",
                                        index
                                    )
                                    .into(),
                                ),
                            );
                            return TypeContent::UNKNOWN_REPORTED;
                        }
                        AtomContent::Complex(_) => {
                            self.add_issue(
                                slice.as_node_ref(),
                                IssueKind::InvalidType(
                                    format!(
                                        "Parameter {} of Literal[...] cannot be of type \"complex\"",
                                        index
                                    )
                                    .into(),
                                ),
                            );
                            return TypeContent::UNKNOWN_REPORTED;
                        }
                        AtomContent::Name(_) | AtomContent::NoneLiteral => None,
                        _ => return expr_not_allowed(self),
                    };
                    if let Some(kind) = maybe {
                        return TypeContent::Type(Type::Literal(Literal {
                            kind,
                            implicit: false,
                        }));
                    }
                }
                ExpressionContent::ExpressionPart(ExpressionPart::Factor(f)) => {
                    let (sign, e) = f.unpack();
                    let s = sign.as_code();
                    if matches!(s, "-" | "+") {
                        if let ExpressionPart::Atom(atom) = e {
                            if let AtomContent::Int(i) = atom.unpack() {
                                if let Some(mut i) = i.parse() {
                                    if s == "-" {
                                        i = -i;
                                    }
                                    return TypeContent::Type(Type::Literal(Literal {
                                        kind: LiteralKind::Int(i),
                                        implicit: false,
                                    }));
                                } else {
                                    unimplemented!()
                                }
                            }
                        }
                    }
                    return expr_not_allowed(self);
                }
                ExpressionContent::ExpressionPart(ExpressionPart::Primary(p)) => {
                    if let PrimaryContent::Execution(_) = p.second() {
                        return expr_not_allowed(self);
                    }
                }
                _ => return expr_not_allowed(self),
            }
        }
        match self.compute_slice_type_content(slice) {
            TypeContent::SpecialCase(Specific::TypingAny) => {
                self.add_issue(
                    slice.as_node_ref(),
                    IssueKind::InvalidType(
                        format!("Parameter {index} of Literal[...] cannot be of type \"Any\"")
                            .into(),
                    ),
                );
                TypeContent::UNKNOWN_REPORTED
            }
            TypeContent::InvalidVariable(_) => {
                self.add_issue(
                    slice.as_node_ref(),
                    IssueKind::InvalidType(
                        format!("Parameter {index} of Literal[...] is invalid").into(),
                    ),
                );
                TypeContent::UNKNOWN_REPORTED
            }
            TypeContent::EnumMember(e) => TypeContent::Type(Type::EnumMember(e)),
            t => match self.as_type(t, slice.as_node_ref()) {
                Type::Any(cause) => TypeContent::Unknown(UnknownCause::AnyCause(cause)),
                t @ (Type::None | Type::Literal(_)) => TypeContent::Type(t),
                Type::Union(u)
                    if u.iter().all(|t| {
                        matches!(t, Type::Literal(_) | Type::None | Type::EnumMember(_))
                    }) =>
                {
                    TypeContent::Type(Type::Union(u))
                }
                _ => {
                    self.add_issue(
                        slice.as_node_ref(),
                        IssueKind::InvalidType(
                            format!("Parameter {} of Literal[...] is invalid", index).into(),
                        ),
                    );
                    TypeContent::UNKNOWN_REPORTED
                }
            },
        }
    }

    fn compute_get_item_on_annotated(&mut self, slice_type: SliceType) -> TypeContent<'db, 'db> {
        let slice_type = slice_type.to_db_lifetime(self.i_s.db);
        let mut iterator = slice_type.iter();
        let first = iterator.next().unwrap();
        if iterator.next().is_none() {
            self.add_issue(
                slice_type.as_node_ref(),
                IssueKind::InvalidType(Box::from(
                    "Annotated[...] must have exactly one type argument and at least one annotation",
                )),
            );
            TypeContent::UNKNOWN_REPORTED
        } else {
            // Annotated[..., ...] can simply be ignored and the first part can be used.
            self.compute_slice_type_content(first)
        }
    }

    fn compute_get_item_on_class_var(&mut self, slice_type: SliceType) -> TypeContent<'db, 'db> {
        let mut iterator = slice_type.iter();
        let first = iterator.next().unwrap();
        if iterator.next().is_some() {
            self.add_issue(
                slice_type.as_node_ref(),
                IssueKind::ClassVarTooManyArguments,
            );
            TypeContent::UNKNOWN_REPORTED
        } else {
            let i_s = self.i_s;
            if i_s.current_class().is_none() || i_s.current_function().is_some() {
                self.add_issue(
                    slice_type.as_node_ref(),
                    IssueKind::ClassVarOnlyInAssignmentsInClass,
                );
                TypeContent::UNKNOWN_REPORTED
            } else {
                TypeContent::ClassVar(self.compute_slice_type(first))
            }
        }
    }

    fn compute_get_item_on_type_guard(
        &mut self,
        slice_type: SliceType,
        from_type_is: bool,
    ) -> TypeContent<'db, 'db> {
        let mut iterator = slice_type.iter();
        let first = iterator.next().unwrap();
        if iterator.next().is_some() {
            let name = if from_type_is { "TypeIs" } else { "TypeGuard" };
            self.add_issue(
                slice_type.as_node_ref(),
                IssueKind::MustHaveOneArgument { name },
            )
        }
        TypeContent::TypeGuardInfo(TypeGuardInfo {
            type_: self.compute_slice_type(first),
            from_type_is,
        })
    }

    fn compute_get_item_on_flexible_alias(
        &mut self,
        slice_type: SliceType,
    ) -> TypeContent<'db, 'db> {
        let add_issue = || {
            self.add_issue(
                slice_type.as_node_ref(),
                IssueKind::InvalidType("FlexibleAlias must have exactly two type arguments".into()),
            )
        };

        let mut iterator = slice_type.iter();
        let first = iterator.next().unwrap();
        let Some(second) = iterator.next() else {
            add_issue();
            return TypeContent::UNKNOWN_REPORTED;
        };
        if iterator.next().is_some() {
            add_issue();
        }
        self.compute_slice_type(first);
        TypeContent::Type(self.compute_slice_type(second))
    }

    fn expect_type_var_like_args(&mut self, slice_type: SliceType, class: &'static str) {
        for s in slice_type.iter() {
            let result = self.compute_slice_type_content(s);
            let unpacked_type_var_tuple = matches!(
                &result,
                TypeContent::Unpacked(TypeOrUnpack::TypeVarTuple(t))
                    if t.in_definition == self.for_definition
            );
            if !matches!(
                result,
                TypeContent::ParamSpec(_) | TypeContent::Unknown(UnknownCause::ReportedIssue)
            ) && !matches!(
                result,
                TypeContent::Type(Type::TypeVar(usage))
                    if usage.in_definition == self.for_definition
            ) && !unpacked_type_var_tuple
            {
                self.add_issue(s.as_node_ref(), IssueKind::TypeVarExpected { class })
            }
        }
    }

    fn compute_type_primary_or_atom(&mut self, p: PrimaryOrAtom<'x>) -> TypeContent<'db, 'x> {
        match p {
            PrimaryOrAtom::Primary(primary) => self.compute_type_primary(primary),
            PrimaryOrAtom::Atom(atom) => self.compute_type_atom(atom),
        }
    }

    fn compute_type_atom(&mut self, atom: Atom<'x>) -> TypeContent<'db, 'x> {
        match atom.unpack() {
            AtomContent::Name(n) => self.compute_type_name(n),
            AtomContent::Strings(s_o_b) => match s_o_b.as_python_string() {
                PythonString::Ref(start, s) => self.compute_forward_reference(start, s.into()),
                PythonString::String(start, s) => self.compute_forward_reference(start, s.into()),
                PythonString::FString => TypeContent::InvalidVariable(InvalidVariableType::Other),
            },
            AtomContent::NoneLiteral => TypeContent::Type(Type::None),
            AtomContent::List(_) => TypeContent::InvalidVariable(InvalidVariableType::List),
            AtomContent::Int(n) => {
                TypeContent::InvalidVariable(InvalidVariableType::Literal(n.as_code()))
            }
            AtomContent::Tuple(t) => TypeContent::InvalidVariable(InvalidVariableType::Tuple {
                tuple_length: t.iter().count(),
            }),
            AtomContent::Ellipsis => TypeContent::InvalidVariable(InvalidVariableType::Ellipsis),
            AtomContent::Float(_) => TypeContent::InvalidVariable(InvalidVariableType::Float),
            AtomContent::Complex(_) => TypeContent::InvalidVariable(InvalidVariableType::Complex),
            AtomContent::NamedExpression(ne) => match ne.unpack() {
                NamedExpressionContent::Expression(expr) => self.compute_type(expr),
                NamedExpressionContent::Walrus(_) => {
                    TypeContent::InvalidVariable(InvalidVariableType::Other)
                }
            },
            _ => TypeContent::InvalidVariable(InvalidVariableType::Other),
        }
    }

    fn compute_type_name(&mut self, name: Name<'x>) -> TypeContent<'db, 'x> {
        let lookup = NameResolution {
            file: self.file,
            i_s: self.i_s,
            stop_on_assignments: true,
        }
        .lookup_type_name(name);
        self.resolve_type_name_lookup(lookup, name.index())
    }

    fn resolve_type_name_lookup(
        &mut self,
        lookup: Lookup<'db, 'db>,
        origin_index: NodeIndex,
    ) -> TypeContent<'db, 'x> {
        match lookup {
            Lookup::T(c @ TypeContent::SpecialCase(Specific::TypingAny))
                if self.flags().disallow_any_explicit =>
            {
                self.add_issue(
                    NodeRef::new(self.file, origin_index),
                    IssueKind::DisallowedAnyExplicit,
                );
                c
            }
            Lookup::T(c) => c,
            Lookup::TypeVarLike(type_var_like) => {
                self.has_type_vars_or_self = true;
                match (self.type_var_callback)(
                    self.name_resolution.i_s,
                    &self.type_var_manager,
                    type_var_like.clone(),
                    self.current_callable,
                ) {
                    TypeVarCallbackReturn::TypeVarLike(TypeVarLikeUsage::TypeVar(usage)) => {
                        TypeContent::Type(Type::TypeVar(usage))
                    }
                    TypeVarCallbackReturn::TypeVarLike(TypeVarLikeUsage::TypeVarTuple(usage)) => {
                        TypeContent::TypeVarTuple(usage)
                    }
                    TypeVarCallbackReturn::TypeVarLike(TypeVarLikeUsage::ParamSpec(usage)) => {
                        TypeContent::ParamSpec(usage)
                    }
                    TypeVarCallbackReturn::UnboundTypeVar => {
                        let node_ref = NodeRef::new(self.file, origin_index);
                        node_ref
                            .add_issue(self.i_s, IssueKind::UnboundTypeVarLike { type_var_like });
                        TypeContent::UNKNOWN_REPORTED
                    }
                    TypeVarCallbackReturn::AddIssue(kind) => {
                        let node_ref = NodeRef::new(self.file, origin_index);
                        node_ref.add_issue(self.i_s, kind);
                        TypeContent::UNKNOWN_REPORTED
                    }
                    TypeVarCallbackReturn::NotFound {
                        allow_late_bound_callables,
                    } => {
                        let index = self.type_var_manager.add(
                            type_var_like.clone(),
                            self.current_callable.filter(|_| allow_late_bound_callables),
                        );
                        match type_var_like {
                            TypeVarLike::TypeVar(type_var) => TypeContent::Type(Type::TypeVar(
                                TypeVarUsage::new(type_var, self.for_definition, index),
                            )),
                            TypeVarLike::TypeVarTuple(type_var_tuple) => TypeContent::TypeVarTuple(
                                TypeVarTupleUsage::new(type_var_tuple, self.for_definition, index),
                            ),
                            TypeVarLike::ParamSpec(param_spec) => TypeContent::ParamSpec(
                                ParamSpecUsage::new(param_spec, self.for_definition, index),
                            ),
                        }
                    }
                }
            }
        }
    }

    fn execute_mypy_extension_param(
        &mut self,
        primary: Primary,
        specific: Specific,
        details: ArgumentsDetails,
    ) -> TypeContent<'db, 'db> {
        let mut name = None;
        let mut type_ = None;
        self.file
            .inference(self.i_s)
            .infer_primary(primary, &mut ResultContext::Unknown);
        if let ArgumentsDetails::Node(arguments) = details {
            let mut iterator = arguments.iter();
            let name_from_expr = |slf: &mut Self, expr: Expression| {
                let result = StringSlice::from_string_in_expression(slf.file.file_index, expr);
                if result.is_none() && !expr.is_none_literal() {
                    slf.add_issue_for_index(
                        expr.index(),
                        IssueKind::InvalidType("Name argument should be a string literal".into()),
                    );
                }
                result
            };
            let type_from_expr = |slf: &mut Self, expr: Expression| {
                let t = slf.compute_type(expr);
                Some(slf.as_type(t, NodeRef::new(slf.file, expr.index())))
            };
            let arg = iterator.next().unwrap();
            match arg {
                // The first arg is always there
                Argument::Positional(n) => type_ = type_from_expr(self, n.expression()),
                Argument::Keyword(kwarg) if kwarg.unpack().0.as_code() == "type" => {
                    type_ = type_from_expr(self, kwarg.unpack().1)
                }
                Argument::Keyword(kwarg) if kwarg.unpack().0.as_code() == "name" => {
                    name = name_from_expr(self, kwarg.unpack().1)
                }
                _ => (),
            };
            if let Some(named_arg) = iterator.next() {
                match named_arg {
                    Argument::Positional(named_expr) => {
                        name = name_from_expr(self, named_expr.expression())
                    }
                    Argument::Keyword(kwarg) if kwarg.unpack().0.as_code() == "name" => {
                        name = name_from_expr(self, kwarg.unpack().1)
                    }
                    Argument::Keyword(kwarg) if kwarg.unpack().0.as_code() == "type" => {
                        type_ = type_from_expr(self, kwarg.unpack().1)
                    }
                    _ => (),
                }
            }
        };
        let param_kind = match specific {
            Specific::MypyExtensionsNamedArg if name.is_some() => ParamKind::KeywordOnly,
            Specific::MypyExtensionsDefaultNamedArg if name.is_some() => ParamKind::KeywordOnly,
            Specific::MypyExtensionsVarArg => ParamKind::Star,
            Specific::MypyExtensionsKwArg => ParamKind::StarStar,
            _ => {
                if name.is_some() {
                    ParamKind::PositionalOrKeyword
                } else {
                    ParamKind::PositionalOnly
                }
            }
        };
        let type_ = type_.unwrap_or(Type::Any(AnyCause::Todo));
        TypeContent::CallableParam(CallableParam {
            type_: match param_kind {
                ParamKind::PositionalOnly => ParamType::PositionalOnly(type_),
                ParamKind::PositionalOrKeyword => ParamType::PositionalOrKeyword(type_),
                ParamKind::KeywordOnly => ParamType::KeywordOnly(type_),
                ParamKind::Star => ParamType::Star(StarParamType::ArbitraryLen(type_)),
                ParamKind::StarStar => ParamType::StarStar(StarStarParamType::ValueType(type_)),
            },
            name: name.map(|s| s.into()),
            has_default: matches!(
                specific,
                Specific::MypyExtensionsDefaultArg | Specific::MypyExtensionsDefaultNamedArg
            ),
            might_have_type_vars: true,
        })
    }

    pub fn into_type_vars<C>(self, on_type_var_recalculation: C) -> TypeVarLikes
    where
        C: FnOnce(&NameResolution, &dyn Fn(&Type) -> Type),
    {
        if self.type_var_manager.has_late_bound_type_vars() {
            on_type_var_recalculation(&self.name_resolution, &|t| {
                t.rewrite_late_bound_callables(&self.type_var_manager)
            })
        }
        self.type_var_manager.into_type_vars()
    }

    fn add_issue(&self, node_ref: NodeRef, issue_kind: IssueKind) {
        if !self.errors_already_calculated {
            node_ref.add_issue(self.i_s, issue_kind)
        }
    }

    fn add_issue_for_index(&self, index: NodeIndex, issue_kind: IssueKind) {
        self.add_issue(NodeRef::new(self.file, index), issue_kind)
    }

    fn add_module_issue(&self, node_ref: NodeRef, qualified_name: &str) {
        self.add_issue(
            node_ref,
            IssueKind::InvalidType(
                format!("Module \"{qualified_name}\" is not valid as a type",).into(),
            ),
        );
        self.add_issue(
            node_ref,
            IssueKind::Note(Box::from(
                "Perhaps you meant to use a protocol matching the module structure?",
            )),
        );
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum UnknownCause {
    ReportedIssue,
    AnyCause(AnyCause),
    UnknownName(AnyCause),
}

impl UnknownCause {
    fn into(self) -> AnyCause {
        match self {
            Self::ReportedIssue => AnyCause::FromError,
            Self::AnyCause(c) | Self::UnknownName(c) => c,
        }
    }
}

impl<'db, 'file> NameResolution<'db, 'file, '_> {
    fn lookup_type_name(&self, name: Name) -> Lookup<'db, 'db> {
        let resolved = self.resolve_name_without_narrowing(name);
        debug!(
            "Resolved type for {} to {}",
            name.as_code(),
            resolved.debug_info(self.i_s.db)
        );
        self.point_resolution_to_type_name_lookup(resolved)
    }

    fn lookup_primary_names(&self, p: Primary) -> Option<Lookup<'db, 'db>> {
        let base = match p.first() {
            PrimaryOrAtom::Atom(atom) => {
                let AtomContent::Name(name) = atom.unpack() else {
                    unreachable!()
                };
                self.lookup_type_name(name)
            }
            PrimaryOrAtom::Primary(primary) => self.lookup_primary_names(primary)?,
        };
        let PrimaryContent::Attribute(name) = p.second() else {
            unreachable!("Expect this to be called only with attributes")
        };
        let pr = match base {
            Lookup::T(TypeContent::Module(file)) => {
                let had_issue = Cell::new(false);
                let (pr, _) = self
                    .with_new_file(file)
                    .resolve_module_access(name.as_code(), |_| had_issue.set(true))?;
                if had_issue.get() {
                    return None;
                }
                pr
            }
            Lookup::T(TypeContent::Namespace(ns)) => {
                return match namespace_import(self.i_s.db, self.file, &ns, name.as_str())? {
                    ImportResult::File(file_index) => Some(Lookup::T(TypeContent::Module(
                        self.i_s.db.loaded_python_file(file_index),
                    ))),
                    ImportResult::Namespace(new) => Some(Lookup::T(TypeContent::Namespace(new))),
                    _ => None,
                }
            }
            Lookup::T(TypeContent::Class { node_ref, .. }) => {
                node_ref.ensure_cached_class_infos(self.i_s);
                let node_index = ClassInitializer::from_node_ref(node_ref)
                    .class_storage
                    .class_symbol_table
                    .lookup_symbol(name.as_str())?;
                self.with_new_file(node_ref.file)
                    .resolve_point_without_narrowing(node_index)
                    .unwrap_or_else(|| PointResolution::NameDef {
                        node_ref: NodeRef::new(node_ref.file, node_index).name_def_ref_of_name(),
                        global_redirect: false,
                    })
            }
            _ => return None,
        };
        Some(self.point_resolution_to_type_name_lookup(pr))
    }

    fn point_resolution_to_type_name_lookup(&self, resolved: PointResolution) -> Lookup<'db, 'db> {
        let i_s = self.i_s;

        let ensure_cached_class = |class_node_ref: ClassNodeRef<'db>| {
            // At this point the class is not necessarily calculated and we therefore do this here.
            if class_node_ref.is_calculating_class_infos() {
                return Lookup::T(TypeContent::RecursiveClass(class_node_ref));
            }

            class_node_ref.ensure_cached_class_infos(i_s);
            if let Some(t) = class_node_ref
                .use_cached_class_infos(i_s.db)
                .undefined_generics_type
                .get()
            {
                match t.as_ref() {
                    t @ Type::Enum(_) => return Lookup::T(TypeContent::Type(t.clone())),
                    Type::Dataclass(d) => return Lookup::T(TypeContent::Dataclass(d.clone())),
                    Type::TypedDict(td) => {
                        if td.calculating() {
                            return Lookup::T(TypeContent::RecursiveClass(
                                ClassNodeRef::from_link(i_s.db, td.defined_at),
                            ));
                        } else {
                            return Lookup::T(TypeContent::TypedDictDefinition(td.clone()));
                        }
                    }
                    _ => (),
                }
            }
            Lookup::T(TypeContent::Class {
                node_ref: class_node_ref,
                has_type_vars: !class_node_ref.type_vars(self.i_s).is_empty(),
            })
        };
        let func_is_invalid_type = |node_ref: NodeRef<'db>| {
            let func = Function::new_with_unknown_parent(i_s.db, node_ref);
            if let Some(specific) = node_ref
                .file
                .points
                .get(func.node().name_def().index())
                .maybe_calculated_and_specific()
            {
                if let Some(tc) = check_special_case(specific) {
                    return Lookup::T(tc);
                }
            }

            Lookup::T(TypeContent::InvalidVariable(
                InvalidVariableType::Function {
                    name: func.name(),
                    qualified_name: func.qualified_name(i_s.db),
                },
            ))
        };
        match resolved {
            PointResolution::NameDef {
                node_ref,
                global_redirect,
            } => {
                if node_ref.file_index() != self.file.file_index {
                    return self
                        .with_new_file(node_ref.file)
                        .point_resolution_to_type_name_lookup(resolved);
                }
                let node_ref = node_ref.to_db_lifetime(i_s.db);
                if node_ref.point().maybe_calculated_and_specific() == Some(Specific::Cycle) {
                    return Lookup::T(TypeContent::UNKNOWN_REPORTED);
                }

                let name_def = node_ref.as_name_def();
                return match name_def.expect_type() {
                    TypeLike::ClassDef(c) => {
                        cache_class_name(node_ref, c);
                        ensure_cached_class(ClassNodeRef::new(node_ref.file, c.index()))
                    }
                    TypeLike::Assignment(assignment) => {
                        if node_ref.point().calculated() {
                            if let Some(PointResolution::Inferred(inf)) =
                                self.resolve_point_without_narrowing(node_ref.node_index)
                            {
                                if let Some(n) = inf.maybe_saved_node_ref(self.i_s.db) {
                                    if let Some(tnl) = Self::check_special_type_definition(n) {
                                        return tnl;
                                    }
                                }
                            }
                        }
                        if global_redirect {
                            node_ref
                                .file
                                .name_resolution_for_types(&InferenceState::new(self.i_s.db))
                                .compute_type_assignment(assignment)
                        } else {
                            self.with_new_file(node_ref.file)
                                .compute_type_assignment(assignment)
                        }
                    }
                    TypeLike::ImportFromAsName(from_as_name) => self
                        .point_resolution_to_type_name_lookup(
                            self.resolve_import_from_name_def_without_narrowing(from_as_name),
                        ),
                    TypeLike::DottedAsName(dotted_as_name) => self
                        .point_resolution_to_type_name_lookup(
                            self.resolve_import_name_name_def_without_narrowing(dotted_as_name),
                        ),
                    TypeLike::Function(f) => {
                        let func_node_ref = NodeRef::new(node_ref.file, f.index());
                        func_is_invalid_type(func_node_ref)
                    }
                    TypeLike::ParamName(annotation) => Lookup::T(TypeContent::InvalidVariable({
                        let as_base_class_any = annotation
                            .map(|a| {
                                match use_cached_annotation_type(i_s.db, node_ref.file, a).as_ref()
                                {
                                    Type::Any(_) => true,
                                    Type::Type(t) => match t.as_ref() {
                                        Type::Any(_) => true,
                                        Type::Class(GenericClass {
                                            link,
                                            generics: ClassGenerics::None,
                                        }) => {
                                            *link == i_s.db.python_state.object_node_ref().as_link()
                                        }
                                        _ => false,
                                    },
                                    _ => false,
                                }
                            })
                            .unwrap_or(true);
                        if as_base_class_any {
                            InvalidVariableType::ParamNameAsBaseClassAny(node_ref)
                        } else {
                            InvalidVariableType::Variable(node_ref)
                        }
                    })),
                    TypeLike::Other => {
                        // Happens currently with walrus assignments
                        Lookup::T(TypeContent::InvalidVariable(InvalidVariableType::Variable(
                            node_ref,
                        )))
                    }
                };
            }
            PointResolution::Inferred(inferred) => {
                if let Some(i_node_ref) = inferred.maybe_saved_node_ref(i_s.db) {
                    if let Some(specific) = i_node_ref.point().maybe_specific() {
                        if let Some(tc) = check_special_case(specific) {
                            return Lookup::T(tc);
                        }
                        if matches!(
                            specific,
                            Specific::TypingTypeVarClass
                                | Specific::TypingTypeVarTupleClass
                                | Specific::TypingParamSpecClass
                        ) {
                            return Lookup::T(TypeContent::InvalidVariable(
                                InvalidVariableType::Variable(i_node_ref),
                            ));
                        }
                    } else if let Some(complex) = i_node_ref.complex() {
                        match complex {
                            ComplexPoint::TypeVarLike(tvl) => {
                                return Lookup::TypeVarLike(tvl.clone())
                            }
                            ComplexPoint::Class(_) => {
                                let c_node_ref = ClassNodeRef::from_node_ref(i_node_ref);
                                return ensure_cached_class(c_node_ref);
                            }
                            ComplexPoint::TypeAlias(a) => {
                                return Lookup::T(TypeContent::TypeAlias(a))
                            }
                            _ => (),
                        };
                        if let Some(r) = Self::check_special_type_definition(i_node_ref) {
                            return r;
                        }
                    }
                    if let Some(cause) = inferred.maybe_any(i_s.db) {
                        return Lookup::T(TypeContent::Unknown(UnknownCause::UnknownName(cause)));
                    } else if i_node_ref.maybe_function().is_some() {
                        return func_is_invalid_type(i_node_ref);
                    }
                }
                if let Some(file) = inferred.maybe_file(i_s.db) {
                    return Lookup::T(TypeContent::Module(i_s.db.loaded_python_file(file)));
                }
                if let Some(ComplexPoint::TypeInstance(Type::Namespace(ns))) =
                    inferred.maybe_complex_point(i_s.db)
                {
                    return Lookup::T(TypeContent::Namespace(ns.clone()));
                }
                if inferred.maybe_specific(i_s.db) == Some(Specific::ModuleNotFound) {
                    return Lookup::T(TypeContent::Unknown(UnknownCause::UnknownName(
                        AnyCause::ModuleNotFound,
                    )));
                }
            }
            PointResolution::ModuleGetattrName(name_node_ref) => {
                // TODO Avoid using inference here
                // If a module contains a __getattr__, the type can be part of that
                // (which is typically just an Any that propagates).
                let inf = name_node_ref.infer_name_of_definition_by_index(i_s);
                let executed = inf.execute(
                    i_s,
                    &KnownArgsWithCustomAddIssue::new(
                        &Inferred::from_type(i_s.db.python_state.str_type()),
                        &|_| (),
                    ),
                );
                if let Some(cause) = executed.maybe_any(i_s.db) {
                    return Lookup::T(TypeContent::Unknown(UnknownCause::AnyCause(cause)));
                }
            }
            _ => (),
        };
        Lookup::T(TypeContent::InvalidVariable(InvalidVariableType::Other))
    }

    fn maybe_special_assignment_execution<'x>(
        &self,
        expr: Expression<'x>,
    ) -> Result<(), CalculatingAliasType<'x>> {
        // For TypeVar, TypedDict, NewType and similar definitions
        let ExpressionContent::ExpressionPart(ExpressionPart::Primary(primary)) = expr.unpack()
        else {
            return Err(CalculatingAliasType::Normal);
        };
        let PrimaryContent::Execution(details) = primary.second() else {
            return Err(CalculatingAliasType::Normal);
        };
        match self.lookup_primary_or_atom_type(primary.first()) {
            Some(Lookup::T(TypeContent::SpecialCase(Specific::TypingTypedDict))) => {
                Err(CalculatingAliasType::TypedDict {
                    primary_index: primary.index(),
                    details,
                })
            }
            Some(Lookup::T(TypeContent::SpecialCase(Specific::TypingNamedTuple))) => {
                Err(CalculatingAliasType::NamedTuple {
                    primary_index: primary.index(),
                    details,
                })
            }
            _ => Ok(()),
        }
    }

    fn lookup_primary_or_atom_type(&self, p: PrimaryOrAtom) -> Option<Lookup<'db, 'db>> {
        match p {
            PrimaryOrAtom::Primary(primary) => match primary.second() {
                PrimaryContent::Attribute(name) => {
                    match self.lookup_primary_or_atom_type(primary.first())? {
                        Lookup::T(TypeContent::Module(f)) => {
                            Some(self.with_new_file(f).lookup_type_name(name))
                        }
                        _ => None,
                    }
                }
                _ => None,
            },
            PrimaryOrAtom::Atom(atom) => match atom.unpack() {
                AtomContent::Name(n) => Some(self.lookup_type_name(n)),
                _ => None,
            },
        }
    }

    pub fn ensure_cached_named_tuple_annotation(&self, annotation: Annotation) {
        self.ensure_cached_annotation_internal(annotation, TypeComputationOrigin::NamedTupleMember)
    }

    fn ensure_cached_annotation_internal(
        &self,
        annotation: Annotation,
        origin: TypeComputationOrigin,
    ) {
        if !self.file.points.get(annotation.index()).calculated() {
            let mut x = type_computation_for_variable_annotation;
            let mut comp = TypeComputation::new(
                self.i_s,
                self.file,
                PointLink::new(self.file.file_index, annotation.index()),
                &mut x,
                origin,
            );
            comp.cache_annotation(annotation.index(), annotation.expression(), false);
            comp.into_type_vars(|inf, recalculate_type_vars| {
                inf.recalculate_annotation_type_vars(annotation.index(), recalculate_type_vars);
            });
        }
    }

    pub fn ensure_cached_annotation(&self, annotation: Annotation, is_initialized: bool) {
        self.ensure_cached_annotation_internal(
            annotation,
            TypeComputationOrigin::AssignmentTypeCommentOrAnnotation {
                is_initialized,
                type_comment: false,
            },
        )
    }

    pub fn compute_type_application_on_class(
        &self,
        class: Class,
        slice_type: SliceType,
        from_alias_definition: bool,
    ) -> Inferred {
        compute_type_application!(
            self,
            slice_type,
            from_alias_definition,
            compute_type_get_item_on_class(class, slice_type, None)
        )
    }

    pub fn compute_type_application_on_dataclass(
        &self,
        dataclass: &Dataclass,
        slice_type: SliceType,
        from_alias_definition: bool,
    ) -> Inferred {
        compute_type_application!(
            self,
            slice_type,
            from_alias_definition,
            compute_type_get_item_on_dataclass(dataclass, slice_type, None)
        )
    }

    pub fn compute_type_application_on_named_tuple(
        &self,
        named_tuple: Rc<NamedTuple>,
        slice_type: SliceType,
        from_alias_definition: bool,
    ) -> Inferred {
        compute_type_application!(
            self,
            slice_type,
            from_alias_definition,
            compute_type_get_item_on_named_tuple(named_tuple, slice_type)
        )
    }

    pub fn compute_type_application_on_typed_dict(
        &self,
        typed_dict: &TypedDict,
        slice_type: SliceType,
        from_alias_definition: bool,
    ) -> Inferred {
        compute_type_application!(
            self,
            slice_type,
            from_alias_definition,
            compute_type_get_item_on_typed_dict(typed_dict, slice_type)
        )
    }

    pub fn compute_type_application_on_alias(
        &self,
        alias: &TypeAlias,
        slice_type: SliceType,
        from_alias_definition: bool,
    ) -> Inferred {
        if !from_alias_definition && !alias.application_allowed() {
            slice_type
                .as_node_ref()
                .add_issue(self.i_s, IssueKind::OnlyClassTypeApplication);
            return Inferred::new_any_from_error();
        }
        compute_type_application!(
            self,
            slice_type,
            from_alias_definition,
            compute_type_get_item_on_alias(alias, slice_type)
        )
    }

    pub fn compute_type_application_on_typing_class(
        &self,
        specific: Specific,
        slice_type: SliceType,
        from_alias_definition: bool,
    ) -> Inferred {
        match specific {
            Specific::TypingGeneric | Specific::TypingProtocol => {
                self.add_issue(
                    slice_type.cst_node.index(),
                    IssueKind::InvalidType("Invalid type application".to_string().into()),
                );
                Inferred::new_any_from_error()
            }
            Specific::TypingTuple => {
                compute_type_application!(
                    self,
                    slice_type,
                    from_alias_definition,
                    compute_type_get_item_on_tuple(slice_type)
                )
            }
            Specific::TypingCallable => {
                compute_type_application!(
                    self,
                    slice_type,
                    from_alias_definition,
                    compute_type_get_item_on_callable(slice_type)
                )
            }
            Specific::TypingUnion => {
                compute_type_application!(
                    self,
                    slice_type,
                    from_alias_definition,
                    compute_type_get_item_on_union(slice_type)
                )
            }
            Specific::TypingOptional => {
                compute_type_application!(
                    self,
                    slice_type,
                    from_alias_definition,
                    compute_type_get_item_on_optional(slice_type)
                )
            }
            Specific::TypingType | Specific::BuiltinsType => {
                compute_type_application!(
                    self,
                    slice_type,
                    from_alias_definition,
                    compute_type_get_item_on_type(slice_type)
                )
            }
            Specific::TypingLiteral => {
                compute_type_application!(
                    self,
                    slice_type,
                    from_alias_definition,
                    compute_get_item_on_literal(slice_type)
                )
            }
            Specific::TypingAnnotated => {
                compute_type_application!(
                    self,
                    slice_type,
                    from_alias_definition,
                    compute_get_item_on_annotated(slice_type)
                )
            }
            Specific::MypyExtensionsFlexibleAlias => {
                compute_type_application!(
                    self,
                    slice_type,
                    from_alias_definition,
                    compute_get_item_on_flexible_alias(slice_type)
                )
            }
            _ => unreachable!("{:?}", specific),
        }
    }

    #[inline]
    pub(super) fn use_cached_param_annotation(&self, annotation: ParamAnnotation) -> Inferred {
        if cfg!(debug_assertions) {
            let point = self.file.points.get(annotation.index());
            debug_assert!(
                matches!(
                    point.specific(),
                    Specific::AnnotationOrTypeCommentWithTypeVars
                        | Specific::AnnotationOrTypeCommentWithoutTypeVars
                        | Specific::AnnotationOrTypeCommentSimpleClassInstance
                        | Specific::AnnotationOrTypeCommentClassVar
                        | Specific::AnnotationOrTypeCommentFinal
                ),
                "{point:?}"
            );
        }
        Inferred::from_saved_link(PointLink::new(self.file.file_index, annotation.index()))
    }

    pub(super) fn use_cached_annotation(&self, annotation: Annotation) -> Inferred {
        if cfg!(debug_assertions) {
            let point = self.file.points.get(annotation.index());
            debug_assert!(
                matches!(
                    point.specific(),
                    Specific::AnnotationOrTypeCommentWithTypeVars
                        | Specific::AnnotationOrTypeCommentWithoutTypeVars
                        | Specific::AnnotationOrTypeCommentSimpleClassInstance
                        | Specific::AnnotationOrTypeCommentClassVar
                        | Specific::AnnotationOrTypeCommentFinal
                ),
                "{point:?}"
            );
        }
        Inferred::from_saved_link(PointLink::new(self.file.file_index, annotation.index()))
    }

    pub fn use_cached_return_annotation(&self, annotation: ReturnAnnotation) -> Inferred {
        if cfg!(debug_assertions) {
            let point = self.file.points.get(annotation.index());
            debug_assert!(
                matches!(
                    point.specific(),
                    Specific::AnnotationOrTypeCommentWithTypeVars
                        | Specific::AnnotationOrTypeCommentWithoutTypeVars
                        | Specific::AnnotationOrTypeCommentSimpleClassInstance
                ),
                "{point:?}"
            );
        }
        Inferred::from_saved_link(PointLink::new(self.file.file_index, annotation.index()))
    }

    pub fn use_cached_return_annotation_type(
        &self,
        annotation: ReturnAnnotation,
    ) -> Cow<'file, Type> {
        self.use_cached_annotation_or_type_comment_type_internal(
            annotation.index(),
            annotation.expression(),
        )
    }

    pub fn use_cached_annotation_type(&self, annotation: Annotation) -> Cow<'file, Type> {
        self.use_cached_annotation_or_type_comment_type_internal(
            annotation.index(),
            annotation.expression(),
        )
    }

    pub fn use_cached_param_annotation_type(
        &self,
        annotation: ParamAnnotation,
    ) -> Cow<'file, Type> {
        self.use_cached_maybe_starred_annotation_type_internal(
            annotation.index(),
            annotation.maybe_starred(),
        )
    }

    fn use_cached_maybe_starred_annotation_type_internal(
        &self,
        annotation_index: NodeIndex,
        maybe_starred: Result<StarExpression, Expression>,
    ) -> Cow<'file, Type> {
        match maybe_starred {
            Ok(star_expr) => {
                debug_assert!(matches!(
                    self.file.points.get(annotation_index).specific(),
                    Specific::AnnotationOrTypeCommentWithTypeVars
                        | Specific::AnnotationOrTypeCommentWithoutTypeVars
                ));
                self.use_cached_annotation_internal(star_expr.index())
            }
            Err(expr) => {
                self.use_cached_annotation_or_type_comment_type_internal(annotation_index, expr)
            }
        }
    }

    fn use_cached_annotation_or_type_comment_type_internal(
        &self,
        annotation_index: NodeIndex,
        expr: Expression,
    ) -> Cow<'file, Type> {
        let point = self.file.points.get(annotation_index);
        assert!(point.calculated(), "Expr: {:?}", expr);
        match point.specific() {
            Specific::AnnotationOrTypeCommentSimpleClassInstance => {
                expect_class_or_simple_generic(self.i_s.db, NodeRef::new(self.file, expr.index()))
            }
            _ => {
                debug_assert!(
                    matches!(
                        point.specific(),
                        Specific::AnnotationOrTypeCommentWithTypeVars
                            | Specific::AnnotationOrTypeCommentWithoutTypeVars
                            | Specific::AnnotationOrTypeCommentClassVar
                            | Specific::AnnotationOrTypeCommentFinal
                    ),
                    "{:?}",
                    point.specific()
                );
                self.use_cached_annotation_internal(expr.index())
            }
        }
    }

    fn use_cached_annotation_internal(&self, type_storage_index: NodeIndex) -> Cow<'file, Type> {
        let complex_index = self.file.points.get(type_storage_index).complex_index();
        match self.file.complex_points.get(complex_index) {
            ComplexPoint::TypeInstance(t) => Cow::Borrowed(t),
            _ => unreachable!(),
        }
    }

    pub fn recalculate_annotation_type_vars(
        &self,
        node_index: NodeIndex,
        recalculate: impl Fn(&Type) -> Type,
    ) {
        if matches!(
            self.file.points.get(node_index).specific(),
            Specific::AnnotationOrTypeCommentWithTypeVars
                | Specific::AnnotationOrTypeCommentClassVar
        ) {
            let new_t = recalculate(&use_cached_annotation_or_type_comment(
                self.i_s,
                NodeRef::new(self.file, node_index),
            ));
            self.file.complex_points.insert(
                &self.file.points,
                node_index + ANNOTATION_TO_EXPR_DIFFERENCE,
                ComplexPoint::TypeInstance(new_t),
                Locality::Todo,
            )
        }
    }

    fn check_special_assignments<'x>(
        &self,
        assignment: Assignment,
        name_def: NameDef,
        expr: Expression<'x>,
    ) -> Result<Lookup<'file, 'file>, CalculatingAliasType<'x>> {
        self.maybe_special_assignment_execution(expr)?;
        if self.file.points.get(name_def.index()).calculating() {
            // TODO this is wrong, circular functional NamedTuples/TypedDicts are not implemented
            // properly now
            return Ok(Lookup::UNKNOWN_REPORTED);
        }
        self.infer_special_type_definition(assignment, name_def)
            .ok_or(CalculatingAliasType::Normal)
    }

    fn infer_special_type_definition(
        &self,
        assignment: Assignment,
        name_def: NameDef,
    ) -> Option<Lookup<'db, 'db>> {
        // We use inference from here on, because we know this is not really infering crazy stuff,
        // it's just running the normal initalizers for our special cases.
        // Inference is not a good idea to run otherwise, because it uses a lot of narrowing.
        debug!(
            "Infer special definition for assignment {:?}",
            assignment.as_code()
        );
        let inference = self.file.inference(self.i_s);
        inference.cache_assignment(assignment);
        let inf = inference.check_point_cache(name_def.index())?;
        let saved_node_ref = inf.maybe_saved_node_ref(self.i_s.db)?;
        if matches!(
            saved_node_ref.point().maybe_specific(),
            Some(Specific::InvalidTypeDefinition)
        ) {
            return Some(Lookup::UNKNOWN_REPORTED);
        }
        Self::check_special_type_definition(saved_node_ref)
    }

    fn check_special_type_definition(node_ref: NodeRef) -> Option<Lookup> {
        Some(Lookup::T(match node_ref.complex()? {
            ComplexPoint::TypeVarLike(tv) => return Some(Lookup::TypeVarLike(tv.clone())),
            ComplexPoint::NamedTupleDefinition(t) => {
                let Type::NamedTuple(nt) = t.as_ref() else {
                    unreachable!()
                };
                TypeContent::NamedTuple(nt.clone())
            }
            ComplexPoint::NewTypeDefinition(n) => TypeContent::Type(Type::NewType(n.clone())),
            ComplexPoint::TypedDictDefinition(tdd) => {
                let Type::TypedDict(td) = tdd.type_.as_ref() else {
                    unreachable!();
                };
                TypeContent::TypedDictDefinition(td.clone())
            }
            ComplexPoint::TypeInstance(Type::Type(t)) => match t.as_ref() {
                t @ Type::Enum(_) => TypeContent::Type(t.clone()),
                Type::None => TypeContent::Type(Type::None),
                _ => return None,
            },
            _ => return None,
        }))
    }

    pub(crate) fn infer_special_calculated_type_assignment(
        &self,
        specific: Specific,
        assignment: Assignment,
    ) -> Inferred {
        debug_assert!(matches!(
            specific,
            Specific::TypingTypedDict | Specific::TypingNamedTuple
        ));
        match self.compute_type_assignment(assignment) {
            Lookup::T(TypeContent::TypeAlias(ta)) => {
                if ta.is_valid() {
                    Inferred::from_type(Type::Type(Rc::new(ta.type_if_valid().clone())))
                } else {
                    Inferred::new_any_from_error()
                }
            }
            // Error should have been created, because it's an invalid alias.
            Lookup::T(TypeContent::InvalidVariable(_) | TypeContent::Unknown(_)) => {
                match specific {
                    Specific::TypingTypedDict => self.add_issue(
                        assignment.index(),
                        IssueKind::InvalidAssignmentForm {
                            class_name: "TypedDict",
                        },
                    ),
                    Specific::TypingNamedTuple => todo!(),
                    _ => unreachable!(),
                }
                Inferred::new_any_from_error()
            }
            tnl => {
                recoverable_error!("Unexpected special type assignment result: {tnl:?}");
                Inferred::new_any_from_error()
            }
        }
    }

    fn compute_type_assignment(&self, assignment: Assignment) -> Lookup<'file, 'file> {
        let is_explicit = match assignment.maybe_annotation() {
            Some(annotation) => {
                self.ensure_cached_annotation(annotation, true);
                self.file.points.get(annotation.index()).maybe_specific()
                    == Some(Specific::AnnotationTypeAlias)
            }
            None => false,
        };
        self.compute_type_assignment_internal(assignment, is_explicit)
    }

    fn compute_type_assignment_internal(
        &self,
        assignment: Assignment,
        is_explicit: bool,
    ) -> Lookup<'file, 'file> {
        // Use the node star_targets or single_target, because they are not used otherwise.
        let file = self.file;
        let cached_type_node_ref = assignment_type_node_ref(file, assignment);
        let point = cached_type_node_ref.point();
        if point.calculated() {
            return load_cached_type(cached_type_node_ref);
        }

        if !is_explicit {
            // Only non-explicit TypeAliases are allowed here.
            if let Some(name_or_prim) = assignment.maybe_simple_type_reassignment() {
                // For very simple cases like `Foo = int`. Not sure yet if this going to stay.
                debug!(
                    "Found alias that could maybe just be redirected: {}",
                    assignment.as_code()
                );
                let lookup = debug_indent(|| match name_or_prim {
                    NameOrPrimaryWithNames::Name(name) => Some(self.lookup_type_name(name)),
                    NameOrPrimaryWithNames::PrimaryWithNames(primary) => {
                        self.lookup_primary_names(primary)
                    }
                });
                match lookup {
                    Some(Lookup::T(TypeContent::SpecialCase(Specific::TypingAny))) => {
                        // This is a bit of a weird special case that was necessary to pass the test
                        // testDisallowAnyExplicitAlias
                        if self.flags().disallow_any_explicit {
                            NodeRef::new(file, name_or_prim.index())
                                .add_issue(self.i_s, IssueKind::DisallowedAnyExplicit)
                        }
                    }
                    // It seems like Mypy is ignoring this?
                    Some(Lookup::T(TypeContent::SpecialType(_))) => (),
                    Some(lookup) => {
                        debug!("Alias can be redirected: {lookup:?}");
                        return lookup;
                    }
                    _ => {
                        debug!("Alias can not be redirected");
                    }
                }
            }
        }
        if let Some((name_def, annotation, expr)) =
            assignment.maybe_simple_type_expression_assignment()
        {
            debug!("Started type alias calculation: {}", name_def.as_code());
            if let Some(type_comment) = self.check_for_type_comment_internal(assignment, || {
                file.points
                    .get(name_def.index())
                    .maybe_calculated_and_specific()
                    == Some(Specific::Cycle)
            }) {
                // This case is a bit weird in Mypy, but it makes it possible to use a type
                // definition like:
                //
                //     Foo = 1  # type: Any
                if let TypeCommentState::Type(t) = &type_comment.type_ {
                    if let Type::Any(cause) = t.as_ref() {
                        return Lookup::T(TypeContent::Unknown(UnknownCause::AnyCause(*cause)));
                    }
                }
            }
            if !is_explicit
                && (expr.maybe_single_string_literal().is_some() || annotation.is_some())
            {
                return Lookup::T(TypeContent::InvalidVariable(InvalidVariableType::Variable(
                    NodeRef::new(file, name_def.index()),
                )));
            }

            let check_for_alias = |origin| {
                self.check_for_alias(origin, cached_type_node_ref, name_def, expr, is_explicit)
            };

            if is_explicit {
                return check_for_alias(CalculatingAliasType::Normal);
            }

            let result = self
                .check_special_assignments(assignment, name_def, expr)
                .unwrap_or_else(|origin| check_for_alias(origin));
            debug!("Finished type alias calculation: {}", name_def.as_code());
            result
        } else {
            if let AssignmentContent::WithAnnotation(target, annotation, right) =
                assignment.unpack()
            {
                let calculating = match target {
                    Target::Name(n) => {
                        file.points.get(n.index()).maybe_calculated_and_specific()
                            == Some(Specific::Cycle)
                    }
                    _ => false,
                };
                if calculating {
                    return Lookup::UNKNOWN_REPORTED;
                }
                self.ensure_cached_annotation(annotation, right.is_some());
                if let Type::Any(cause) = self.use_cached_annotation_type(annotation).as_ref() {
                    return Lookup::T(TypeContent::Unknown(UnknownCause::AnyCause(*cause)));
                }
            }
            Lookup::T(TypeContent::InvalidVariable(InvalidVariableType::Other))
        }
    }

    fn check_for_alias(
        &self,
        origin: CalculatingAliasType,
        cached_type_node_ref: NodeRef<'file>,
        name_def: NameDef,
        expr: Expression,
        is_explicit: bool,
    ) -> Lookup<'file, 'file> {
        cached_type_node_ref.set_point(Point::new_calculating());
        let find_type_var_likes = || match &origin {
            CalculatingAliasType::Normal => {
                TypeVarFinder::find_alias_type_vars(self.i_s, self.file, expr)
            }
            CalculatingAliasType::TypedDict { details, .. }
            | CalculatingAliasType::NamedTuple { details, .. } => {
                if let ArgumentsDetails::Node(n) = details {
                    // Skip the name
                    if let Some(arg) = n.iter().nth(1) {
                        if let Argument::Positional(pos) = arg {
                            return TypeVarFinder::find_alias_type_vars(
                                self.i_s,
                                self.file,
                                pos.expression(),
                            );
                        }
                    }
                }
                self.i_s.db.python_state.empty_type_var_likes.clone()
            }
        };
        let type_var_likes = find_type_var_likes();

        let in_definition = cached_type_node_ref.as_link();
        let alias = TypeAlias::new(
            type_var_likes,
            in_definition,
            Some(PointLink::new(
                self.file.file_index,
                name_def.name().index(),
            )),
        );
        save_alias(cached_type_node_ref, alias);

        let mut type_var_manager = TypeVarManager::<PointLink>::default();
        let mut type_var_callback = |_: &InferenceState, _: &_, type_var_like: TypeVarLike, _| {
            // Here we avoid all late bound type var calculation for callable, which is how
            // mypy works. The default behavior without a type_var_callback would be to
            // just calculate all late bound type vars, but that would mean that something
            // like `Foo = Callable[[T], T]` could not be used like `Foo[int]`, which is
            // generally how type aliases work.
            let index = type_var_manager.add(type_var_like.clone(), None);
            TypeVarCallbackReturn::TypeVarLike(
                type_var_like.as_type_var_like_usage(index, in_definition),
            )
        };
        let p = self.file.points.get(expr.index());
        let mut comp = TypeComputation::new(
            self.i_s,
            self.file,
            in_definition,
            &mut type_var_callback,
            match &origin {
                CalculatingAliasType::Normal => TypeComputationOrigin::TypeAlias,
                CalculatingAliasType::TypedDict { .. } => TypeComputationOrigin::TypedDictMember,
                CalculatingAliasType::NamedTuple { .. } => TypeComputationOrigin::NamedTupleMember,
            },
        );
        let ComplexPoint::TypeAlias(alias) = cached_type_node_ref.complex().unwrap() else {
            unreachable!()
        };
        match origin {
            CalculatingAliasType::Normal => {
                comp.errors_already_calculated = p.calculated();
                let tc = comp.compute_type(expr);
                let node_ref = NodeRef::new(self.file, expr.index());
                match tc {
                    TypeContent::InvalidVariable(_)
                    | TypeContent::Unknown(UnknownCause::UnknownName(_))
                        if !is_explicit =>
                    {
                        alias.set_invalid();
                    }
                    _ => {
                        let type_ = comp.as_type(tc, node_ref);
                        let is_recursive_alias = comp.is_recursive_alias;
                        debug_assert!(!comp.type_var_manager.has_type_vars());
                        let mut had_error = false;
                        if is_recursive_alias && self.i_s.current_function().is_some() {
                            node_ref.add_issue(
                                self.i_s,
                                IssueKind::RecursiveTypesNotAllowedInFunctionScope {
                                    alias_name: name_def.as_code().into(),
                                },
                            );
                            had_error = true;
                        }
                        if is_invalid_recursive_alias(
                            self.i_s.db,
                            &SeenRecursiveAliases::new(in_definition),
                            &type_,
                        ) {
                            node_ref.add_issue(
                                self.i_s,
                                IssueKind::InvalidRecursiveTypeAliasUnionOfItself {
                                    target: "union",
                                },
                            );
                            had_error = true;
                        }
                        // This is called detect_diverging_alias in Mypy as well.
                        if detect_diverging_alias(self.i_s.db, &alias.type_vars, &type_) {
                            node_ref.add_issue(
                                self.i_s,
                                IssueKind::InvalidRecursiveTypeAliasTypeVarNesting,
                            );
                            had_error = true;
                        }
                        if had_error {
                            alias.set_valid(Type::ERROR, false);
                        } else {
                            alias.set_valid(type_, is_recursive_alias);
                        }
                        if is_recursive_alias {
                            // Since the type aliases are not finished at the time of the type
                            // calculation, we need to recheck for Type[Type[...]]. It is however
                            // very important that this happens after setting the alias, otherwise
                            // something like X = Type[X] is not recognized.
                            check_for_and_replace_type_type_in_finished_alias(
                                self.i_s,
                                cached_type_node_ref,
                                alias,
                            );
                        }
                    }
                };
            }
            CalculatingAliasType::TypedDict {
                primary_index,
                details,
            } => {
                match new_typed_dict_with_execution_syntax(
                    self.i_s,
                    &mut comp,
                    &SimpleArgs::new(*self.i_s, self.file, primary_index, details),
                ) {
                    Some((name, members, _)) => {
                        alias.set_valid(
                            Type::TypedDict(TypedDict::new_definition(
                                name,
                                members,
                                alias.location,
                                alias.type_vars.clone(),
                            )),
                            comp.is_recursive_alias,
                        );
                    }
                    None => alias.set_valid(Type::ERROR, false),
                }
            }
            CalculatingAliasType::NamedTuple {
                primary_index,
                details,
            } => {
                match new_typing_named_tuple_internal(
                    self.i_s,
                    &mut comp,
                    &SimpleArgs::new(*self.i_s, self.file, primary_index, details),
                ) {
                    Some((name, params)) => {
                        alias.set_valid(
                            Type::NamedTuple(NamedTuple::from_params(
                                alias.location,
                                name,
                                alias.type_vars.clone(),
                                params,
                            )),
                            comp.is_recursive_alias,
                        );
                    }
                    None => alias.set_valid(Type::ERROR, false),
                }
            }
        };
        debug!(
            "Alias {}={} on #{} is valid? {}",
            name_def.as_code(),
            expr.as_code(),
            NodeRef::new(self.file, expr.index()).line(),
            alias.is_valid()
        );
        load_cached_type(cached_type_node_ref)
    }

    pub(crate) fn compute_explicit_type_assignment(&self, assignment: Assignment) -> Inferred {
        let name_lookup = self.compute_type_assignment_internal(assignment, true);
        if matches!(
            name_lookup,
            Lookup::T(TypeContent::Unknown(_) | TypeContent::InvalidVariable(_))
        ) {
            return Inferred::new_any(AnyCause::FromError);
        }
        Inferred::from_saved_node_ref(assignment_type_node_ref(self.file, assignment))
    }

    pub(super) fn compute_type_comment(
        &self,
        start: CodeIndex,
        s: &str,
        assignment_node_ref: NodeRef,
    ) -> TypeCommentDetails<'db> {
        let f: &'db PythonFile =
            self.file
                .ensure_annotation_file(self.i_s.db, start, s.trim_end_matches('\\').into());
        let name_resolution = self.with_new_file(f);
        if let Some(star_exprs) = f.tree.maybe_star_expressions() {
            match star_exprs.unpack() {
                StarExpressionContent::Expression(expr) => {
                    // It is kind of a hack to use the ANNOTATION_TO_EXPR_DIFFERENCE here. However this
                    // allows us to reuse the code for annotations completely and the nodes before the expr
                    // should really never be used by anything productive.
                    let expr_index = expr.index();
                    let index = expr_index - ANNOTATION_TO_EXPR_DIFFERENCE;
                    if let Some(tuple) = expr.maybe_tuple() {
                        let type_ = name_resolution
                            .calc_type_comment_tuple(assignment_node_ref, tuple.iter());
                        NodeRef::new(f, index).set_point(Point::new_specific(
                            Specific::AnnotationOrTypeCommentWithTypeVars,
                            Locality::Todo,
                        ));
                        NodeRef::new(f, expr_index).insert_type(type_);
                    } else {
                        let mut x = type_computation_for_variable_annotation;
                        let mut comp = TypeComputation::new(
                            self.i_s,
                            f,
                            assignment_node_ref.as_link(),
                            &mut x,
                            TypeComputationOrigin::AssignmentTypeCommentOrAnnotation {
                                is_initialized: true,
                                type_comment: true,
                            },
                        );
                        comp.cache_annotation_or_type_comment(index, expr, false, None);
                        let type_vars = comp.into_type_vars(|inf, recalculate_type_vars| {
                            inf.recalculate_annotation_type_vars(index, recalculate_type_vars);
                        });
                        debug_assert!(type_vars.is_empty());
                    }
                    let inf_node_ref = NodeRef::new(f, index);
                    TypeCommentDetails {
                        inferred: Inferred::from_saved_node_ref(inf_node_ref),
                        type_: if !NodeRef::new(f, expr_index).point().calculated()
                            && matches!(
                                inf_node_ref.point().maybe_specific(),
                                Some(
                                    Specific::AnnotationOrTypeCommentFinal
                                        | Specific::AnnotationOrTypeCommentClassVar
                                )
                            ) {
                            TypeCommentState::UnfinishedFinalOrClassVar(inf_node_ref)
                        } else {
                            TypeCommentState::Type(
                                name_resolution
                                    .use_cached_annotation_or_type_comment_type_internal(
                                        index, expr,
                                    ),
                            )
                        },
                    }
                }
                StarExpressionContent::Tuple(t) => {
                    let star_exprs_index = star_exprs.index();
                    let index = star_exprs_index - ANNOTATION_TO_EXPR_DIFFERENCE;
                    let type_ =
                        name_resolution.calc_type_comment_tuple(assignment_node_ref, t.iter());
                    NodeRef::new(f, index).insert_type(type_);
                    let complex_index = f.points.get(index).complex_index();
                    TypeCommentDetails {
                        inferred: Inferred::from_saved_node_ref(NodeRef::new(f, index)),
                        type_: if let ComplexPoint::TypeInstance(type_) =
                            f.complex_points.get(complex_index)
                        {
                            TypeCommentState::Type(Cow::Borrowed(type_))
                        } else {
                            unreachable!()
                        },
                    }
                }
                StarExpressionContent::StarExpression(s) => {
                    self.add_issue(
                        s.index(),
                        IssueKind::InvalidType(
                            "Star expressions are not allowed within a type comment".into(),
                        ),
                    );
                    TypeCommentDetails::new_any()
                }
            }
        } else {
            for s in f.tree.root().iter_stmt_likes() {
                if let StmtLikeContent::Error(_) = s.node {
                    return TypeCommentDetails::new_any();
                }
            }
            debug!("Found non-expression in annotation: {}", f.tree.code());
            self.file.add_issue(
                self.i_s,
                Issue {
                    start_position: start,
                    end_position: start + s.len() as CodeIndex,
                    kind: IssueKind::InvalidSyntaxInTypeComment {
                        type_comment: s.trim().into(),
                    },
                },
            );
            TypeCommentDetails::new_any()
        }
    }

    fn calc_type_comment_tuple<'s>(
        &self,
        assignment_node_ref: NodeRef,
        iterator: impl Iterator<Item = StarLikeExpression<'s>>,
    ) -> Type {
        let generics = iterator
            .map(|star_like| {
                let expr = match star_like {
                    StarLikeExpression::NamedExpression(named_expr) => named_expr.expression(),
                    StarLikeExpression::StarNamedExpression(s) => {
                        self.add_issue(
                            s.index(),
                            IssueKind::InvalidType(
                                "Star expressions are not allowed within a type comment".into(),
                            ),
                        );
                        return Type::ERROR;
                    }
                    StarLikeExpression::Expression(expr) => expr,
                    StarLikeExpression::StarExpression(_) => unreachable!(),
                };
                if let Some(tuple) = expr.maybe_tuple() {
                    self.calc_type_comment_tuple(assignment_node_ref, tuple.iter())
                } else {
                    let expr_node_ref = NodeRef::new(self.file, expr.index());
                    let mut x = type_computation_for_variable_annotation;
                    let mut comp = TypeComputation::new(
                        self.i_s,
                        self.file,
                        assignment_node_ref.as_link(),
                        &mut x,
                        TypeComputationOrigin::AssignmentTypeCommentOrAnnotation {
                            is_initialized: true,
                            type_comment: true,
                        },
                    );
                    let t = comp.compute_type(expr);
                    let mut type_ = comp.as_type(t, expr_node_ref);
                    let type_vars = comp.into_type_vars(|_, recalculate_type_vars| {
                        type_ = recalculate_type_vars(&type_);
                    });
                    debug_assert!(type_vars.is_empty());
                    type_
                }
            })
            .collect();
        Type::Tuple(Tuple::new_fixed_length(generics))
    }

    pub fn check_for_type_comment(
        &self,
        assignment: Assignment,
    ) -> Option<TypeCommentDetails<'db>> {
        self.check_for_type_comment_internal(assignment, || false)
    }

    fn check_for_type_comment_internal(
        &self,
        assignment: Assignment,
        is_cycle: impl Fn() -> bool,
    ) -> Option<TypeCommentDetails<'db>> {
        let suffix = assignment.suffix();
        if let Some(start) = suffix.find('#') {
            let mut start = start + 1;
            let after_hash = &suffix[start..];
            const TYPE: &str = "type:";
            if let Some(after) = after_hash.trim_start_matches(' ').strip_prefix(TYPE) {
                let full_rest = after.trim_start_matches(' ');
                // Use only the part before the comment after the type definition.
                let s = full_rest.split('#').next().unwrap();
                start += after_hash.len() - full_rest.len();
                if is_cycle() {
                    return None;
                }
                debug!("Infer type comment {s:?} on {:?}", assignment.as_code());
                if maybe_type_ignore(s).is_none() {
                    return Some(self.compute_type_comment(
                        assignment.end() + start as CodeIndex,
                        s,
                        NodeRef::new(self.file, assignment.index()),
                    ));
                }
            }
        }
        None
    }
    pub fn compute_cast_target(&self, node_ref: NodeRef) -> Result<Inferred, ()> {
        let named_expr = node_ref.as_named_expression();
        let mut x = type_computation_for_variable_annotation;
        let mut comp = TypeComputation::new(
            self.i_s,
            self.file,
            node_ref.as_link(),
            &mut x,
            TypeComputationOrigin::CastTarget,
        );

        let t = comp.compute_type(named_expr.expression());
        let Some(mut type_) = comp.as_type_or_error(t, node_ref) else {
            return Err(());
        };
        let type_vars = comp.into_type_vars(|_, recalculate_type_vars| {
            type_ = recalculate_type_vars(&type_);
        });
        debug_assert!(type_vars.is_empty());
        Ok(Inferred::from_type(type_))
    }

    fn within_type_var_like_definition<T>(
        &self,
        node_ref: NodeRef,
        callback: impl FnOnce(TypeComputation) -> T,
    ) -> T {
        let in_definition = node_ref.as_link();
        let mut on_type_var = |i_s: &InferenceState, _: &_, type_var_like, _| {
            i_s.find_parent_type_var(&type_var_like).unwrap_or_else(
                || TypeVarCallbackReturn::NotFound {
                    allow_late_bound_callables: true,
                }, // TODO it should probably something like this for recursive TypeVar defaults
                   // || TypeVarCallbackReturn::TypeVarLike(type_var_like.as_type_var_like_usage(?, in_definition))
            )
        };
        let comp = TypeComputation::new(
            self.i_s,
            self.file,
            in_definition,
            &mut on_type_var,
            TypeComputationOrigin::Other,
        );
        callback(comp)
    }

    pub fn compute_type_var_bound(&self, expr: Expression) -> Type {
        let node_ref = NodeRef::new(self.file, expr.index());
        self.within_type_var_like_definition(node_ref, |mut comp| {
            match comp.compute_type(expr) {
                TypeContent::InvalidVariable(_) => {
                    // TODO this is a bit weird and should probably generate other errors
                    node_ref.add_issue(comp.i_s, IssueKind::TypeVarBoundMustBeType);
                    Type::ERROR
                }
                t => comp.as_type(t, node_ref),
            }
        })
    }
    pub fn compute_type_var_value(&self, expr: Expression) -> Option<Type> {
        let node_ref = NodeRef::new(self.file, expr.index());
        let mut on_type_var = |i_s: &InferenceState, _: &_, type_var_like, _| {
            if i_s.find_parent_type_var(&type_var_like).is_some() {
                TypeVarCallbackReturn::AddIssue(IssueKind::TypeVarConstraintCannotHaveTypeVariables)
            } else {
                TypeVarCallbackReturn::UnboundTypeVar
            }
        };
        let mut comp = TypeComputation::new(
            self.i_s,
            self.file,
            node_ref.as_link(),
            &mut on_type_var,
            TypeComputationOrigin::Other,
        );
        match comp.compute_type(expr) {
            TypeContent::InvalidVariable(invalid @ InvalidVariableType::Literal(_)) => {
                invalid.add_issue(
                    comp.i_s.db,
                    |t| node_ref.add_issue(comp.i_s, t),
                    comp.origin,
                );
                None
            }
            TypeContent::InvalidVariable(_) => {
                // TODO this is a bit weird and should probably generate other errors
                node_ref.add_issue(comp.i_s, IssueKind::TypeVarTypeExpected);
                None
            }
            t => Some(comp.as_type(t, node_ref)),
        }
    }

    pub fn compute_type_var_default(&self, expr: Expression) -> Option<Type> {
        let node_ref = NodeRef::new(self.file, expr.index());
        self.within_type_var_like_definition(node_ref, |mut comp| {
            let tc = comp.compute_type(expr);
            Some(comp.as_type(tc, node_ref))
        })
    }

    pub fn compute_param_spec_default(&self, expr: Expression) -> Option<CallableParams> {
        let node_ref = NodeRef::new(self.file, expr.index());
        self.within_type_var_like_definition(node_ref, |mut comp| {
            comp.calculate_callable_params_for_expr(expr, false, false)
        })
    }

    pub fn compute_type_var_tuple_default(&self, expr: Expression) -> Option<TypeArgs> {
        let node_ref = NodeRef::new(self.file, expr.index());
        self.within_type_var_like_definition(node_ref, |mut comp| match comp.compute_type(expr) {
            TypeContent::Unpacked(unpacked) => Some(TypeArgs::new(
                comp.use_tuple_unpack(unpacked, node_ref).into_tuple_args(),
            )),
            _ => None,
        })
    }

    pub fn compute_new_type_constraint(&self, expr: Expression) -> Type {
        let mut x = type_computation_for_variable_annotation;
        let node_ref = NodeRef::new(self.file, expr.index());
        let mut comp = TypeComputation::new(
            self.i_s,
            self.file,
            node_ref.as_link(),
            &mut x,
            TypeComputationOrigin::Other,
        );
        match comp.compute_type(expr) {
            TypeContent::InvalidVariable(_) => {
                node_ref.add_issue(self.i_s, IssueKind::NewTypeInvalidType);
                Type::ERROR
            }
            t => {
                let t = comp.as_type(t, node_ref);
                if !t.is_subclassable(self.i_s.db) {
                    node_ref.add_issue(
                        self.i_s,
                        IssueKind::NewTypeMustBeSubclassable {
                            got: t.format_short(self.i_s.db),
                        },
                    );
                }
                if t.maybe_class(self.i_s.db)
                    .is_some_and(|cls| cls.is_protocol(self.i_s.db))
                {
                    node_ref.add_issue(self.i_s, IssueKind::NewTypeCannotUseProtocols);
                }
                t
            }
        }
    }
}

type SeenRecursiveAliases<'a> = AlreadySeen<'a, PointLink>;

fn is_invalid_recursive_alias(db: &Database, seen: &SeenRecursiveAliases, t: &Type) -> bool {
    t.iter_with_unpacked_unions_without_unpacking_recursive_types()
        .any(|t| {
            if let Type::RecursiveType(rec) = t {
                if rec.has_alias_origin(db) {
                    let new_seen = seen.append(rec.link);
                    return if rec.calculating(db) {
                        new_seen.is_cycle()
                    } else {
                        is_invalid_recursive_alias(db, &new_seen, rec.calculated_type(db))
                    };
                }
            }
            false
        })
}

fn detect_diverging_alias(db: &Database, type_var_likes: &TypeVarLikes, t: &Type) -> bool {
    !type_var_likes.is_empty()
        && t.find_in_type(db, &mut |t| match t {
            Type::RecursiveType(rec) if rec.has_alias_origin(db) && rec.generics.is_some() => {
                if rec.calculating(db) {
                    rec.generics.as_ref().is_some_and(|generics| {
                        let has_direct_type_var_like = generics.iter().any(|g| match g {
                            GenericItem::TypeArg(t) => matches!(t, Type::TypeVar(_)),
                            GenericItem::TypeArgs(ts) => match &ts.args {
                                TupleArgs::WithUnpack(w) => {
                                    matches!(w.unpack, TupleUnpack::TypeVarTuple(_))
                                }
                                _ => false,
                            },
                            GenericItem::ParamSpecArg(p) => p.params.maybe_param_spec().is_some(),
                        });
                        !has_direct_type_var_like && generics.has_type_vars()
                    })
                } else {
                    false
                }
            }
            _ => false,
        })
}

fn check_for_and_replace_type_type_in_finished_alias(
    i_s: &InferenceState,
    alias_origin: NodeRef,
    alias: &TypeAlias,
) {
    // TODO this is not complete now. This only properly checks aliases that are self-recursive.
    // Something like:
    //
    //     A = Type[B]
    //     B = List[Type[A]]
    //
    //  will probably just be ignored and should need additional logic to be recognized.
    //  see also the test type_type_alias_circular
    if alias
        .type_if_valid()
        .find_in_type(i_s.db, &mut |t| match t {
            Type::Type(t) => t
                .iter_with_unpacked_unions_without_unpacking_recursive_types()
                .any(|t| match t {
                    Type::RecursiveType(recursive_alias) => {
                        !recursive_alias.calculating(i_s.db)
                            && recursive_alias.has_alias_origin(i_s.db)
                            && recursive_alias
                                .calculated_type(i_s.db)
                                .iter_with_unpacked_unions_without_unpacking_recursive_types()
                                .any(|t| matches!(t, Type::Type(_)))
                    }
                    _ => false,
                }),
            _ => false,
        })
    {
        alias_origin.add_issue(i_s, IssueKind::CannotContainType { name: "Type" });
        let alias = TypeAlias::new(alias.type_vars.clone(), alias.location, alias.name);
        alias.set_valid(Type::ERROR, false);
        save_alias(alias_origin, alias)
    }
}

fn save_alias(alias_origin: NodeRef, alias: TypeAlias) {
    let complex = ComplexPoint::TypeAlias(Box::new(alias));
    alias_origin.insert_complex(complex, Locality::Todo);
}

#[derive(Debug)]
enum TypeCompTupleUnpack {
    TypeVarTuple(TypeVarTupleUsage),
    ArbitraryLen(Box<Type>),
    FixedLen(Vec<Type>),
    WithUnpack(WithUnpack),
}

impl TypeCompTupleUnpack {
    fn into_tuple_args(self) -> TupleArgs {
        match self {
            Self::TypeVarTuple(tvt) => TupleArgs::WithUnpack(WithUnpack {
                before: Rc::from([]),
                unpack: TupleUnpack::TypeVarTuple(tvt),
                after: Rc::from([]),
            }),
            Self::ArbitraryLen(t) => TupleArgs::ArbitraryLen(t),
            Self::FixedLen(ts) => TupleArgs::FixedLen(ts.into()),
            Self::WithUnpack(with_unpack) => TupleArgs::WithUnpack(with_unpack),
        }
    }
}

enum TuplePart {
    Type(Type),
    TupleUnpack(TypeCompTupleUnpack),
}

struct TypeArgIterator<'a, I> {
    slices: I,
    current_unpack: Option<(NodeRef<'a>, TypeCompTupleUnpack)>,
    current_unpack_reverse: Option<TypeCompTupleUnpack>,
    reverse_already_analyzed: Option<NodeRef<'a>>,
}

impl<'a, I: Clone + Iterator<Item = SliceOrSimple<'a>>> TypeArgIterator<'a, I> {
    fn new(slices: I) -> Self {
        Self {
            slices,
            current_unpack: None,
            current_unpack_reverse: None,
            reverse_already_analyzed: None,
        }
    }

    fn next_type_argument(
        &mut self,
        type_computation: &mut TypeComputation,
        has_type_var_tuple: bool,
    ) -> Option<(NodeRef<'a>, Type)> {
        if let Some((from, unpack)) = self.current_unpack.as_mut() {
            let cannot_split_type_var_tuple = || {
                type_computation.add_issue(*from, IssueKind::TypeVarTupleCannotBeSplit);
                Some((*from, Type::ERROR))
            };
            match unpack {
                TypeCompTupleUnpack::TypeVarTuple(_) => return cannot_split_type_var_tuple(),
                TypeCompTupleUnpack::ArbitraryLen(t) => return Some((*from, (**t).clone())),
                TypeCompTupleUnpack::WithUnpack(with_unpack) => {
                    let mut iterator = with_unpack.before.iter();
                    if let Some(first) = iterator.next() {
                        let new_with_unpack = WithUnpack {
                            before: iterator.cloned().collect(),
                            unpack: with_unpack.unpack.clone(),
                            after: with_unpack.after.clone(),
                        };
                        let first = first.clone();
                        let from = *from;
                        self.current_unpack =
                            Some((from, TypeCompTupleUnpack::WithUnpack(new_with_unpack)));
                        return Some((from, first));
                    } else {
                        return cannot_split_type_var_tuple();
                    }
                }
                TypeCompTupleUnpack::FixedLen(ts) => {
                    if !ts.is_empty() {
                        return Some((*from, ts.remove(0)));
                    } else {
                        self.current_unpack = None;
                    }
                }
            }
        }
        let s = self.slices.next()?;
        let t = type_computation.compute_slice_type_content(s);
        match type_computation.convert_slice_type_or_tuple_unpack(t, s.as_node_ref()) {
            TuplePart::Type(t) => Some((s.as_node_ref(), t)),
            TuplePart::TupleUnpack(u) => {
                debug_assert!(self.current_unpack.is_none());
                if !has_type_var_tuple && !matches!(u, TypeCompTupleUnpack::FixedLen(_)) {
                    type_computation.add_issue(
                        s.as_node_ref(),
                        IssueKind::UnpackOnlyValidInVariadicPosition,
                    );
                    self.current_unpack = None;
                    return Some((s.as_node_ref(), Type::ERROR));
                }
                self.current_unpack = Some((s.as_node_ref(), u));
                self.next_type_argument(type_computation, has_type_var_tuple)
            }
        }
    }

    fn next_type_argument_back(
        &mut self,
        type_computation: &mut TypeComputation,
    ) -> Option<(NodeRef<'a>, Type)> {
        let (from, result) = self.next_back(type_computation)?;
        match result {
            Ok(t) => Some((from, t)),
            Err(s) => {
                let t = type_computation.compute_slice_type_content(s);
                match type_computation.convert_slice_type_or_tuple_unpack(t, from) {
                    TuplePart::Type(t) => Some((from, t)),
                    TuplePart::TupleUnpack(u) => {
                        self.current_unpack_reverse = Some(u);
                        self.next_type_argument_back(type_computation)
                    }
                }
            }
        }
    }

    fn next_back(
        &mut self,
        type_computation: &mut TypeComputation,
    ) -> Option<(NodeRef<'a>, Result<Type, SliceOrSimple>)> {
        let cannot_split_type_var_tuple = |from: NodeRef| {
            type_computation.add_issue(from, IssueKind::TypeVarTupleCannotBeSplit);
            Type::ERROR
        };

        let remove_next_back_from_with_unpack =
            |from: NodeRef, overwrite: &mut _, with_unpack: WithUnpack| {
                let mut iterator = with_unpack.after.iter();
                if let Some(last) = iterator.next_back() {
                    let new_with_unpack = WithUnpack {
                        before: with_unpack.before.clone(),
                        unpack: with_unpack.unpack.clone(),
                        after: iterator.cloned().collect(),
                    };
                    let last = last.clone();
                    *overwrite = TypeCompTupleUnpack::WithUnpack(new_with_unpack);
                    last
                } else {
                    match with_unpack.unpack {
                        TupleUnpack::TypeVarTuple(_) => cannot_split_type_var_tuple(from),
                        TupleUnpack::ArbitraryLen(t) => t,
                    }
                }
            };

        if let Some(unpack) = self.current_unpack_reverse.as_mut() {
            let from = self.reverse_already_analyzed.unwrap();
            match unpack {
                TypeCompTupleUnpack::TypeVarTuple(_) => {
                    return Some((from, Ok(cannot_split_type_var_tuple(from))))
                }
                TypeCompTupleUnpack::WithUnpack(with_unpack) => {
                    let with_unpack = with_unpack.clone();
                    return Some((
                        from,
                        Ok(remove_next_back_from_with_unpack(from, unpack, with_unpack)),
                    ));
                }
                TypeCompTupleUnpack::FixedLen(ts) => {
                    if let Some(result) = ts.pop() {
                        return Some((from, Ok(result)));
                    } else {
                        self.current_unpack_reverse = None;
                    }
                }
                TypeCompTupleUnpack::ArbitraryLen(t) => return Some((from, Ok((**t).clone()))),
            }
        }
        let mut current = None;
        // slices are not reversible, becuase of how the CST is structured. This is not used often,
        // just clone the iterator.
        for s in self.slices.clone() {
            if let Some(already_analyzed) = self.reverse_already_analyzed {
                if s.as_node_ref() == already_analyzed {
                    break;
                }
            }
            current = Some(s);
        }
        let Some(current_slice_part) = current else {
            if let Some((from, unpack)) = self.current_unpack.as_mut() {
                match unpack {
                    TypeCompTupleUnpack::TypeVarTuple(_) => {
                        return Some((*from, Ok(cannot_split_type_var_tuple(*from))))
                    }
                    TypeCompTupleUnpack::WithUnpack(with_unpack) => {
                        let with_unpack = with_unpack.clone();
                        return Some((
                            *from,
                            Ok(remove_next_back_from_with_unpack(
                                *from,
                                unpack,
                                with_unpack,
                            )),
                        ));
                    }
                    TypeCompTupleUnpack::FixedLen(ts) => {
                        if let Some(result) = ts.pop() {
                            return Some((*from, Ok(result)));
                        } else {
                            self.current_unpack = None;
                        }
                    }
                    TypeCompTupleUnpack::ArbitraryLen(t) => {
                        return Some((*from, Ok((**t).clone())))
                    }
                }
            }
            return None;
        };
        let from = current_slice_part.as_node_ref();
        self.reverse_already_analyzed = Some(from);
        Some((from, Err(current_slice_part)))
    }

    fn next_param_spec(
        &mut self,
        type_computation: &mut TypeComputation,
        allow_aesthetic_class_simplification: bool,
    ) -> Option<ParamSpecArg> {
        let params = type_computation.calculate_callable_params(
            self.slices.next()?,
            true,
            allow_aesthetic_class_simplification,
        );
        Some(ParamSpecArg::new(params, None))
    }

    fn next_param_spec_back(
        &mut self,
        type_computation: &mut TypeComputation,
    ) -> Option<ParamSpecArg> {
        let (_, result) = self.next_back(type_computation)?;
        let slice = result.err()?;
        let params = type_computation.calculate_callable_params(slice, true, false);
        Some(ParamSpecArg::new(params, None))
    }

    fn as_type_arguments(
        &mut self,
        type_computation: &mut TypeComputation,
        allow_empty_tuple: bool,
    ) -> TupleArgsDetails {
        let mut gatherer = MaybeUnpackGatherer::default();

        let empty_not_explicit = Cell::new(true);
        let add_unpack = |type_computation: &mut TypeComputation,
                          from,
                          u,
                          gatherer: &mut MaybeUnpackGatherer| {
            let maybe_err = match u {
                TypeCompTupleUnpack::TypeVarTuple(tvt) => {
                    gatherer.add_unpack(TupleUnpack::TypeVarTuple(tvt))
                }
                TypeCompTupleUnpack::ArbitraryLen(t) => {
                    gatherer.add_unpack(TupleUnpack::ArbitraryLen(*t))
                }
                TypeCompTupleUnpack::WithUnpack(with_unpack) => {
                    gatherer.add_with_unpack(with_unpack)
                }
                TypeCompTupleUnpack::FixedLen(ts) => {
                    gatherer.add_types(ts.into_iter());
                    return;
                }
            };
            if maybe_err.is_err() {
                type_computation.add_issue(from, IssueKind::MoreThanOneUnpackTypeIsNotAllowed)
            }
            empty_not_explicit.set(false);
        };
        if let Some((from, current_unpack)) = self.current_unpack.take() {
            add_unpack(type_computation, from, current_unpack, &mut gatherer)
        }
        for s in self.slices.by_ref() {
            empty_not_explicit.set(false);
            if let Some(already_analyzed) = self.reverse_already_analyzed {
                if already_analyzed == s.as_node_ref() {
                    break;
                }
            }
            let t = type_computation.compute_slice_type_content(s);
            if allow_empty_tuple
                && matches!(
                    t,
                    TypeContent::InvalidVariable(InvalidVariableType::Tuple { tuple_length: 0 })
                )
            {
                break;
            }
            match type_computation.convert_slice_type_or_tuple_unpack(t, s.as_node_ref()) {
                TuplePart::Type(t) => gatherer.add_type(t),
                TuplePart::TupleUnpack(u) => {
                    add_unpack(type_computation, s.as_node_ref(), u, &mut gatherer)
                }
            }
        }
        if let Some(u) = self.current_unpack_reverse.take() {
            add_unpack(
                type_computation,
                self.reverse_already_analyzed.unwrap(),
                u,
                &mut gatherer,
            )
        }
        TupleArgsDetails {
            empty_not_explicit: empty_not_explicit.get(),
            args: gatherer.into_tuple_args(),
        }
    }
}

enum CalculatingAliasType<'x> {
    Normal,
    TypedDict {
        primary_index: NodeIndex,
        details: ArgumentsDetails<'x>,
    },
    NamedTuple {
        primary_index: NodeIndex,
        details: ArgumentsDetails<'x>,
    },
}

pub(super) fn assignment_type_node_ref<'x>(
    file: &'x PythonFile,
    assignment: Assignment,
) -> NodeRef<'x> {
    NodeRef::new(file, assignment.index() + ASSIGNMENT_TYPE_CACHE_OFFSET)
}

#[inline]
fn check_special_case(specific: Specific) -> Option<TypeContent<'static, 'static>> {
    Some(TypeContent::SpecialType(match specific {
        Specific::TypingGeneric => SpecialType::Generic,
        Specific::TypingProtocol => SpecialType::Protocol,
        Specific::BuiltinsType => SpecialType::BuiltinsType,
        Specific::TypingType => SpecialType::TypingType,
        Specific::TypingCallable => SpecialType::Callable,
        Specific::TypingLiteralString => SpecialType::LiteralString,
        Specific::TypingUnpack => SpecialType::Unpack,
        Specific::TypingConcatenateClass => SpecialType::Concatenate,
        Specific::TypingLiteral => SpecialType::Literal,
        Specific::TypingTuple => SpecialType::Tuple,
        Specific::TypingRequired => {
            return Some(TypeContent::TypedDictFieldModifier(
                TypedDictFieldModifier::Required,
            ))
        }
        Specific::TypingNotRequired => {
            return Some(TypeContent::TypedDictFieldModifier(
                TypedDictFieldModifier::NotRequired,
            ))
        }
        Specific::TypingReadOnly => {
            return Some(TypeContent::TypedDictFieldModifier(
                TypedDictFieldModifier::ReadOnly,
            ))
        }
        Specific::AnyDueToError
        | Specific::ModuleNotFound
        | Specific::AnnotationOrTypeCommentSimpleClassInstance
        | Specific::AnnotationOrTypeCommentWithTypeVars
        | Specific::AnnotationOrTypeCommentWithoutTypeVars
        | Specific::TypingTypeVarClass
        | Specific::TypingTypeVarTupleClass
        | Specific::TypingParamSpecClass => return None,
        _ => return Some(TypeContent::SpecialCase(specific)),
    }))
}

fn load_cached_type(node_ref: NodeRef) -> Lookup {
    match node_ref.complex().unwrap() {
        ComplexPoint::TypeAlias(a) => {
            if a.calculating() {
                // This means it's a recursive type definition.
                Lookup::T(TypeContent::RecursiveAlias(node_ref.as_link()))
            } else if !a.is_valid() {
                let assignment = NodeRef::new(
                    node_ref.file,
                    node_ref.node_index - ASSIGNMENT_TYPE_CACHE_OFFSET,
                )
                .expect_assignment();
                let name_def = assignment
                    .maybe_simple_type_expression_assignment()
                    .unwrap()
                    .0;
                debug!("Found invalid type alias: {}", name_def.as_code());
                Lookup::T(TypeContent::InvalidVariable(InvalidVariableType::Variable(
                    NodeRef::new(node_ref.file, name_def.index()),
                )))
            } else {
                Lookup::T(TypeContent::TypeAlias(a))
            }
        }
        ComplexPoint::TypeVarLike(t) => Lookup::TypeVarLike(t.clone()),
        _ => unreachable!("Expected an Alias or TypeVarLike, but received something weird"),
    }
}

pub fn use_cached_simple_generic_type<'db>(
    db: &'db Database,
    file: &PythonFile,
    expr: Expression,
) -> Cow<'db, Type> {
    debug_assert_eq!(file.points.get(expr.index()).kind(), PointKind::Redirect);
    expect_class_or_simple_generic(db, NodeRef::new(file, expr.index()))
}

fn expect_class_or_simple_generic(db: &Database, node_ref: NodeRef) -> Cow<'static, Type> {
    fn inner(db: &Database, node_ref: NodeRef) -> GenericClass {
        let p = node_ref.point();
        debug_assert!(p.calculated(), "{node_ref:?}");
        match p.kind() {
            PointKind::Specific => {
                debug_assert_eq!(p.specific(), Specific::SimpleGeneric);
                let primary = node_ref.as_primary();
                let first_cls = inner(db, NodeRef::new(node_ref.file, primary.first_child_index()));
                debug_assert_eq!(first_cls.generics, ClassGenerics::None);
                let link = first_cls.link;

                let PrimaryContent::GetItem(slice_type) = primary.second() else {
                    unreachable!();
                };
                let generics = match slice_type {
                    CSTSliceType::NamedExpression(named) => ClassGenerics::ExpressionWithClassType(
                        PointLink::new(node_ref.file_index(), named.expression().index()),
                    ),
                    CSTSliceType::Slice(_) | CSTSliceType::StarredExpression(_) => unreachable!(),
                    CSTSliceType::Slices(slices) => ClassGenerics::SlicesWithClassTypes(
                        PointLink::new(node_ref.file_index(), slices.index()),
                    ),
                };
                GenericClass { link, generics }
            }
            PointKind::Complex => GenericClass {
                link: node_ref.as_link(),
                generics: ClassGenerics::None,
            },
            PointKind::Redirect => inner(db, p.as_redirected_node_ref(db)),
            PointKind::FileReference => unreachable!("Simple class should never be a file"),
        }
    }
    Cow::Owned(Type::Class(inner(db, node_ref)))
}

pub fn use_cached_param_annotation_type<'db: 'file, 'file>(
    db: &'db Database,
    file: &'file PythonFile,
    annotation: ParamAnnotation,
) -> Cow<'file, Type> {
    file.name_resolution_for_types(&InferenceState::new(db))
        .use_cached_param_annotation_type(annotation)
}

pub fn use_cached_annotation_type<'db: 'file, 'file>(
    db: &'db Database,
    file: &'file PythonFile,
    annotation: Annotation,
) -> Cow<'file, Type> {
    file.name_resolution_for_types(&InferenceState::new(db))
        .use_cached_annotation_or_type_comment_type_internal(
            annotation.index(),
            annotation.expression(),
        )
}

pub fn use_cached_annotation_or_type_comment<'db: 'file, 'file>(
    i_s: &InferenceState<'db, '_>,
    definition: NodeRef<'file>,
) -> Cow<'file, Type> {
    debug_assert!(matches!(
        definition.point().specific(),
        Specific::AnnotationOrTypeCommentSimpleClassInstance
            | Specific::AnnotationOrTypeCommentWithoutTypeVars
            | Specific::AnnotationOrTypeCommentWithTypeVars
            | Specific::AnnotationOrTypeCommentClassVar
            | Specific::AnnotationOrTypeCommentFinal
    ));
    let n = definition.add_to_node_index(ANNOTATION_TO_EXPR_DIFFERENCE as i64);
    let maybe_starred = match n.maybe_expression() {
        Some(expr) => Err(expr),
        None => Ok(n.as_star_expression()),
    };
    definition
        .file
        .name_resolution_for_types(i_s)
        .use_cached_maybe_starred_annotation_type_internal(definition.node_index, maybe_starred)
}

pub fn maybe_saved_annotation(node_ref: NodeRef) -> Option<&Type> {
    if matches!(
        node_ref.point().maybe_specific(),
        Some(
            Specific::AnnotationOrTypeCommentWithTypeVars
                | Specific::AnnotationOrTypeCommentWithoutTypeVars
                | Specific::AnnotationOrTypeCommentClassVar
                | Specific::AnnotationOrTypeCommentFinal
        )
    ) {
        let Some(ComplexPoint::TypeInstance(t)) = node_ref
            .add_to_node_index(ANNOTATION_TO_EXPR_DIFFERENCE as i64)
            .complex()
        else {
            unreachable!()
        };
        return Some(t);
    }
    None
}

struct TupleArgsDetails {
    args: TupleArgs,
    empty_not_explicit: bool, // Explicit would be something like Unpack[Tuple[()]]
}

pub enum TypeCommentState<'db> {
    Type(Cow<'db, Type>),
    UnfinishedFinalOrClassVar(NodeRef<'db>),
}

pub struct TypeCommentDetails<'db> {
    pub type_: TypeCommentState<'db>,
    pub inferred: Inferred,
}

impl TypeCommentDetails<'_> {
    fn new_any() -> Self {
        Self {
            inferred: Inferred::new_any_from_error(),
            type_: TypeCommentState::Type(Cow::Borrowed(&Type::ERROR)),
        }
    }
}

#[derive(Debug, Clone)]
pub struct GenericCounts {
    pub expected: usize,
    pub expected_minimum: Option<usize>,
    pub given: usize,
    pub at_least_expected: bool,
}
