use std::{borrow::Cow, rc::Rc};

use parsa_python_ast::{SliceType as ASTSliceType, *};

use super::TypeVarFinder;
use crate::{
    arguments::SimpleArguments,
    database::{
        ComplexPoint, Database, Locality, Point, PointLink, PointType, Specific, TypeAlias,
    },
    debug,
    diagnostics::{Issue, IssueType},
    file::{File, Inference, PythonFile},
    getitem::{SliceOrSimple, SliceType, SliceTypeIterator},
    imports::{python_import, ImportResult},
    inference_state::InferenceState,
    inferred::Inferred,
    matching::{FormatData, Generics, ResultContext},
    new_class,
    node_ref::NodeRef,
    type_::{
        new_collections_named_tuple, new_typing_named_tuple, AnyCause, CallableContent,
        CallableParam, CallableParams, CallableWithParent, ClassGenerics, Dataclass, DbString,
        Enum, EnumMember, FunctionKind, GenericClass, GenericItem, GenericsList, Literal,
        LiteralKind, NamedTuple, Namespace, NewType, ParamSpecArgument, ParamSpecUsage, ParamType,
        RecursiveType, StarParamType, StarStarParamType, StringSlice, Tuple, TupleTypeArguments,
        TupleUnpack, Type, TypeArguments, TypeVar, TypeVarKind, TypeVarLike, TypeVarLikeUsage,
        TypeVarLikes, TypeVarManager, TypeVarTupleUsage, TypeVarUsage, TypedDict,
        TypedDictGenerics, TypedDictMember, UnionEntry, UnionType, WithUnpack,
    },
    type_helpers::{start_namedtuple_params, Class, Function, Module},
};

const ASSIGNMENT_TYPE_CACHE_OFFSET: u32 = 1;
const ANNOTATION_TO_EXPR_DIFFERENCE: u32 = 2;

#[derive(Debug)]
pub enum TypeVarCallbackReturn {
    TypeVarLike(TypeVarLikeUsage<'static>),
    UnboundTypeVar,
    NotFound,
}

type MapAnnotationTypeCallback<'a> =
    Option<&'a dyn Fn(&mut TypeComputation, TypeContent) -> AnnotationReturn>;

enum AnnotationReturn {
    Type(Type),
    UnpackType(Type),
}

type TypeVarCallback<'db, 'x> = &'x mut dyn FnMut(
    &InferenceState<'db, '_>,
    &TypeVarManager,
    TypeVarLike,
    Option<PointLink>, // current_callable
) -> TypeVarCallbackReturn;

#[derive(Debug, Clone)]
pub(super) enum SpecialType {
    Union,
    Optional,
    Any,
    Protocol,
    ProtocolWithGenerics,
    Generic,
    GenericWithGenerics,
    TypingNamedTuple,
    TypingTypedDict,
    Required,
    NotRequired,
    CollectionsNamedTuple,
    Callable,
    Type,
    Tuple,
    Literal,
    LiteralString,
    Unpack,
    Concatenate,
    TypeAlias,
    Self_,
    Final,
    Annotated,
    ClassVar,
    MypyExtensionsParamType(Specific),
    CallableParam(CallableParam),
}

#[derive(Debug, Clone)]
pub(super) enum InvalidVariableType<'a> {
    List,
    Tuple { tuple_length: usize },
    Execution { was_class: bool },
    Function(Function<'a, 'a>),
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
    AssignmentTypeCommentOrAnnotation { is_initialized: bool },
    ParamTypeCommentOrAnnotation,
    TypedDictMember,
    TypeApplication,
    TypeAlias,
    CastTarget,
    Constraint,
    NamedTupleMember,
    BaseClass,
}

impl InvalidVariableType<'_> {
    fn add_issue(
        &self,
        db: &Database,
        add_issue: impl Fn(IssueType),
        origin: TypeComputationOrigin,
    ) {
        add_issue(match self {
            Self::Variable(var_ref) | Self::ParamNameAsBaseClassAny(var_ref) => {
                add_issue(IssueType::InvalidType(
                    format!(
                        "Variable \"{}.{}\" is not valid as a type",
                        var_ref.in_module().qualified_name(db),
                        var_ref.as_code().to_owned(),
                    )
                    .into(),
                ));
                IssueType::Note(
                    Box::from("See https://mypy.readthedocs.io/en/stable/common_issues.html#variables-vs-type-aliases"),
                )
            }
            Self::Function(func) => {
                add_issue(IssueType::InvalidType(
                    format!(
                        "Function {:?} is not valid as a type",
                        func.qualified_name(db),
                    )
                    .into(),
                ));
                IssueType::Note(Box::from(match func.name() {
                    "any" => "Perhaps you meant \"typing.Any\" instead of \"any\"?",
                    "callable" => "Perhaps you meant \"typing.Callable\" instead of \"callable\"?",
                    _ => "Perhaps you need \"Callable[...]\" or a callback protocol?",
                }))
            }
            Self::List => {
                add_issue(IssueType::InvalidType(Box::from(
                    "Bracketed expression \"[...]\" is not valid as a type",
                )));
                IssueType::Note(Box::from("Did you mean \"List[...]\"?"))
            }
            Self::Tuple { tuple_length } => {
                add_issue(IssueType::InvalidType(Box::from(
                    "Syntax error in type annotation",
                )));
                if *tuple_length == 1 {
                    IssueType::Note(Box::from("Suggestion: Is there a spurious trailing comma?"))
                } else {
                    IssueType::Note(Box::from(
                        "Suggestion: Use Tuple[T1, ..., Tn] instead of (T1, ..., Tn)",
                    ))
                }
            }
            Self::Literal(s) => IssueType::InvalidType(
                format!("Invalid type: try using Literal[{s}] instead?").into(),
            ),
            Self::Execution { .. } | Self::Other if origin == TypeComputationOrigin::CastTarget => {
                IssueType::InvalidCastTarget
            }
            Self::Execution { .. } | Self::Other if origin == TypeComputationOrigin::TypeAlias => {
                IssueType::InvalidType(Box::from(
                    "Invalid type alias: expression is not a valid type",
                ))
            }
            Self::Execution { was_class: true } => {
                add_issue(IssueType::InvalidType(Box::from(
                    "Invalid type comment or annotation",
                )));
                IssueType::Note(Box::from("Suggestion: use Foo[...] instead of Foo(...)"))
            }
            Self::Execution { .. } | Self::Other => {
                IssueType::InvalidType(Box::from(if origin == TypeComputationOrigin::BaseClass {
                    "Type expected within [...]"
                } else {
                    "Invalid type comment or annotation"
                }))
            }
            Self::InlineTypedDict => IssueType::InvalidType(Box::from(
                "Inline TypedDict types not supported; use assignment to define TypedDict",
            )),
            Self::Slice => {
                add_issue(IssueType::InvalidType(Box::from(
                    "Invalid type comment or annotation",
                )));
                IssueType::Note(Box::from("did you mean to use ',' instead of ':' ?"))
            }
            Self::Float => IssueType::InvalidType(
                "Invalid type: float literals cannot be used as a type".into(),
            ),
            Self::Complex => IssueType::InvalidType(
                "Invalid type: complex literals cannot be used as a type".into(),
            ),
            Self::Ellipsis => IssueType::InvalidType("Unexpected \"...\"".into()),
        })
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeOrUnpack {
    Type(Type),
    TypeVarTuple(TypeVarTupleUsage),
}

#[derive(Debug, Clone)]
enum TypeContent<'db, 'a> {
    Module(&'db PythonFile),
    Namespace(Rc<Namespace>),
    Class {
        node_ref: NodeRef<'db>,
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
    RecursiveAlias(PointLink),
    RecursiveClass(NodeRef<'db>),
    InvalidVariable(InvalidVariableType<'a>),
    TypeVarTuple(TypeVarTupleUsage),
    ParamSpec(ParamSpecUsage),
    Unpacked(TypeOrUnpack),
    Concatenate(CallableParams),
    ClassVar(Type),
    EnumMember(EnumMember),
    Required(Type),
    Final(Type),
    NotRequired(Type),
    Unknown(AnyCause),
}

enum ClassGetItemResult<'db> {
    GenericClass(GenericClass),
    SimpleGeneric {
        node_ref: NodeRef<'db>,
        class_link: PointLink,
        generics: ClassGenerics,
    },
}

#[derive(Debug)]
pub(super) enum TypeNameLookup<'db, 'a> {
    Module(&'db PythonFile),
    Namespace(Rc<Namespace>),
    Class { node_ref: NodeRef<'db> },
    TypeVarLike(TypeVarLike),
    TypeAlias(&'db TypeAlias),
    NewType(Rc<NewType>),
    SpecialType(SpecialType),
    InvalidVariable(InvalidVariableType<'a>),
    NamedTupleDefinition(Rc<NamedTuple>),
    TypedDictDefinition(Rc<TypedDict>),
    Enum(Rc<Enum>),
    Dataclass(Rc<Dataclass>),
    RecursiveAlias(PointLink),
    RecursiveClass(NodeRef<'db>),
    Unknown(AnyCause),
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
        let mut on_type_var = |i_s: &InferenceState, _: &_, type_var_like: TypeVarLike, _| {
            if let Some(class) = i_s.current_class() {
                if let Some(usage) = class
                    .type_vars(i_s)
                    .find(type_var_like.clone(), class.node_ref.as_link())
                {
                    if $from_alias_definition {
                        $slice_type.as_node_ref().add_issue(
                            i_s,
                            IssueType::BoundTypeVarInAlias{
                                name: Box::from(type_var_like.name(i_s.db))
                            },
                        );
                    } else {
                        return TypeVarCallbackReturn::TypeVarLike(usage)
                    }
                }
            }
            if let Some(function) = i_s.current_function() {
                if let Some(usage) = function
                    .type_vars(i_s)
                    .find(type_var_like.clone(), function.node_ref.as_link())
                {
                    if $from_alias_definition {
                        $slice_type.as_node_ref().add_issue(
                            i_s,
                            IssueType::BoundTypeVarInAlias{
                                name: Box::from(type_var_like.name(i_s.db))
                            },
                        );
                    } else {
                        return TypeVarCallbackReturn::TypeVarLike(usage)
                    }
                }
            }
            if $from_alias_definition {
                TypeVarCallbackReturn::NotFound
            } else {
                TypeVarCallbackReturn::UnboundTypeVar
            }
        };
        let mut tcomp = TypeComputation::new(
            $self,
            $slice_type.as_node_ref().as_link(),
            &mut on_type_var,
            match $from_alias_definition {
                false => TypeComputationOrigin::TypeApplication,
                true => TypeComputationOrigin::TypeAlias,
            }
        );
        let t = tcomp.$method $args;
        match t {
            TypeContent::Class{node_ref, ..} => {
                todo!("Type application issue")
            }
            TypeContent::SimpleGeneric{class_link, generics, ..} => {
                Inferred::from_type(Type::Type(Rc::new(Type::new_class(class_link, generics))))
            }
            TypeContent::Type(mut type_) => {
                let type_var_likes = tcomp.into_type_vars(|inf, recalculate_type_vars| {
                    type_ = recalculate_type_vars(&type_);
                });
                if type_var_likes.len() > 0 {
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
            TypeContent::Unknown(cause) => Inferred::new_any(cause),
            _ => todo!("type application: {t:?}"),
        }
    }}
}

fn type_computation_for_variable_annotation(
    i_s: &InferenceState,
    manager: &TypeVarManager,
    type_var_like: TypeVarLike,
    current_callable: Option<PointLink>,
) -> TypeVarCallbackReturn {
    if let Some(class) = i_s.current_class() {
        if let Some(usage) = class
            .type_vars(i_s)
            .find(type_var_like.clone(), class.node_ref.as_link())
        {
            return TypeVarCallbackReturn::TypeVarLike(usage);
        }
    }
    if let Some(func) = i_s.current_function() {
        let usage = func
            .type_vars(i_s)
            .find(type_var_like, func.node_ref.as_link());
        if let Some(usage) = usage {
            return TypeVarCallbackReturn::TypeVarLike(usage);
        }
    }
    match current_callable {
        Some(_) => TypeVarCallbackReturn::NotFound,
        None => TypeVarCallbackReturn::UnboundTypeVar,
    }
}

pub struct TypeComputation<'db, 'file, 'i_s, 'c> {
    inference: &'c mut Inference<'db, 'file, 'i_s>,
    for_definition: PointLink,
    current_callable: Option<PointLink>,
    type_var_manager: TypeVarManager,
    type_var_callback: TypeVarCallback<'db, 'c>,
    // This is only for type aliases. Type aliases are also allowed to be used by Python itself.
    // It's therefore unclear if type inference or type computation is needed. So once we encounter
    // a type alias we check in the database if the error was already calculated and set the flag.
    errors_already_calculated: bool,
    pub has_type_vars_or_self: bool,
    origin: TypeComputationOrigin,
    is_recursive_alias: bool,
}

impl<'db: 'x + 'file, 'file, 'i_s, 'c, 'x> TypeComputation<'db, 'file, 'i_s, 'c> {
    pub fn new(
        inference: &'c mut Inference<'db, 'file, 'i_s>,
        for_definition: PointLink,
        type_var_callback: TypeVarCallback<'db, 'c>,
        origin: TypeComputationOrigin,
    ) -> Self {
        Self {
            inference,
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
        mut start: CodeIndex,
        mut string: Box<str>,
    ) -> TypeContent<'db, 'db> {
        let maybe_new = string.trim_start();
        let whitespace_in_beginning = string.len() - maybe_new.len();
        if whitespace_in_beginning > 0 {
            start += whitespace_in_beginning as CodeIndex;
            string = maybe_new.into()
        }
        let f: &'db PythonFile =
            self.inference
                .file
                .new_annotation_file(self.inference.i_s.db, start, string);
        if let Some(star_exprs) = f.tree.maybe_star_expressions() {
            let compute_type =
                |comp: &mut TypeComputation<'db, '_, '_, '_>| match star_exprs.unpack() {
                    StarExpressionContent::Expression(expr) => comp.compute_type(expr),
                    StarExpressionContent::Tuple(t) => todo!(),
                    StarExpressionContent::StarExpression(s) => todo!(),
                };
            let old_manager = std::mem::take(&mut self.type_var_manager);
            let mut comp = TypeComputation {
                inference: &mut f.inference(self.inference.i_s),
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
            for stmt_or_error in f.tree.root().iter_stmts() {
                if let StmtOrError::Error(node_index) = stmt_or_error {
                    // There is invalid syntax (issue added previously)
                    return TypeContent::Unknown(AnyCause::FromError);
                }
            }
            self.inference.file.add_issue(
                self.inference.i_s,
                Issue {
                    start_position: start,
                    end_position: start + f.tree.code().len() as CodeIndex,
                    type_: IssueType::InvalidSyntaxInTypeAnnotation,
                },
            );
            TypeContent::Unknown(AnyCause::FromError)
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
            TypeContent::SpecialType(SpecialType::TypingNamedTuple) => {
                CalculatedBaseClass::NewNamedTuple
            }
            TypeContent::SpecialType(SpecialType::TypingTypedDict) => {
                CalculatedBaseClass::TypedDict
            }
            TypeContent::SpecialType(SpecialType::Type) => {
                CalculatedBaseClass::Type(Type::new_class(
                    self.inference
                        .i_s
                        .db
                        .python_state
                        .bare_type_node_ref()
                        .as_link(),
                    ClassGenerics::None,
                ))
            }
            TypeContent::InvalidVariable(InvalidVariableType::ParamNameAsBaseClassAny(_)) => {
                // TODO what is this case?
                CalculatedBaseClass::Unknown
            }
            TypeContent::ParamSpec(_) | TypeContent::InvalidVariable(_) => {
                CalculatedBaseClass::Invalid
            }
            TypeContent::Type(Type::Enum(e)) => CalculatedBaseClass::InvalidEnum(e),
            _ => {
                let type_ =
                    self.as_type(calculated, NodeRef::new(self.inference.file, expr.index()));
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
                    self.inference
                        .i_s
                        .db
                        .python_state
                        .bare_type_node_ref()
                        .as_link(),
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
                self.add_issue_for_index(expr.index(), IssueType::CannotSubclassNewType);
                CalculatedBaseClass::Unknown
            }
            Type::RecursiveType(t) => self.compute_base_class_for_type(
                expr,
                t.calculated_type(self.inference.i_s.db).clone(),
            ),
            _ => CalculatedBaseClass::Invalid,
        }
    }

    pub fn compute_typed_dict_member(
        &mut self,
        name: StringSlice,
        expr: Expression,
        total: bool,
    ) -> TypedDictMember {
        let calculated = self.compute_type(expr);
        let (type_, required) = match calculated {
            TypeContent::Required(t) => (t, true),
            TypeContent::NotRequired(t) => (t, false),
            _ => (
                self.as_type(calculated, NodeRef::new(self.inference.file, expr.index())),
                total,
            ),
        };
        TypedDictMember {
            name,
            type_,
            required,
        }
    }

    pub fn cache_annotation(&mut self, annotation: Annotation, is_implicit_optional: bool) {
        let expr = annotation.expression();
        let from = NodeRef::new(self.inference.file, expr.index());
        match annotation.simple_param_kind() {
            Some(SimpleParamKind::Normal) | None => self.cache_annotation_or_type_comment(
                annotation.index(),
                expr,
                is_implicit_optional,
                None,
            ),
            Some(SimpleParamKind::Star) => self.cache_annotation_or_type_comment(
                annotation.index(),
                expr,
                false,
                Some(&|slf, t| slf.wrap_star(t, from)),
            ),
            Some(SimpleParamKind::StarStar) => self.cache_annotation_or_type_comment(
                annotation.index(),
                expr,
                false,
                Some(&|slf, t| slf.wrap_star_star(t, expr)),
            ),
        };
    }

    fn wrap_star(&mut self, tc: TypeContent, from: NodeRef) -> AnnotationReturn {
        match tc {
            TypeContent::Unpacked(TypeOrUnpack::Type(t @ Type::Tuple(_))) => {
                AnnotationReturn::UnpackType(t)
            }
            TypeContent::Unpacked(TypeOrUnpack::TypeVarTuple(_)) => todo!(),
            TypeContent::Unpacked(TypeOrUnpack::Type(t)) => {
                self.add_issue(
                    from,
                    IssueType::VariadicUnpackMustBeTupleLike {
                        actual: t.format_short(self.inference.i_s.db),
                    },
                );
                AnnotationReturn::Type(Type::Any(AnyCause::FromError))
            }
            _ => match self.as_type(tc, from) {
                // TODO is this AnnotationReturn really needed??
                t @ Type::ParamSpecArgs(_) => AnnotationReturn::Type(t),
                t => AnnotationReturn::Type(Type::Tuple(Rc::new(Tuple::new_arbitrary_length(t)))),
            },
        }
    }

    fn wrap_star_star(&mut self, tc: TypeContent, expr: Expression) -> AnnotationReturn {
        let from = NodeRef::new(self.inference.file, expr.index());
        match tc {
            TypeContent::Unpacked(TypeOrUnpack::Type(t @ Type::TypedDict(_))) => {
                AnnotationReturn::UnpackType(t)
            }
            TypeContent::Unpacked(_) => {
                self.add_issue(from, IssueType::UnpackItemInStarStarMustBeTypedDict);
                AnnotationReturn::Type(Type::Any(AnyCause::FromError))
            }
            _ => match self.as_type(tc, from) {
                t @ Type::ParamSpecKwargs(_) => AnnotationReturn::Type(t),
                t => AnnotationReturn::Type(new_class!(
                    self.inference.i_s.db.python_state.dict_node_ref().as_link(),
                    self.inference.i_s.db.python_state.str_type(),
                    t,
                )),
            },
        }
    }

    pub fn cache_return_annotation(&mut self, annotation: ReturnAnnotation) {
        self.cache_annotation_or_type_comment(
            annotation.index(),
            annotation.expression(),
            false,
            None,
        );
    }

    fn cache_annotation_or_type_comment(
        &mut self,
        annotation_index: NodeIndex,
        expr: Expression,
        is_implicit_optional: bool,
        map_type_callback: MapAnnotationTypeCallback,
    ) {
        let annotation_node_ref = NodeRef::new(self.inference.file, annotation_index);
        if annotation_node_ref.point().calculated() {
            return;
        }
        debug!(
            "Infer annotation expression class on {:?}: {:?}",
            self.inference.file.byte_to_line_column(expr.start()),
            expr.as_code()
        );

        let type_ = self.compute_type(expr);

        let node_ref = NodeRef::new(self.inference.file, expr.index());
        let mut is_class_var = false;
        let i_s = self.inference.i_s;
        let uses_class_generics = |class: &Class, t: &Type| {
            let mut uses_class_generics = false;
            t.search_type_vars(&mut |usage| {
                if usage.in_definition() == class.node_ref.as_link() {
                    uses_class_generics = true
                }
            });
            uses_class_generics
        };
        let mut type_ = match map_type_callback {
            Some(map_type_callback) => match map_type_callback(self, type_) {
                AnnotationReturn::Type(t) => t,
                AnnotationReturn::UnpackType(t) => t,
            },
            None => match type_ {
                TypeContent::SimpleGeneric { .. } | TypeContent::Class { .. }
                    if !is_implicit_optional =>
                {
                    debug_assert!(self.inference.file.points.get(expr.index()).calculated());
                    annotation_node_ref.set_point(Point::new_simple_specific(
                        Specific::AnnotationOrTypeCommentSimpleClassInstance,
                        Locality::Todo,
                    ));
                    return;
                }
                TypeContent::SpecialType(
                    special @ (SpecialType::TypeAlias | SpecialType::Final),
                ) if matches!(
                    self.origin,
                    TypeComputationOrigin::AssignmentTypeCommentOrAnnotation { .. }
                ) =>
                {
                    debug_assert!(!is_implicit_optional);
                    annotation_node_ref.set_point(Point::new_simple_specific(
                        match special {
                            SpecialType::TypeAlias => Specific::TypingTypeAlias,
                            SpecialType::Final => Specific::TypingFinal,
                            _ => unreachable!(),
                        },
                        Locality::Todo,
                    ));
                    return;
                }
                TypeContent::SpecialType(SpecialType::ClassVar) => {
                    if matches!(
                        self.origin,
                        TypeComputationOrigin::AssignmentTypeCommentOrAnnotation { .. }
                    ) && i_s.current_class().is_some()
                        && i_s.current_function().is_none()
                    {
                        todo!()
                    } else {
                        self.add_issue(node_ref, IssueType::ClassVarOnlyInAssignmentsInClass);
                        Type::Any(AnyCause::FromError)
                    }
                }
                TypeContent::ClassVar(t) => {
                    is_class_var = true;
                    if !matches!(
                        self.origin,
                        TypeComputationOrigin::AssignmentTypeCommentOrAnnotation { .. }
                    ) {
                        self.add_issue(node_ref, IssueType::ClassVarOnlyInAssignmentsInClass);
                        Type::Any(AnyCause::FromError)
                    } else if self.has_type_vars_or_self {
                        let i_s = self.inference.i_s;
                        let class = i_s.current_class().unwrap();
                        if uses_class_generics(class, &t) {
                            self.add_issue(node_ref, IssueType::ClassVarCannotContainTypeVariables);
                            Type::Any(AnyCause::FromError)
                        } else if !class.type_vars(i_s).is_empty() && t.has_self_type() {
                            self.add_issue(
                                node_ref,
                                IssueType::ClassVarCannotContainSelfTypeInGenericClass,
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
                    } = self.origin
                    {
                        if !is_initialized && !self.inference.file.is_stub(i_s.db) {
                            self.add_issue(
                                node_ref,
                                IssueType::FinalNameMustBeInitializedWithValue,
                            );
                        }
                        if i_s
                            .current_class()
                            .is_some_and(|class| uses_class_generics(class, &t))
                        {
                            self.add_issue(
                                node_ref,
                                IssueType::FinalInClassBodyCannotDependOnTypeVariables,
                            );
                            Type::Any(AnyCause::FromError)
                        } else {
                            t
                        }
                    } else {
                        self.as_type(TypeContent::Final(t), node_ref)
                    }
                }
                _ => self.as_type(type_, node_ref),
            },
        };
        if is_implicit_optional {
            type_.make_optional(i_s.db)
        }
        node_ref.insert_complex(ComplexPoint::TypeInstance(type_), Locality::Todo);
        annotation_node_ref.set_point(Point::new_simple_specific(
            if is_class_var {
                Specific::AnnotationOrTypeCommentClassVar
            } else if self.has_type_vars_or_self {
                Specific::AnnotationOrTypeCommentWithTypeVars
            } else {
                Specific::AnnotationOrTypeCommentWithoutTypeVars
            },
            Locality::Todo,
        ));
    }

    fn as_type(&mut self, type_: TypeContent, node_ref: NodeRef) -> Type {
        self.as_type_or_error(type_, node_ref)
            .unwrap_or(Type::Any(AnyCause::FromError))
    }

    fn as_type_or_error(&mut self, type_: TypeContent, node_ref: NodeRef) -> Option<Type> {
        let db = self.inference.i_s.db;
        match type_ {
            TypeContent::Class {
                node_ref: class_node_ref,
                ..
            } => {
                let cls = Class::with_undefined_generics(class_node_ref);
                if db.project.flags.disallow_any_generics
                    && !cls.type_vars(self.inference.i_s).is_empty()
                {
                    self.add_issue(
                        node_ref,
                        IssueType::MissingTypeParameters {
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
                            d.options,
                        )
                    }
                }));
            }
            TypeContent::NamedTuple(nt) => {
                return Some({
                    if nt.__new__.type_vars.is_empty() {
                        Type::NamedTuple(nt)
                    } else {
                        let defined_at = nt.__new__.defined_at;
                        Type::NamedTuple(nt).replace_type_var_likes(db, &mut |usage| {
                            if usage.in_definition() == defined_at {
                                usage.as_type_var_like().as_any_generic_item()
                            } else {
                                usage.into_generic_item()
                            }
                        })
                    }
                });
            }
            TypeContent::TypedDictDefinition(td) => {
                return match &td.generics {
                    TypedDictGenerics::None => Some(Type::TypedDict(td)),
                    TypedDictGenerics::NotDefinedYet(_) => {
                        if db.project.flags.disallow_any_generics {
                            self.add_issue(
                                node_ref,
                                IssueType::MissingTypeParameters {
                                    name: td.name.unwrap().as_str(db).into(),
                                },
                            );
                        }
                        Some(
                            Type::TypedDict(td).replace_type_var_likes(db, &mut |usage| {
                                usage.as_type_var_like().as_any_generic_item()
                            }),
                        )
                    }
                    TypedDictGenerics::Generics(_) => unreachable!(),
                }
            }
            TypeContent::Module(file) => {
                self.add_module_issue(node_ref, &Module::new(file).qualified_name(db));
            }
            TypeContent::Namespace(n) => {
                self.add_module_issue(node_ref, &n.qualified_name());
            }
            TypeContent::TypeAlias(a) => {
                if db.project.flags.disallow_any_generics && !a.type_vars.is_empty() {
                    self.add_issue(
                        node_ref,
                        IssueType::MissingTypeParameters {
                            name: a.name(db).unwrap().into(),
                        },
                    );
                }
                self.is_recursive_alias |= a.is_recursive();
                return Some(a.as_type_and_set_type_vars_any(db));
            }
            TypeContent::SpecialType(m) => match m {
                SpecialType::Callable => {
                    if db.project.flags.disallow_any_generics {
                        self.add_issue(
                            node_ref,
                            IssueType::MissingTypeParameters {
                                name: "Callable".into(),
                            },
                        );
                    }
                    return Some(Type::Callable(
                        self.inference
                            .i_s
                            .db
                            .python_state
                            .any_callable_from_error
                            .clone(),
                    ));
                }
                SpecialType::Any => return Some(Type::Any(AnyCause::Explicit)),
                SpecialType::Type => {
                    if db.project.flags.disallow_any_generics {
                        self.add_issue(
                            node_ref,
                            IssueType::MissingTypeParameters {
                                name: "Type".into(),
                            },
                        );
                    }
                    return Some(db.python_state.type_of_any.clone());
                }
                SpecialType::Tuple => {
                    if db.project.flags.disallow_any_generics {
                        self.add_issue(
                            node_ref,
                            IssueType::MissingTypeParameters {
                                name: "Tuple".into(),
                            },
                        );
                    }
                    return Some(Type::Tuple(Tuple::new_empty()));
                }
                SpecialType::TypingNamedTuple => {
                    return Some(db.python_state.typing_named_tuple_type())
                }
                SpecialType::ClassVar => {
                    self.add_issue(node_ref, IssueType::ClassVarNestedInsideOtherType);
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
                        IssueType::InvalidType(Box::from(
                            "Literal[...] must have at least one parameter",
                        )),
                    );
                }
                SpecialType::Self_ => self.add_issue(
                    node_ref,
                    match self.origin {
                        TypeComputationOrigin::TypedDictMember => {
                            IssueType::TypedDictSelfNotAllowed
                        }
                        TypeComputationOrigin::NamedTupleMember => {
                            IssueType::NamedTupleSelfNotAllowed
                        }
                        TypeComputationOrigin::TypeApplication
                        | TypeComputationOrigin::TypeAlias => IssueType::SelfTypeInTypeAliasTarget,
                        TypeComputationOrigin::Constraint | TypeComputationOrigin::BaseClass => {
                            IssueType::SelfTypeOutsideOfClass
                        }
                        _ => {
                            if let Some(class) = self.inference.i_s.current_class() {
                                if class.is_metaclass(db) {
                                    IssueType::SelfTypeInMetaclass
                                } else {
                                    self.has_type_vars_or_self = true;
                                    return Some(Type::Self_);
                                }
                            } else {
                                IssueType::SelfTypeOutsideOfClass
                            }
                        }
                    },
                ),
                SpecialType::Annotated => {
                    self.add_issue(
                        node_ref,
                        IssueType::InvalidType(Box::from(
                            "Annotated[...] must have exactly one type argument and at least one annotation",
                        )),
                    );
                }
                SpecialType::Optional => {
                    self.add_issue(node_ref, IssueType::OptionalMustHaveOneArgument);
                }
                SpecialType::Unpack => {
                    self.add_issue(node_ref, IssueType::UnpackRequiresExactlyOneArgument);
                }
                SpecialType::Final => self.add_issue(node_ref, IssueType::FinalInWrongPlace),
                _ => {
                    self.add_issue(node_ref, IssueType::InvalidType(Box::from("Invalid type")));
                }
            },
            TypeContent::TypeVarTuple(t) => todo!(),
            TypeContent::ParamSpec(p) => {
                self.add_issue(
                    node_ref,
                    IssueType::InvalidType(
                        format!(
                            "Invalid location for ParamSpec \"{}\"",
                            p.param_spec.name(self.inference.i_s.db),
                        )
                        .into(),
                    ),
                );
                self.add_issue(
                    node_ref,
                    IssueType::Note(Box::from("You can use ParamSpec as the first argument to Callable, e.g., 'Callable[P, int]'"))
                );
            }
            TypeContent::Unpacked(t) => {
                self.add_issue(node_ref, IssueType::UnpackOnlyValidInVariadicPosition);
            }
            TypeContent::Concatenate(_) => {
                self.add_issue(
                    node_ref,
                    IssueType::InvalidType(Box::from("Invalid location for Concatenate")),
                );
                self.add_issue(
                    node_ref,
                    IssueType::Note(Box::from(
                        "You can use Concatenate as the first argument to Callable",
                    )),
                );
            }
            // TODO here we would need to check if the generics are actually valid.
            TypeContent::RecursiveAlias(link) => {
                self.is_recursive_alias = true;
                return Some(Type::RecursiveType(Rc::new(RecursiveType::new(link, None))));
            }
            // TODO here we would need to check if the generics are actually valid.
            TypeContent::RecursiveClass(node_ref) => {
                self.is_recursive_alias = true;
                return Some(Type::RecursiveType(Rc::new(RecursiveType::new(
                    node_ref.as_link(),
                    None,
                ))));
            }
            TypeContent::Unknown(cause) => (),
            TypeContent::ClassVar(t) => {
                self.add_issue(node_ref, IssueType::ClassVarNestedInsideOtherType);
            }
            TypeContent::EnumMember(m) => {
                let format_data = FormatData::new_short(self.inference.i_s.db);
                self.add_issue(
                    node_ref,
                    IssueType::InvalidType(
                        format!(
                            "Invalid type: try using {} instead?",
                            m.format(&format_data)
                        )
                        .into(),
                    ),
                );
            }
            TypeContent::Final(_) => self.add_issue(node_ref, IssueType::FinalInWrongPlace),
            TypeContent::InvalidVariable(t) => {
                t.add_issue(
                    self.inference.i_s.db,
                    |t| self.add_issue(node_ref, t),
                    self.origin,
                );
            }
            TypeContent::Required(_) => {
                self.add_issue(
                    node_ref,
                    IssueType::InvalidType(
                        "Required[] can be only used in a TypedDict definition".into(),
                    ),
                );
            }
            TypeContent::NotRequired(_) => {
                self.add_issue(
                    node_ref,
                    IssueType::InvalidType(
                        "NotRequired[] can be only used in a TypedDict definition".into(),
                    ),
                );
            }
        }
        None
    }

    fn compute_named_expr_type(&mut self, named_expr: NamedExpression) -> Type {
        let t = self.compute_type(named_expr.expression());
        self.as_type(t, NodeRef::new(self.inference.file, named_expr.index()))
    }

    fn compute_type(&mut self, expr: Expression<'x>) -> TypeContent<'db, 'x> {
        let type_content = match expr.unpack() {
            ExpressionContent::ExpressionPart(n) => self.compute_type_expression_part(n),
            ExpressionContent::Lambda(_) => todo!(),
            ExpressionContent::Ternary(t) => todo!(),
        };
        if !self.inference.file.points.get(expr.index()).calculated() {
            match &type_content {
                TypeContent::Class {
                    has_type_vars: true,
                    ..
                } => {
                    // This essentially means we have a class with Any generics. This is not what
                    // we want to be defined as a redirect and therefore we calculate Foo[Any, ...]
                    return TypeContent::Type(self.as_type(
                        type_content,
                        NodeRef::new(self.inference.file, expr.index()),
                    ));
                }
                TypeContent::Class { node_ref, .. }
                | TypeContent::SimpleGeneric { node_ref, .. } => {
                    Inferred::from_saved_node_ref(*node_ref).save_redirect(
                        self.inference.i_s,
                        self.inference.file,
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
            SliceOrSimple::Slice(n) => TypeContent::InvalidVariable(InvalidVariableType::Slice),
        }
    }

    fn compute_slice_type(&mut self, slice: SliceOrSimple) -> Type {
        let t = self.compute_slice_type_content(slice);
        self.as_type(t, slice.as_node_ref())
    }

    fn compute_slice_type_or_unpack(&mut self, slice: SliceOrSimple) -> Result<Type, TupleUnpack> {
        let t = self.compute_slice_type_content(slice);
        self.convert_slice_type_or_tuple_unpack(t, slice)
    }

    fn compute_tuple_types<'s>(
        &mut self,
        iterator: impl Iterator<Item = SliceOrSimple<'s>>,
    ) -> TupleTypeArguments {
        let mut before = vec![];
        let mut after = vec![];
        let mut unpack = None;
        for s in iterator {
            match self.compute_slice_type_or_unpack(s) {
                Ok(t) => {
                    if unpack.is_none() {
                        before.push(t)
                    } else {
                        after.push(t)
                    }
                }
                Err(u) => unpack = Some(u),
            }
        }
        if let Some(unpack) = unpack {
            TupleTypeArguments::WithUnpack(WithUnpack {
                before: before.into(),
                unpack,
                after: after.into(),
            })
        } else {
            TupleTypeArguments::FixedLength(before.into())
        }
    }

    fn convert_slice_type_or_tuple_unpack(
        &mut self,
        t: TypeContent,
        slice: SliceOrSimple,
    ) -> Result<Type, TupleUnpack> {
        match t {
            TypeContent::Unpacked(TypeOrUnpack::TypeVarTuple(tvt)) => {
                Err(TupleUnpack::TypeVarTuple(tvt))
            }
            TypeContent::Unpacked(TypeOrUnpack::Type(_)) => todo!(),
            t => Ok(self.as_type(t, slice.as_node_ref())),
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

                let node_ref_a = NodeRef::new(self.inference.file, a.index());
                let node_ref_b = NodeRef::new(self.inference.file, b.index());
                if self.errors_already_calculated {
                    if self.inference.i_s.db.project.flags.disallow_any_explicit {
                        if matches!(first, TypeContent::SpecialType(SpecialType::Any)) {
                            node_ref_a
                                .add_issue(self.inference.i_s, IssueType::DisallowedAnyExplicit)
                        }
                        if matches!(second, TypeContent::SpecialType(SpecialType::Any)) {
                            node_ref_b
                                .add_issue(self.inference.i_s, IssueType::DisallowedAnyExplicit)
                        }
                    }
                    if let Some(first) = self.as_type_or_error(first, node_ref_a) {
                        if let Some(second) = self.as_type_or_error(second, node_ref_b) {
                            return TypeContent::Type(first.union(self.inference.i_s.db, second));
                        }
                    }
                    // We need to somehow track that it was an invalid union for checking aliases.
                    return TypeContent::InvalidVariable(InvalidVariableType::Other);
                }

                let first = self.as_type(first, node_ref_a);
                // TODO this should only merge in annotation contexts
                let second = self.as_type(second, node_ref_b);
                TypeContent::Type(first.union(self.inference.i_s.db, second))
            }
            _ => TypeContent::InvalidVariable(InvalidVariableType::Other),
        }
    }

    fn compute_type_primary(&mut self, primary: Primary<'x>) -> TypeContent<'db, 'x> {
        let base = self.compute_type_primary_or_atom(primary.first());
        match primary.second() {
            PrimaryContent::Attribute(name) => self.compute_type_attribute(primary, base, name),
            PrimaryContent::Execution(details) => match base {
                TypeContent::SpecialType(SpecialType::MypyExtensionsParamType(s)) => {
                    self.execute_mypy_extension_param(primary, s, details)
                }
                TypeContent::SpecialType(SpecialType::TypingNamedTuple) => {
                    let args = SimpleArguments::from_primary(
                        *self.inference.i_s,
                        self.inference.file,
                        primary,
                    );
                    TypeContent::Type(
                        match new_typing_named_tuple(self.inference.i_s, &args, true) {
                            Some(rc) => Type::NamedTuple(rc),
                            None => Type::Any(AnyCause::FromError),
                        },
                    )
                }
                TypeContent::SpecialType(SpecialType::CollectionsNamedTuple) => {
                    let args = SimpleArguments::from_primary(
                        *self.inference.i_s,
                        self.inference.file,
                        primary,
                    );
                    TypeContent::Type(
                        match new_collections_named_tuple(self.inference.i_s, &args) {
                            Some(rc) => Type::NamedTuple(rc),
                            None => Type::Any(AnyCause::FromError),
                        },
                    )
                }
                TypeContent::SpecialType(SpecialType::TypingTypedDict) => {
                    TypeContent::InvalidVariable(InvalidVariableType::InlineTypedDict)
                }
                TypeContent::Unknown(cause) => TypeContent::Unknown(cause),
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
                let s = SliceType::new(self.inference.file, primary.index(), slice_type);
                match base {
                    TypeContent::Class { node_ref, .. } => {
                        let db = self.inference.i_s.db;
                        self.compute_type_get_item_on_class(
                            Class::with_undefined_generics(node_ref),
                            s,
                            Some(primary),
                        )
                    }
                    TypeContent::Dataclass(d) => {
                        self.compute_type_get_item_on_dataclass(&d, s, Some(primary))
                    }
                    TypeContent::NamedTuple(nt) => {
                        self.compute_type_get_item_on_named_tuple(nt, s, Some(primary))
                    }
                    TypeContent::TypedDictDefinition(td) => {
                        self.compute_type_get_item_on_typed_dict(&td, s, Some(primary))
                    }
                    TypeContent::SimpleGeneric {
                        class_link,
                        generics,
                        ..
                    } => {
                        todo!()
                    }
                    TypeContent::Type(d) => match d {
                        Type::Any(_) => TypeContent::Type(d),
                        _ => {
                            debug!(
                                "Invalid getitem used on {}",
                                d.format_short(self.inference.i_s.db)
                            );
                            TypeContent::InvalidVariable(InvalidVariableType::Other)
                        }
                    },
                    TypeContent::Module(m) => todo!("{primary:?}"),
                    TypeContent::Namespace(namespace) => todo!("{primary:?}"),
                    TypeContent::TypeAlias(m) => self.compute_type_get_item_on_alias(m, s),
                    TypeContent::SpecialType(special) => match special {
                        SpecialType::Union => self.compute_type_get_item_on_union(s),
                        SpecialType::Optional => self.compute_type_get_item_on_optional(s),
                        SpecialType::Type => self.compute_type_get_item_on_type(s),
                        SpecialType::Tuple => self.compute_type_get_item_on_tuple(s),
                        SpecialType::Any => todo!(),
                        SpecialType::Protocol => {
                            self.expect_type_var_like_args(s, "Protocol");
                            TypeContent::SpecialType(SpecialType::ProtocolWithGenerics)
                        }
                        SpecialType::ProtocolWithGenerics => todo!(),
                        SpecialType::Generic => {
                            self.expect_type_var_like_args(s, "Generic");
                            TypeContent::SpecialType(SpecialType::GenericWithGenerics)
                        }
                        SpecialType::GenericWithGenerics => todo!(),
                        SpecialType::TypingNamedTuple | SpecialType::CollectionsNamedTuple => {
                            todo!()
                        }
                        SpecialType::TypingTypedDict => todo!(),
                        SpecialType::Required => {
                            self.compute_type_get_item_on_required_like(s, "Required")
                        }
                        SpecialType::NotRequired => {
                            self.compute_type_get_item_on_required_like(s, "NotRequired")
                        }
                        SpecialType::Callable => self.compute_type_get_item_on_callable(s),
                        SpecialType::MypyExtensionsParamType(_) => todo!(),
                        SpecialType::CallableParam(_) => todo!(),
                        SpecialType::Literal => self.compute_get_item_on_literal(s),
                        SpecialType::LiteralString => todo!(),
                        SpecialType::TypeAlias => todo!(),
                        SpecialType::Self_ => {
                            self.add_issue(
                                s.as_node_ref(),
                                IssueType::InvalidType(Box::from(
                                    "Self type cannot have type arguments",
                                )),
                            );
                            TypeContent::Type(Type::Any(AnyCause::FromError))
                        }
                        SpecialType::Final => self.compute_type_get_item_on_final(s),
                        SpecialType::Unpack => self.compute_type_get_item_on_unpack(s),
                        SpecialType::Concatenate => self.compute_type_get_item_on_concatenate(s),
                        SpecialType::Annotated => self.compute_get_item_on_annotated(s),
                        SpecialType::ClassVar => self.compute_get_item_on_class_var(s),
                    },
                    TypeContent::RecursiveAlias(link) => {
                        self.is_recursive_alias = true;
                        let type_vars = &NodeRef::from_link(self.inference.i_s.db, link)
                            .maybe_alias()
                            .unwrap()
                            .type_vars;
                        let generics = self.compute_generics_for_alias(s, type_vars);
                        TypeContent::Type(Type::RecursiveType(Rc::new(RecursiveType::new(
                            link,
                            Some(generics),
                        ))))
                    }
                    TypeContent::RecursiveClass(node_ref) => {
                        let class = Class::with_undefined_generics(node_ref);
                        let type_var_likes = class.type_vars(self.inference.i_s);
                        let mut generics = vec![];
                        self.compute_get_item_generics_on_class(
                            s,
                            s.iter(),
                            class.name(),
                            type_var_likes,
                            &mut generics,
                        );
                        TypeContent::Type(Type::RecursiveType(Rc::new(RecursiveType::new(
                            node_ref.as_link(),
                            (!type_var_likes.is_empty())
                                .then(|| GenericsList::generics_from_vec(generics)),
                        ))))
                    }
                    TypeContent::InvalidVariable(t) => {
                        t.add_issue(
                            self.inference.i_s.db,
                            |t| self.add_issue(s.as_node_ref(), t),
                            self.origin,
                        );
                        TypeContent::Unknown(AnyCause::FromError)
                    }
                    TypeContent::TypeVarTuple(_) => todo!(),
                    TypeContent::ParamSpec(_) => todo!(),
                    TypeContent::Unpacked(_) => todo!(),
                    TypeContent::Concatenate(_) => todo!(),
                    TypeContent::ClassVar(_) => todo!(),
                    TypeContent::EnumMember(_) => todo!(),
                    TypeContent::Required(_) => todo!(),
                    TypeContent::NotRequired(_) => todo!(),
                    TypeContent::Final(_) => todo!(),
                    TypeContent::Unknown(cause) => TypeContent::Unknown(cause),
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
        let db = self.inference.i_s.db;
        match base {
            TypeContent::Module(f) => {
                if let Some(index) = f.symbol_table.lookup_symbol(name.as_str()) {
                    self.inference.file.points.set(
                        name.index(),
                        Point::new_redirect(f.file_index(), index, Locality::Todo),
                    );
                    self.compute_type_name(name)
                } else {
                    let module = Module::new(f);
                    match module.sub_module(db, name.as_str()) {
                        Some(ImportResult::File(file_index)) => {
                            self.inference.file.points.set(
                                name.index(),
                                Point::new_file_reference(file_index, Locality::Todo),
                            );
                            TypeContent::Module(db.loaded_python_file(file_index))
                        }
                        Some(ImportResult::Namespace { .. }) => todo!(),
                        None => {
                            let node_ref = NodeRef::new(self.inference.file, primary.index());
                            if let Some(inf) = module
                                .maybe_execute_getattr(self.inference.i_s, &|issue| {
                                    node_ref.add_issue(self.inference.i_s, issue)
                                })
                            {
                                // If a module contains a __getattr__, the type can be part of that
                                // (which is typically just an Any that propagates).
                                match check_module_getattr_type(self.inference.i_s, inf) {
                                    TypeNameLookup::Unknown(cause) => TypeContent::Unknown(cause),
                                    _ => unreachable!(),
                                }
                            } else {
                                debug!("TypeComputation: Attribute on class not found");
                                self.add_issue_for_index(primary.index(), IssueType::TypeNotFound);
                                self.inference.file.points.set(
                                    name.index(),
                                    Point::new_simple_specific(
                                        Specific::AnyDueToError,
                                        Locality::Todo,
                                    ),
                                );
                                TypeContent::Unknown(AnyCause::FromError)
                            }
                        }
                    }
                }
            }
            TypeContent::Namespace(n) => {
                match python_import(
                    db,
                    self.inference.file_index,
                    &n.path,
                    &n.content,
                    name.as_str(),
                ) {
                    Some(ImportResult::File(file_index)) => {
                        let file = db.loaded_python_file(file_index);
                        TypeContent::Module(file)
                    }
                    Some(ImportResult::Namespace(ns)) => TypeContent::Namespace(ns),
                    None => {
                        self.add_issue_for_index(primary.index(), IssueType::TypeNotFound);
                        TypeContent::Unknown(AnyCause::FromError)
                    }
                }
            }
            TypeContent::Class { node_ref, .. } => {
                let cls = Class::with_undefined_generics(node_ref);
                self.check_attribute_on_class(cls, primary, name)
            }
            TypeContent::Dataclass(_) | TypeContent::NamedTuple(_) => todo!(),
            TypeContent::TypedDictDefinition(_) => todo!(),
            TypeContent::SimpleGeneric {
                class_link,
                generics,
                ..
            } => {
                let cls = Class::from_generic_class_components(db, class_link, &generics);
                self.check_attribute_on_class(cls, primary, name)
            }
            TypeContent::Type(t) => match t {
                Type::Any(cause) => TypeContent::Type(Type::Any(cause)),
                Type::Enum(e) => match Enum::lookup(&e, db, name.as_str(), false) {
                    Some(m) => TypeContent::EnumMember(m),
                    _ => {
                        let content = TypeContent::Class {
                            node_ref: NodeRef::from_link(db, e.class),
                            has_type_vars: false, // Enums have no type vars ever.
                        };
                        self.compute_type_attribute(primary, content, name)
                    }
                },
                _ => TypeContent::InvalidVariable(InvalidVariableType::Other),
            },
            TypeContent::TypeAlias(_)
            | TypeContent::RecursiveAlias(_)
            | TypeContent::RecursiveClass(_) => todo!(),
            TypeContent::SpecialType(m) => todo!(),
            TypeContent::TypeVarTuple(_) => todo!(),
            TypeContent::ParamSpec(param_spec) => match name.as_code() {
                "args" => TypeContent::Type(Type::ParamSpecArgs(param_spec)),
                "kwargs" => TypeContent::Type(Type::ParamSpecKwargs(param_spec)),
                _ => todo!(),
            },
            TypeContent::Unpacked(_) => todo!(),
            TypeContent::Concatenate(_) => todo!(),
            TypeContent::InvalidVariable(t) => TypeContent::InvalidVariable(t),
            TypeContent::ClassVar(_) => todo!(),
            TypeContent::EnumMember(_) => todo!(),
            TypeContent::Required(_) => todo!(),
            TypeContent::NotRequired(_) => todo!(),
            TypeContent::Final(_) => todo!(),
            TypeContent::Unknown(cause) => TypeContent::Unknown(cause),
        }
    }

    fn check_attribute_on_class(
        &mut self,
        cls: Class,
        primary: Primary,
        name: Name<'x>,
    ) -> TypeContent<'db, 'x> {
        let point_type = cache_name_on_class(cls, self.inference.file, name);
        if point_type == PointType::Redirect {
            self.compute_type_name(name)
        } else {
            debug!("TypeComputation: Attribute on class not found");
            debug_assert_eq!(point_type, PointType::Specific);
            self.add_issue_for_index(primary.index(), IssueType::TypeNotFound);
            TypeContent::Unknown(AnyCause::FromError)
        }
    }

    fn compute_generics_for_alias(
        &mut self,
        slice_type: SliceType,
        type_var_likes: &TypeVarLikes,
    ) -> GenericsList {
        let mut generics = vec![];
        self.calculate_type_arguments(
            slice_type,
            &mut generics,
            slice_type.iter(),
            type_var_likes,
            &|| Box::from("TODO alias name"),
            |slf: &mut Self, given_count, expected_count| {
                slf.add_issue(
                    slice_type.as_node_ref(),
                    IssueType::TypeAliasArgumentIssue {
                        expected_count,
                        given_count,
                    },
                );
            },
        );
        GenericsList::generics_from_vec(generics)
    }

    #[inline]
    fn check_constraints(
        &mut self,
        type_var: &TypeVar,
        s: &SliceOrSimple,
        type_: &TypeContent,
        get_of: impl FnOnce() -> Box<str>,
    ) {
        match &type_var.kind {
            TypeVarKind::Unrestricted => (),
            TypeVarKind::Bound(bound) => {
                // Performance: This could be optimized to not create new objects all the time.
                let actual = self.as_type(type_.clone(), s.as_node_ref());
                let i_s = &mut self.inference.i_s;
                if !bound.is_simple_super_type_of(i_s, &actual).bool() {
                    s.as_node_ref().add_issue(
                        i_s,
                        IssueType::TypeVarBoundViolation {
                            actual: actual.format_short(i_s.db),
                            of: get_of(),
                            expected: bound.format_short(i_s.db),
                        },
                    );
                }
            }
            TypeVarKind::Constraints(constraints) => {
                let t2 = self.as_type(type_.clone(), s.as_node_ref());
                let i_s = &mut self.inference.i_s;
                if let Type::TypeVar(usage) = &t2 {
                    if let TypeVarKind::Constraints(constraints2) = &usage.type_var.kind {
                        if constraints2.iter().all(|t2| {
                            constraints
                                .iter()
                                .any(|t| t.is_simple_super_type_of(i_s, t2).bool())
                        }) {
                            // The provided type_var2 is a subset of the type_var constraints.
                            return;
                        }
                    }
                }
                if !constraints
                    .iter()
                    .any(|t| t.is_simple_super_type_of(i_s, &t2).bool())
                {
                    s.as_node_ref().add_issue(
                        i_s,
                        IssueType::InvalidTypeVarValue {
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
        let db = self.inference.i_s.db;
        let c = match self.compute_type_get_item_on_class_inner(
            Class::with_undefined_generics(NodeRef::from_link(db, dataclass.class.link)),
            slice_type,
            primary,
        ) {
            ClassGetItemResult::GenericClass(c) => c,
            ClassGetItemResult::SimpleGeneric {
                node_ref, generics, ..
            } => GenericClass {
                link: node_ref.as_link(),
                generics,
            },
        };
        TypeContent::Type(Type::Dataclass(Dataclass::new(c, dataclass.options)))
    }

    fn compute_type_get_item_on_named_tuple(
        &mut self,
        named_tuple: Rc<NamedTuple>,
        slice_type: SliceType,
        primary: Option<Primary>,
    ) -> TypeContent<'db, 'db> {
        let db = self.inference.i_s.db;
        let mut generics = vec![];
        self.calculate_type_arguments(
            slice_type,
            &mut generics,
            slice_type.iter(),
            &named_tuple.__new__.type_vars,
            &|| todo!(), //Box::from("TODO type name"),
            |slf: &mut Self, given_count, expected_count| {
                slf.add_issue(
                    slice_type.as_node_ref(),
                    IssueType::TypeArgumentIssue {
                        class: named_tuple.name.as_str(db).into(),
                        given_count,
                        expected_count,
                    },
                );
            },
        );
        let defined_at = named_tuple.__new__.defined_at;
        TypeContent::Type(
            Type::NamedTuple(named_tuple).replace_type_var_likes(db, &mut |usage| {
                if usage.in_definition() == defined_at {
                    generics[usage.index().as_usize()].clone()
                } else {
                    usage.into_generic_item()
                }
            }),
        )
    }

    fn compute_type_get_item_on_typed_dict(
        &mut self,
        typed_dict: &TypedDict,
        slice_type: SliceType,
        primary: Option<Primary>,
    ) -> TypeContent<'db, 'db> {
        let db = self.inference.i_s.db;
        let mut generics = vec![];
        if let TypedDictGenerics::NotDefinedYet(type_var_likes) = &typed_dict.generics {
            self.calculate_type_arguments(
                slice_type,
                &mut generics,
                slice_type.iter(),
                type_var_likes,
                &|| todo!(), //Box::from("TODO type name"),
                |slf: &mut Self, given_count, expected_count| {
                    slf.add_issue(
                        slice_type.as_node_ref(),
                        IssueType::TypeArgumentIssue {
                            class: typed_dict
                                .name_or_fallback(&FormatData::new_short(db))
                                .into(),
                            given_count,
                            expected_count,
                        },
                    );
                },
            );
            let generics = GenericsList::generics_from_vec(generics);
            let new_td = typed_dict.apply_generics(db, generics);
            TypeContent::Type(Type::TypedDict(new_td))
        } else {
            todo!()
        }
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
        }
    }

    fn compute_type_get_item_on_class_inner(
        &mut self,
        class: Class,
        slice_type: SliceType,
        primary: Option<Primary>,
    ) -> ClassGetItemResult<'db> {
        if !matches!(class.generics(), Generics::None | Generics::NotDefinedYet) {
            todo!();
            //return TypeContent::InvalidVariable(InvalidVariableType::Other);
        }
        let type_var_likes = class.type_vars(self.inference.i_s);

        let mut iterator = slice_type.iter();
        let mut generics = vec![];

        if !type_var_likes.is_empty() {
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
            |slf: &mut Self, given_count, expected_count| {
                slf.add_issue(
                    slice_type.as_node_ref(),
                    IssueType::TypeArgumentIssue {
                        class: Box::from(class_name),
                        given_count,
                        expected_count,
                    },
                );
            },
        );
    }

    #[inline]
    fn maybe_generic_class_without_type_var(
        &mut self,
        class: Class,
        slice_type: SliceType<'x>,
        generics: &mut Vec<GenericItem>,
        iterator: &mut impl Iterator<Item = SliceOrSimple<'x>>,
        tvs: &TypeVarLikes,
        primary: Option<Primary>,
    ) -> Option<(NodeRef<'db>, ClassGenerics)> {
        if primary.is_none() || self.origin != TypeComputationOrigin::ParamTypeCommentOrAnnotation {
            return None;
        }
        for (i, type_var_like) in tvs.iter().enumerate() {
            let TypeVarLike::TypeVar(type_var) = type_var_like else {
                return None
            };
            if let Some(slice_content) = iterator.next() {
                let t = self.compute_slice_type_content(slice_content);
                self.check_constraints(type_var, &slice_content, &t, || Box::from(class.name()));
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
                        generics.push(GenericItem::TypeArgument(
                            self.compute_slice_type(slice_content),
                        ));
                    }
                    generics.push(GenericItem::TypeArgument(
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
            let node_ref = NodeRef::new(self.inference.file, primary.unwrap().index())
                .to_db_lifetime(self.inference.i_s.db);
            node_ref.set_point(Point::new_simple_specific(
                Specific::SimpleGeneric,
                Locality::Todo,
            ));
            Some((
                node_ref,
                match slice_type.ast_node {
                    ASTSliceType::NamedExpression(n) => ClassGenerics::ExpressionWithClassType(
                        PointLink::new(node_ref.file_index(), n.expression().index()),
                    ),
                    ASTSliceType::Slices(slices) => ClassGenerics::SlicesWithClassTypes(
                        PointLink::new(node_ref.file_index(), slices.index()),
                    ),
                    ASTSliceType::Slice(_) => unreachable!(),
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
        mut iterator: impl Iterator<Item = SliceOrSimple<'x>>,
        type_var_likes: &TypeVarLikes,
        get_of: &impl Fn() -> Box<str>,
        on_count_mismatch: impl FnOnce(&mut Self, usize, usize),
    ) {
        let mut given_count = generics.len();
        let expected_count = type_var_likes.len();
        for type_var_like in type_var_likes.iter().skip(generics.len()) {
            let generic_item = match type_var_like {
                TypeVarLike::TypeVar(type_var) => {
                    if let Some(slice_content) = iterator.next() {
                        let t = self.compute_slice_type_content(slice_content);
                        self.check_constraints(&type_var, &slice_content, &t, get_of);
                        given_count += 1;
                        GenericItem::TypeArgument(self.as_type(t, slice_content.as_node_ref()))
                    } else {
                        type_var_like.as_any_generic_item()
                    }
                }
                TypeVarLike::TypeVarTuple(_) => {
                    let fetch = slice_type.iter().count() as isize + 1 - expected_count as isize;
                    GenericItem::TypeArguments(TypeArguments {
                        args: if let Ok(fetch) = fetch.try_into() {
                            given_count += 1;
                            self.compute_tuple_types(iterator.by_ref().take(fetch))
                        } else {
                            // If not enough type arguments are given, an error is raised elsewhere.
                            TupleTypeArguments::FixedLength(Rc::new([]))
                        },
                    })
                }
                TypeVarLike::ParamSpec(_) => {
                    given_count += 1;
                    if expected_count == 1 && slice_type.iter().count() != 1 {
                        // PEP 612 allows us to write C[int, str] instead of C[[int, str]],
                        // because "for aesthetic purposes we allow these to be omitted".
                        let params = self.calculate_simplified_param_spec_generics(&mut iterator);
                        GenericItem::ParamSpecArgument(ParamSpecArgument::new(params, None))
                    } else {
                        let params = self.calculate_callable_params(
                            iterator.next().unwrap(),
                            true,
                            expected_count == 1,
                        );
                        GenericItem::ParamSpecArgument(ParamSpecArgument::new(params, None))
                    }
                }
            };
            generics.push(generic_item);
        }
        for slice_content in iterator {
            // Still calculate errors for the rest of the types given. After all they are still
            // expected to be types.
            self.compute_slice_type(slice_content);
            given_count += 1;
        }
        if given_count != expected_count {
            on_count_mismatch(self, given_count, expected_count);
            generics.clear();
            for missing_type_var in type_var_likes.iter() {
                generics.push(missing_type_var.as_any_generic_item())
            }
        }
    }

    fn compute_type_get_item_on_tuple(&mut self, slice_type: SliceType) -> TypeContent<'db, 'db> {
        let mut iterator = slice_type.iter();
        let first = iterator.next().unwrap();
        let generics = if let Some(slice_or_simple) = iterator.next() {
            if let SliceOrSimple::Simple(s) = slice_or_simple {
                if s.named_expr.is_ellipsis_literal() {
                    let t = self.compute_slice_type(first);
                    return TypeContent::Type(Type::Tuple(Rc::new(Tuple::new_arbitrary_length(t))));
                }
            }
            Tuple::new(self.compute_tuple_types(slice_type.iter()))
        } else {
            let t = self.compute_slice_type_content(first);
            // Handle Tuple[()]
            match t {
                TypeContent::InvalidVariable(InvalidVariableType::Tuple { tuple_length: 0 }) => {
                    Tuple::new_fixed_length(Rc::new([]))
                }
                _ => match self.convert_slice_type_or_tuple_unpack(t, first) {
                    Ok(t) => Tuple::new_fixed_length(Rc::new([t])),
                    Err(unpack) => Tuple::new(TupleTypeArguments::WithUnpack(WithUnpack {
                        before: Rc::from([]),
                        unpack,
                        after: Rc::from([]),
                    })),
                },
            }
        };
        TypeContent::Type(Type::Tuple(Rc::new(generics)))
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
                        IssueType::ParamSpecNestedSpecificationsNotAllowed,
                    );
                    had_issue = true;
                }
                _ => self.add_param(&mut params, t, s.as_node_ref().node_index),
            }
        }
        if had_issue {
            CallableParams::Any(AnyCause::FromError)
        } else {
            CallableParams::Simple(Rc::from(params))
        }
    }

    fn check_param(&mut self, t: TypeContent, index: NodeIndex) -> CallableParam {
        let param_type = match t {
            TypeContent::SpecialType(SpecialType::CallableParam(p)) => return p,
            TypeContent::Unpacked(TypeOrUnpack::Type(Type::TypedDict(td))) => {
                ParamType::StarStar(StarStarParamType::UnpackTypedDict(td))
            }
            _ => {
                ParamType::PositionalOnly(self.as_type(t, NodeRef::new(self.inference.file, index)))
            }
        };
        CallableParam {
            type_: param_type,
            has_default: false,
            name: None,
        }
    }

    fn add_param(&mut self, params: &mut Vec<CallableParam>, t: TypeContent, index: NodeIndex) {
        let p = self.check_param(t, index);
        if let Some(previous) = params.last() {
            let prev_kind = previous.type_.param_kind();
            let current_kind = p.type_.param_kind();
            let msg = match current_kind {
                ParamKind::PositionalOnly
                    if current_kind < prev_kind || previous.has_default && !p.has_default =>
                {
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
                self.add_issue_for_index(index, IssueType::InvalidType(Box::from(msg)));
                return;
            }

            if let Some(param_name) = p.name.as_ref() {
                let param_name = param_name.as_str(self.inference.i_s.db);
                for other in params.iter() {
                    if let Some(other_name) = other.name.as_ref() {
                        let other_name = other_name.as_str(self.inference.i_s.db);
                        if param_name == other_name {
                            self.add_issue_for_index(
                                index,
                                IssueType::InvalidType(
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
            todo!();
        };
        let calc_params =
            |slf: &mut Self| match slf.compute_slice_type_content(first) {
                TypeContent::ParamSpec(p) => CallableParams::WithParamSpec(Rc::new([]), p),
                TypeContent::SpecialType(SpecialType::Any) if from_class_generics => {
                    CallableParams::Any(AnyCause::Explicit)
                }
                TypeContent::Unknown(cause) => CallableParams::Any(cause),
                TypeContent::Concatenate(p) => p,
                t if allow_aesthetic_class_simplification => CallableParams::Simple(Rc::new([
                    slf.check_param(t, first.as_node_ref().node_index)
                ])),
                _ => {
                    if from_class_generics {
                        slf.add_issue(
                            n.as_node_ref(),
                            IssueType::InvalidParamSpecGenerics {
                                got: Box::from(n.named_expr.as_code()),
                            },
                        );
                    } else {
                        slf.add_issue(n.as_node_ref(), IssueType::InvalidCallableParams);
                    }
                    CallableParams::Any(AnyCause::FromError)
                }
            };
        match n.named_expr.expression().maybe_unpacked_atom() {
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
                            match t {
                                TypeContent::TypeVarTuple(tvt) => todo!(),
                                _ => {
                                    let node_ref =
                                        NodeRef::new(self.inference.file, star_expr.index());
                                    let t = self.as_type(t, node_ref);
                                    if matches!(t, Type::Tuple(_)) {
                                        todo!()
                                    }
                                    self.add_issue(
                                        node_ref,
                                        IssueType::VariadicUnpackMustBeTupleLike {
                                            actual: t.format_short(self.inference.i_s.db),
                                        },
                                    );
                                }
                            }
                        }
                        _ => unreachable!(),
                    }
                }
                CallableParams::Simple(Rc::from(params))
            }
            Some(AtomContent::Ellipsis) => CallableParams::Any(AnyCause::Explicit),
            _ => calc_params(self),
        }
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

        let db = self.inference.i_s.db;
        let content = if slice_type.iter().count() == 2 {
            let mut iterator = slice_type.iter();
            let params = self.calculate_callable_params(iterator.next().unwrap(), false, false);
            let return_type = iterator
                .next()
                .map(|slice_content| self.compute_slice_type(slice_content))
                .unwrap_or(Type::Any(AnyCause::Todo));
            Rc::new(CallableContent {
                name: None,
                class_name: None,
                defined_at,
                kind: FunctionKind::Function {
                    had_first_self_or_class_annotation: true,
                },
                type_vars: self
                    .inference
                    .i_s
                    .db
                    .python_state
                    .empty_type_var_likes
                    .clone(),
                params,
                return_type,
            })
        } else {
            self.add_issue(slice_type.as_node_ref(), IssueType::InvalidCallableArgCount);
            self.inference
                .i_s
                .db
                .python_state
                .any_callable_from_error
                .clone()
        };
        self.current_callable = old;
        TypeContent::Type(Type::Callable(content))
    }

    fn compute_type_get_item_on_union(
        &mut self,
        slice_type: SliceType,
    ) -> TypeContent<'static, 'static> {
        let iterator = slice_type.iter();
        if let SliceTypeIterator::SliceOrSimple(s) = iterator {
            let t = self.compute_slice_type_content(s);
            let t = self.as_type(t, s.as_node_ref());
            TypeContent::Type(t)
        } else {
            let mut entries = vec![];
            let mut format_index = 0;
            for slice_or_simple in iterator {
                let t = self.compute_slice_type_content(slice_or_simple);
                let type_ = self.as_type(t, slice_or_simple.as_node_ref());
                match type_ {
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
            let mut t = UnionType::new(entries);
            t.sort_for_priority();
            TypeContent::Type(Type::Union(t))
        }
    }

    fn compute_type_get_item_on_optional(
        &mut self,
        slice_type: SliceType,
    ) -> TypeContent<'db, 'db> {
        let mut iterator = slice_type.iter();
        let first = iterator.next().unwrap();
        if let Some(next) = iterator.next() {
            self.add_issue(next.as_node_ref(), IssueType::OptionalMustHaveOneArgument);
        }
        let t = self.compute_slice_type(first);
        let format_as_optional = !t.is_union_like();
        let mut t = t.union_with_details(self.inference.i_s.db, Type::None, format_as_optional);
        if let Type::Union(union_type) = &mut t {
            union_type.sort_for_priority();
        };
        TypeContent::Type(t)
    }

    fn compute_type_get_item_on_type(&mut self, slice_type: SliceType) -> TypeContent<'db, 'db> {
        let mut iterator = slice_type.iter();
        let content = iterator.next().unwrap();
        if iterator.count() > 0 {
            todo!()
        }
        let mut t = match self.compute_slice_type_content(content) {
            TypeContent::SpecialType(SpecialType::Type) => {
                self.inference.i_s.db.python_state.bare_type_type()
            }
            t => self.as_type(t, content.as_node_ref()),
        };
        if t.iter_with_unpacked_unions()
            .any(|t| matches!(t, Type::Type(_)))
        {
            t = Type::Any(AnyCause::FromError);
            self.add_issue(
                slice_type.as_node_ref(),
                IssueType::TypeCannotContainAnotherType,
            )
        }
        TypeContent::Type(Type::Type(Rc::new(t)))
    }

    fn compute_type_get_item_on_alias(
        &mut self,
        alias: &TypeAlias,
        slice_type: SliceType,
    ) -> TypeContent<'db, 'db> {
        let generics = self.compute_generics_for_alias(slice_type, &alias.type_vars);
        self.is_recursive_alias |= alias.is_recursive();
        TypeContent::Type(
            alias
                .replace_type_var_likes(self.inference.i_s.db, false, &mut |usage| {
                    generics[usage.index()].clone()
                })
                .into_owned(),
        )
    }

    fn compute_type_get_item_on_final(&mut self, slice_type: SliceType) -> TypeContent<'db, 'db> {
        let mut iterator = slice_type.iter();
        let first = iterator.next().unwrap();
        if iterator.count() != 0 {
            self.add_issue(slice_type.as_node_ref(), IssueType::FinalTooManyArguments);
        }
        match self.compute_slice_type_content(first) {
            TypeContent::ClassVar(_) => {
                slice_type
                    .as_node_ref()
                    .add_issue(self.inference.i_s, IssueType::FinalAndClassVarUsedBoth);
                TypeContent::Unknown(AnyCause::FromError)
            }
            t => TypeContent::Final(self.as_type(t, slice_type.as_node_ref())),
        }
    }

    fn compute_type_get_item_on_unpack(&mut self, slice_type: SliceType) -> TypeContent<'db, 'db> {
        let mut iterator = slice_type.iter();
        let first = iterator.next().unwrap();
        if iterator.count() == 0 {
            TypeContent::Unpacked(match self.compute_slice_type_content(first) {
                TypeContent::TypeVarTuple(t) => TypeOrUnpack::TypeVarTuple(t),
                t => TypeOrUnpack::Type(self.as_type(t, first.as_node_ref())),
            })
        } else {
            self.add_issue(
                slice_type.as_node_ref(),
                IssueType::UnpackRequiresExactlyOneArgument,
            );
            TypeContent::Unknown(AnyCause::FromError)
        }
    }

    fn compute_type_get_item_on_concatenate(
        &mut self,
        slice_type: SliceType,
    ) -> TypeContent<'db, 'db> {
        let count = slice_type.iter().count();
        let mut iterator = slice_type.iter();
        let types: Vec<_> = iterator
            .by_ref()
            .take(count - 1)
            .map(|s| self.compute_slice_type(s))
            .collect();
        match self.compute_slice_type_content(iterator.next().unwrap()) {
            TypeContent::ParamSpec(p) => {
                TypeContent::Concatenate(CallableParams::WithParamSpec(types.into(), p))
            }
            TypeContent::Concatenate(_) => {
                self.add_issue(slice_type.as_node_ref(), IssueType::NestedConcatenate);
                TypeContent::Unknown(AnyCause::FromError)
            }
            TypeContent::Unknown(cause) => TypeContent::Unknown(cause),
            TypeContent::InvalidVariable(InvalidVariableType::Ellipsis) => {
                let mut params: Vec<_> = types
                    .into_iter()
                    .map(|t| CallableParam::new_anonymous(ParamType::PositionalOnly(t)))
                    .collect();
                params.push(CallableParam::new_anonymous(ParamType::Star(
                    StarParamType::ArbitraryLength(Type::Any(AnyCause::Explicit)),
                )));
                params.push(CallableParam::new_anonymous(ParamType::StarStar(
                    StarStarParamType::ValueType(Type::Any(AnyCause::Explicit)),
                )));
                TypeContent::Concatenate(CallableParams::Simple(params.into()))
            }
            _ => {
                self.add_issue(
                    slice_type.as_node_ref(),
                    IssueType::ConcatenateLastParamNeedsToBeParamSpec,
                );
                TypeContent::Unknown(AnyCause::FromError)
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
        slice: SliceOrSimple<'x>,
        index: usize,
    ) -> TypeContent<'db, 'db> {
        if let SliceOrSimple::Simple(s) = slice {
            let expr_not_allowed = |slf: &Self| {
                slf.add_issue(
                    slice.as_node_ref(),
                    IssueType::InvalidType(
                        "Invalid type: Literal[...] cannot contain arbitrary expressions".into(),
                    ),
                );
                TypeContent::Unknown(AnyCause::FromError)
            };
            match s.named_expr.expression().unpack() {
                ExpressionContent::ExpressionPart(ExpressionPart::Atom(atom)) => {
                    let maybe = match atom.unpack() {
                        AtomContent::Int(i) => {
                            Some(LiteralKind::Int(i.parse().unwrap_or_else(|| todo!())))
                        }
                        AtomContent::Bytes(b) => Some(LiteralKind::Bytes(
                            NodeRef::new(self.inference.file, b.index()).as_link(),
                        )),
                        AtomContent::Strings(s) => s.maybe_single_string_literal().map(|s| {
                            LiteralKind::String(
                                DbString::from_python_string(
                                    self.inference.file_index,
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
                                IssueType::InvalidType(
                                    format!(
                                        "Parameter {} of Literal[...] cannot be of type \"float\"",
                                        index
                                    )
                                    .into(),
                                ),
                            );
                            return TypeContent::Unknown(AnyCause::FromError);
                        }
                        AtomContent::Complex(_) => {
                            self.add_issue(
                                slice.as_node_ref(),
                                IssueType::InvalidType(
                                    format!(
                                        "Parameter {} of Literal[...] cannot be of type \"complex\"",
                                        index
                                    )
                                    .into(),
                                ),
                            );
                            return TypeContent::Unknown(AnyCause::FromError);
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
                    if sign.as_code() == "-" {
                        if let ExpressionPart::Atom(atom) = e {
                            if let AtomContent::Int(i) = atom.unpack() {
                                if let Some(i) = i.parse() {
                                    let node_ref = NodeRef::new(self.inference.file, f.index());
                                    return TypeContent::Type(Type::Literal(Literal {
                                        kind: LiteralKind::Int(-i),
                                        implicit: false,
                                    }));
                                } else {
                                    todo!()
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
            TypeContent::SpecialType(SpecialType::Any) => {
                self.add_issue(
                    slice.as_node_ref(),
                    IssueType::InvalidType(
                        format!("Parameter {index} of Literal[...] cannot be of type \"Any\"")
                            .into(),
                    ),
                );
                TypeContent::Unknown(AnyCause::FromError)
            }
            TypeContent::InvalidVariable(_) => {
                self.add_issue(
                    slice.as_node_ref(),
                    IssueType::InvalidType(
                        format!("Parameter {index} of Literal[...] is invalid").into(),
                    ),
                );
                TypeContent::Unknown(AnyCause::FromError)
            }
            TypeContent::EnumMember(e) => TypeContent::Type(Type::EnumMember(e)),
            t => match self.as_type(t, slice.as_node_ref()) {
                Type::Any(_) => TypeContent::Unknown(AnyCause::FromError),
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
                        IssueType::InvalidType(
                            format!("Parameter {} of Literal[...] is invalid", index).into(),
                        ),
                    );
                    TypeContent::Unknown(AnyCause::FromError)
                }
            },
        }
    }

    fn compute_get_item_on_annotated(&mut self, slice_type: SliceType) -> TypeContent<'db, 'db> {
        let mut iterator = slice_type.iter();
        let first = iterator.next().unwrap();
        if iterator.next().is_none() {
            self.add_issue(
                slice_type.as_node_ref(),
                IssueType::InvalidType(Box::from(
                    "Annotated[...] must have exactly one type argument and at least one annotation",
                )),
            );
            TypeContent::Unknown(AnyCause::FromError)
        } else {
            TypeContent::Type(self.compute_slice_type(first))
        }
    }

    fn compute_get_item_on_class_var(&mut self, slice_type: SliceType) -> TypeContent<'db, 'db> {
        let mut iterator = slice_type.iter();
        let first = iterator.next().unwrap();
        if iterator.next().is_some() {
            self.add_issue(
                slice_type.as_node_ref(),
                IssueType::ClassVarTooManyArguments,
            );
            TypeContent::Unknown(AnyCause::FromError)
        } else {
            let i_s = self.inference.i_s;
            if i_s.current_class().is_none() || i_s.current_function().is_some() {
                self.add_issue(
                    slice_type.as_node_ref(),
                    IssueType::ClassVarOnlyInAssignmentsInClass,
                );
                TypeContent::Unknown(AnyCause::FromError)
            } else {
                TypeContent::ClassVar(self.compute_slice_type(first))
            }
        }
    }

    fn compute_type_get_item_on_required_like(
        &mut self,
        slice_type: SliceType,
        case: &str,
    ) -> TypeContent<'static, 'static> {
        let mut iterator = slice_type.iter();
        let first = iterator.next().unwrap();
        if let Some(next) = iterator.next() {
            self.add_issue(
                next.as_node_ref(),
                IssueType::InvalidType(
                    format!("{case}[] must have exactly one type argument").into(),
                ),
            );
            TypeContent::Unknown(AnyCause::FromError)
        } else {
            let t = self.compute_slice_type(first);
            if case == "Required" {
                TypeContent::Required(t)
            } else {
                TypeContent::NotRequired(t)
            }
        }
    }

    fn expect_type_var_like_args(&mut self, slice_type: SliceType, class: &'static str) {
        for (i, s) in slice_type.iter().enumerate() {
            let result = self.compute_slice_type_content(s);
            let unpacked_type_var_tuple = matches!(
                &result,
                TypeContent::Unpacked(TypeOrUnpack::TypeVarTuple(t))
                    if t.in_definition == self.for_definition
            );
            if !matches!(result, TypeContent::ParamSpec(_))
                && !matches!(
                    result,
                    TypeContent::Type(Type::TypeVar(usage))
                        if usage.in_definition == self.for_definition
                )
                && !unpacked_type_var_tuple
            {
                self.add_issue(s.as_node_ref(), IssueType::TypeVarExpected { class })
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
            AtomContent::Name(n) => {
                self.inference.infer_name_reference(n);
                self.compute_type_name(n)
            }
            AtomContent::Strings(s_o_b) => match s_o_b.as_python_string() {
                PythonString::Ref(start, s) => self.compute_forward_reference(start, s.into()),
                PythonString::String(start, s) => self.compute_forward_reference(start, s.into()),
                PythonString::FString => todo!(),
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
            _ => TypeContent::InvalidVariable(InvalidVariableType::Other),
        }
    }

    fn compute_type_name(&mut self, name: Name<'x>) -> TypeContent<'db, 'x> {
        match self.inference.lookup_type_name(name) {
            TypeNameLookup::Module(f) => TypeContent::Module(f),
            TypeNameLookup::Namespace(namespace) => TypeContent::Namespace(namespace),
            TypeNameLookup::Class { node_ref } => TypeContent::Class {
                node_ref,
                has_type_vars: !Class::with_undefined_generics(node_ref)
                    .type_vars(self.inference.i_s)
                    .is_empty(),
            },
            TypeNameLookup::TypeVarLike(type_var_like) => {
                self.has_type_vars_or_self = true;
                match (self.type_var_callback)(
                    self.inference.i_s,
                    &self.type_var_manager,
                    type_var_like.clone(),
                    self.current_callable,
                ) {
                    TypeVarCallbackReturn::TypeVarLike(TypeVarLikeUsage::TypeVar(usage)) => {
                        Some(TypeContent::Type(Type::TypeVar(usage.into_owned())))
                    }
                    TypeVarCallbackReturn::TypeVarLike(TypeVarLikeUsage::TypeVarTuple(usage)) => {
                        Some(TypeContent::TypeVarTuple(usage.into_owned()))
                    }
                    TypeVarCallbackReturn::TypeVarLike(TypeVarLikeUsage::ParamSpec(usage)) => {
                        Some(TypeContent::ParamSpec(usage.into_owned()))
                    }
                    TypeVarCallbackReturn::UnboundTypeVar => {
                        let node_ref = NodeRef::new(self.inference.file, name.index());
                        node_ref.add_issue(
                            self.inference.i_s,
                            IssueType::UnboundTypeVarLike {
                                type_var_like: type_var_like.clone(),
                            },
                        );
                        Some(TypeContent::Unknown(AnyCause::FromError))
                    }
                    TypeVarCallbackReturn::NotFound => None,
                }
                .unwrap_or_else(|| {
                    let index = self.type_var_manager.add(
                        type_var_like.clone(),
                        self.current_callable.filter(|_| {
                            matches!(
                                self.origin,
                                TypeComputationOrigin::ParamTypeCommentOrAnnotation
                                    | TypeComputationOrigin::AssignmentTypeCommentOrAnnotation { .. }
                                    | TypeComputationOrigin::CastTarget
                            )
                        }),
                    );
                    match type_var_like {
                        TypeVarLike::TypeVar(type_var) => {
                            TypeContent::Type(Type::TypeVar(TypeVarUsage {
                                type_var,
                                index,
                                in_definition: self.for_definition,
                            }))
                        }
                        TypeVarLike::TypeVarTuple(type_var_tuple) => {
                            TypeContent::TypeVarTuple(TypeVarTupleUsage {
                                type_var_tuple,
                                index,
                                in_definition: self.for_definition,
                            })
                        }
                        TypeVarLike::ParamSpec(param_spec) => {
                            TypeContent::ParamSpec(ParamSpecUsage {
                                param_spec,
                                index,
                                in_definition: self.for_definition,
                            })
                        }
                    }
                })
            }
            TypeNameLookup::TypeAlias(alias) => TypeContent::TypeAlias(alias),
            TypeNameLookup::NewType(n) => TypeContent::Type(Type::NewType(n)),
            TypeNameLookup::NamedTupleDefinition(n) => TypeContent::NamedTuple(n),
            TypeNameLookup::TypedDictDefinition(t) => TypeContent::TypedDictDefinition(t),
            TypeNameLookup::Enum(t) => TypeContent::Type(Type::Enum(t)),
            TypeNameLookup::Dataclass(d) => TypeContent::Dataclass(d),
            TypeNameLookup::InvalidVariable(t) => TypeContent::InvalidVariable(t),
            TypeNameLookup::Unknown(cause) => TypeContent::Unknown(cause),
            TypeNameLookup::SpecialType(special) => {
                let i_s = self.inference.i_s;
                if matches!(special, SpecialType::Any) && i_s.db.project.flags.disallow_any_explicit
                {
                    self.add_issue(
                        NodeRef::new(self.inference.file, name.index()),
                        IssueType::DisallowedAnyExplicit,
                    )
                }
                TypeContent::SpecialType(special)
            }
            TypeNameLookup::RecursiveAlias(link) => TypeContent::RecursiveAlias(link),
            TypeNameLookup::RecursiveClass(node_ref) => TypeContent::RecursiveClass(node_ref),
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
        self.inference
            .infer_primary(primary, &mut ResultContext::Unknown);
        match details {
            ArgumentsDetails::Node(arguments) => {
                let mut iterator = arguments.iter();
                let name_from_expr = |slf: &mut Self, expr: Expression| {
                    let result = StringSlice::from_string_in_expression(
                        self.inference.file.file_index(),
                        expr,
                    );
                    if result.is_none() && !expr.is_none_literal() {
                        todo!()
                    }
                    result
                };
                let type_from_expr = |slf: &mut Self, expr: Expression| {
                    let t = slf.compute_type(expr);
                    Some(slf.as_type(t, NodeRef::new(self.inference.file, expr.index())))
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
            }
            ArgumentsDetails::Comprehension(comprehension) => {
                todo!()
            }
            ArgumentsDetails::None => {
                if matches!(
                    specific,
                    Specific::MypyExtensionsNamedArg | Specific::MypyExtensionsDefaultNamedArg
                ) {
                    todo!()
                }
            }
        };
        let param_kind = match specific {
            Specific::MypyExtensionsArg | Specific::MypyExtensionsDefaultArg => {
                if name.is_some() {
                    ParamKind::PositionalOrKeyword
                } else {
                    ParamKind::PositionalOnly
                }
            }
            Specific::MypyExtensionsNamedArg => ParamKind::KeywordOnly,
            Specific::MypyExtensionsDefaultNamedArg => ParamKind::KeywordOnly,
            Specific::MypyExtensionsVarArg => ParamKind::Star,
            Specific::MypyExtensionsKwArg => ParamKind::StarStar,
            _ => unreachable!(),
        };
        let type_ = type_.unwrap_or(Type::Any(AnyCause::Todo));
        TypeContent::SpecialType(SpecialType::CallableParam(CallableParam {
            type_: match param_kind {
                ParamKind::PositionalOnly => ParamType::PositionalOnly(type_),
                ParamKind::PositionalOrKeyword => ParamType::PositionalOrKeyword(type_),
                ParamKind::KeywordOnly => ParamType::KeywordOnly(type_),
                ParamKind::Star => ParamType::Star(StarParamType::ArbitraryLength(type_)),
                ParamKind::StarStar => ParamType::StarStar(StarStarParamType::ValueType(type_)),
            },
            name: name.map(|s| s.into()),
            has_default: matches!(
                specific,
                Specific::MypyExtensionsDefaultArg | Specific::MypyExtensionsDefaultNamedArg
            ),
        }))
    }

    pub fn compute_named_tuple_initializer(
        &mut self,
        node_ref: NodeRef,
        list: StarLikeExpressionIterator,
    ) -> Option<Vec<CallableParam>> {
        // From NamedTuple('x', [('a', int)]) to a callable that matches those params

        let file_index = self.inference.file_index;
        let mut params = start_namedtuple_params(self.inference.i_s.db);
        for element in list {
            let StarLikeExpression::NamedExpression(ne) = element else {
                todo!()
            };
            let mut parts = match ne.expression().maybe_unpacked_atom() {
                Some(AtomContent::Tuple(tup)) => tup.iter(),
                _ => {
                    NodeRef::new(self.inference.file, ne.index()).add_issue(
                        self.inference.i_s,
                        IssueType::TupleExpectedAsNamedTupleField,
                    );
                    return None;
                }
            };
            let Some(first) = parts.next() else {
                todo!()
            };
            let Some(second) = parts.next() else {
                todo!()
            };
            let StarLikeExpression::NamedExpression(name_expr) = first else {
                todo!()
            };
            let StarLikeExpression::NamedExpression(type_expr) = second else {
                todo!()
            };
            let Some(name) = StringSlice::from_string_in_expression(file_index, name_expr.expression()) else {
                NodeRef::new(self.inference.file, name_expr.index()).add_issue(
                    self.inference.i_s,
                    IssueType::NamedTupleInvalidFieldName,
                );
                return None
            };
            let name_str = name.as_str(self.inference.i_s.db);
            let t = self.compute_named_expr_type(type_expr);
            params.push(CallableParam {
                type_: ParamType::PositionalOrKeyword(t),
                name: Some(name.into()),
                has_default: false,
            });
        }
        Some(params)
    }

    pub fn into_type_vars<C>(self, on_type_var_recalculation: C) -> TypeVarLikes
    where
        C: FnOnce(&Inference, &dyn Fn(&Type) -> Type),
    {
        if self.type_var_manager.has_late_bound_type_vars() {
            on_type_var_recalculation(self.inference, &|t| {
                t.rewrite_late_bound_callables(&self.type_var_manager)
            })
        }
        self.type_var_manager.into_type_vars()
    }

    fn add_issue(&self, node_ref: NodeRef, issue_type: IssueType) {
        if !self.errors_already_calculated {
            node_ref.add_issue(self.inference.i_s, issue_type)
        }
    }

    fn add_issue_for_index(&self, index: NodeIndex, issue_type: IssueType) {
        self.add_issue(NodeRef::new(self.inference.file, index), issue_type)
    }

    fn add_module_issue(&self, node_ref: NodeRef, qualified_name: &str) {
        self.add_issue(
            node_ref,
            IssueType::InvalidType(
                format!("Module \"{qualified_name}\" is not valid as a type",).into(),
            ),
        );
        self.add_issue(
            node_ref,
            IssueType::Note(Box::from(
                "Perhaps you meant to use a protocol matching the module structure?",
            )),
        );
    }
}

impl<'db: 'x, 'file, 'i_s, 'x> Inference<'db, 'file, 'i_s> {
    pub fn ensure_cached_named_tuple_annotation(&mut self, annotation: Annotation) {
        self.ensure_cached_annotation_internal(annotation, TypeComputationOrigin::NamedTupleMember)
    }

    fn ensure_cached_annotation_internal(
        &mut self,
        annotation: Annotation,
        origin: TypeComputationOrigin,
    ) {
        if !self.file.points.get(annotation.index()).calculated() {
            let mut x = type_computation_for_variable_annotation;
            let mut comp = TypeComputation::new(
                self,
                PointLink::new(self.file_index, annotation.index()),
                &mut x,
                origin,
            );
            comp.cache_annotation(annotation, false);
            comp.into_type_vars(|inf, recalculate_type_vars| {
                inf.recalculate_annotation_type_vars(annotation.index(), recalculate_type_vars);
            });
        }
    }

    pub fn ensure_cached_annotation(&mut self, annotation: Annotation, is_initialized: bool) {
        self.ensure_cached_annotation_internal(
            annotation,
            TypeComputationOrigin::AssignmentTypeCommentOrAnnotation { is_initialized },
        )
    }

    pub fn compute_type_application_on_class(
        &mut self,
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
        &mut self,
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
        &mut self,
        named_tuple: Rc<NamedTuple>,
        slice_type: SliceType,
        from_alias_definition: bool,
    ) -> Inferred {
        compute_type_application!(
            self,
            slice_type,
            from_alias_definition,
            compute_type_get_item_on_named_tuple(named_tuple, slice_type, None)
        )
    }

    pub fn compute_type_application_on_typed_dict(
        &mut self,
        typed_dict: &TypedDict,
        slice_type: SliceType,
        from_alias_definition: bool,
    ) -> Inferred {
        compute_type_application!(
            self,
            slice_type,
            from_alias_definition,
            compute_type_get_item_on_typed_dict(typed_dict, slice_type, None)
        )
    }

    pub fn compute_type_application_on_alias(
        &mut self,
        alias: &TypeAlias,
        slice_type: SliceType,
        from_alias_definition: bool,
    ) -> Inferred {
        if !from_alias_definition && !alias.application_allowed() {
            slice_type
                .as_node_ref()
                .add_issue(self.i_s, IssueType::OnlyClassTypeApplication);
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
        &mut self,
        specific: Specific,
        slice_type: SliceType,
        from_alias_definition: bool,
    ) -> Inferred {
        match specific {
            Specific::TypingGeneric | Specific::TypingProtocol => {
                todo!()
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
            Specific::TypingType => {
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
            _ => unreachable!("{:?}", specific),
        }
    }

    pub(super) fn use_cached_annotation(&mut self, annotation: Annotation) -> Inferred {
        let point = self.file.points.get(annotation.index());
        debug_assert!(matches!(
            point.specific(),
            Specific::AnnotationOrTypeCommentWithTypeVars
                | Specific::AnnotationOrTypeCommentWithoutTypeVars
                | Specific::AnnotationOrTypeCommentSimpleClassInstance
                | Specific::AnnotationOrTypeCommentClassVar
        ));
        self.check_point_cache(annotation.index()).unwrap()
    }

    pub fn use_cached_return_annotation(&mut self, annotation: ReturnAnnotation) -> Inferred {
        debug_assert!(matches!(
            self.file.points.get(annotation.index()).specific(),
            Specific::AnnotationOrTypeCommentWithTypeVars
                | Specific::AnnotationOrTypeCommentWithoutTypeVars
                | Specific::AnnotationOrTypeCommentSimpleClassInstance
        ));
        self.check_point_cache(annotation.index()).unwrap()
    }

    pub fn use_cached_return_annotation_type(
        &mut self,
        annotation: ReturnAnnotation,
    ) -> Cow<'file, Type> {
        self.use_cached_annotation_or_type_comment_type_internal(
            annotation.index(),
            annotation.expression(),
        )
    }

    pub fn use_cached_annotation_type(&mut self, annotation: Annotation) -> Cow<'file, Type> {
        self.use_cached_annotation_or_type_comment_type_internal(
            annotation.index(),
            annotation.expression(),
        )
    }

    fn use_cached_annotation_or_type_comment_type_internal(
        &mut self,
        annotation_index: NodeIndex,
        expr: Expression,
    ) -> Cow<'file, Type> {
        let point = self.file.points.get(annotation_index);
        assert!(point.calculated(), "Expr: {:?}", expr);
        match point.specific() {
            Specific::AnnotationOrTypeCommentSimpleClassInstance => self
                .infer_expression(expr)
                .expect_class_or_simple_generic(self.i_s),
            Specific::TypingFinal => todo!(),
            _ => {
                debug_assert!(matches!(
                    point.specific(),
                    Specific::AnnotationOrTypeCommentWithTypeVars
                        | Specific::AnnotationOrTypeCommentWithoutTypeVars
                        | Specific::AnnotationOrTypeCommentClassVar
                ));
                let complex_index = self.file.points.get(expr.index()).complex_index();
                match self.file.complex_points.get(complex_index) {
                    ComplexPoint::TypeInstance(t) => Cow::Borrowed(t),
                    _ => unreachable!(),
                }
            }
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

    fn compute_type_assignment(
        &mut self,
        assignment: Assignment<'x>,
        is_explicit: bool,
    ) -> TypeNameLookup<'file, 'file> {
        // Use the node star_targets or single_target, because they are not used otherwise.
        let file = self.file;
        let cached_type_node_ref = assignment_type_node_ref(self.file, assignment);
        let point = cached_type_node_ref.point();
        if point.calculated() {
            return load_cached_type(cached_type_node_ref);
        }
        // It is a little bit special that at this point we can have point.calculating(), but this
        // is due to weird alias recursions where an alias is inferred normally and the type
        // computation is kind of invoked as a type application. So in some very weird and
        // recursive cases the calculation is done twice.

        if let Some(name) = assignment.maybe_simple_type_reassignment() {
            // For very simple cases like `Foo = int`. Not sure yet if this going to stay.

            match self
                .infer_name_reference(name)
                .maybe_saved_specific(self.i_s.db)
            {
                Some(Specific::TypingAny) => {
                    // This is a bit of a weird special case that was necessary to pass the test
                    // testDisallowAnyExplicitAlias
                    if self.i_s.db.project.flags.disallow_any_explicit {
                        NodeRef::new(file, name.index())
                            .add_issue(self.i_s, IssueType::DisallowedAnyExplicit)
                    }
                }
                _ => {
                    let node_ref = NodeRef::new(file, name.index());
                    debug_assert!(node_ref.point().calculated());
                    return check_type_name(self.i_s, node_ref);
                }
            }
        }
        if let Some((name_def, annotation, expr)) =
            assignment.maybe_simple_type_expression_assignment()
        {
            debug!("Started type alias calculation: {}", name_def.as_code());
            if let Some(type_comment) = self.check_for_type_comment(assignment) {
                // This case is a bit weird in Mypy, but it makes it possible to use a type
                // definition like:
                //
                //     Foo = 1  # type: Any
                if let Type::Any(cause) = type_comment.type_.as_ref() {
                    return TypeNameLookup::Unknown(*cause);
                }
            }
            if !is_explicit
                && (expr.maybe_single_string_literal().is_some() || annotation.is_some())
            {
                return TypeNameLookup::InvalidVariable(InvalidVariableType::Variable(
                    NodeRef::new(file, name_def.index()),
                ));
            }
            debug_assert!(file.points.get(name_def.index()).calculated() || annotation.is_some());

            let check_for_alias = |self_: &mut Inference| {
                cached_type_node_ref.set_point(Point::new_calculating());
                let type_var_likes =
                    TypeVarFinder::find_alias_type_vars(self_.i_s, self.file, expr);

                let in_definition = cached_type_node_ref.as_link();
                let alias = TypeAlias::new(
                    type_var_likes,
                    in_definition,
                    Some(PointLink::new(file.file_index(), name_def.name().index())),
                );
                save_alias(cached_type_node_ref, alias);

                let mut type_var_manager = TypeVarManager::default();
                let mut type_var_callback =
                    |_: &InferenceState, _: &_, type_var_like: TypeVarLike, _| {
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
                let p = file.points.get(expr.index());
                let mut comp = TypeComputation::new(
                    self_,
                    in_definition,
                    &mut type_var_callback,
                    TypeComputationOrigin::TypeAlias,
                );
                comp.errors_already_calculated = p.calculated();
                let t = comp.compute_type(expr);
                let ComplexPoint::TypeAlias(alias) = cached_type_node_ref.complex().unwrap() else {
                    unreachable!()
                };
                let node_ref = NodeRef::new(file, expr.index());
                match t {
                    TypeContent::InvalidVariable(t) if !is_explicit => {
                        alias.set_invalid();
                    }
                    _ => {
                        let type_ = comp.as_type(t, node_ref);
                        let is_recursive_alias = comp.is_recursive_alias;
                        debug_assert!(!comp.type_var_manager.has_type_vars());
                        let mut had_error = false;
                        if is_recursive_alias && self.i_s.current_function().is_some() {
                            node_ref.add_issue(
                                self.i_s,
                                IssueType::RecursiveTypesNotAllowedInFunctionScope {
                                    alias_name: name_def.as_code().into(),
                                },
                            );
                            had_error = true;
                        }
                        if is_invalid_recursive_alias(self.i_s.db, &type_) {
                            node_ref.add_issue(
                                self.i_s,
                                IssueType::InvalidRecursiveTypeAliasUnionOfItself {
                                    target: "union",
                                },
                            );
                            had_error = true;
                        }
                        // This is called detect_diverging_alias in Mypy as well.
                        if detect_diverging_alias(self.i_s.db, &alias.type_vars, &type_) {
                            node_ref.add_issue(
                                self.i_s,
                                IssueType::InvalidRecursiveTypeAliasTypeVarNesting,
                            );
                            had_error = true;
                        }
                        if had_error {
                            alias.set_valid(Type::Any(AnyCause::FromError), false);
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
                debug!(
                    "Alias {:?} on #{} is valid? {}",
                    assignment.as_code(),
                    node_ref.line(),
                    alias.is_valid()
                );
                load_cached_type(cached_type_node_ref)
            };

            if is_explicit {
                return check_for_alias(self);
            }

            let inferred = self.check_point_cache(name_def.index()).unwrap();
            let result = if let Some(tv) = inferred.maybe_type_var_like(self.i_s) {
                TypeNameLookup::TypeVarLike(tv)
            } else if let Some(n) = inferred.maybe_new_type(self.i_s) {
                TypeNameLookup::NewType(n)
            } else if let Some(t) = inferred.maybe_named_tuple_definition(self.i_s) {
                let Type::NamedTuple(nt) = t else { unreachable!() };
                TypeNameLookup::NamedTupleDefinition(nt)
            } else if let Some(t) = inferred.maybe_typed_dict_definition(self.i_s) {
                TypeNameLookup::TypedDictDefinition(t)
            } else if let Some(t) = inferred.maybe_enum_definition(self.i_s) {
                TypeNameLookup::Enum(t)
            } else {
                check_for_alias(self)
            };
            debug!("Finished type alias calculation: {}", name_def.as_code());
            result
        } else {
            if let Some(annotation) = assignment.maybe_annotation() {
                self.cache_assignment_nodes(assignment);
                if let Type::Any(cause) = self.use_cached_annotation_type(annotation).as_ref() {
                    return TypeNameLookup::Unknown(*cause);
                }
            }
            TypeNameLookup::InvalidVariable(InvalidVariableType::Other)
        }
    }

    pub(super) fn compute_explicit_type_assignment(&mut self, assignment: Assignment) -> Inferred {
        self.compute_type_assignment(assignment, true);
        Inferred::from_saved_node_ref(assignment_type_node_ref(self.file, assignment))
    }

    pub(super) fn lookup_type_name(&mut self, name: Name<'x>) -> TypeNameLookup<'db, 'x> {
        let point = self.file.points.get(name.index());
        debug_assert!(self.file.points.get(name.index()).calculated());
        match point.type_() {
            PointType::Specific => match point.specific() {
                Specific::AnyDueToError => TypeNameLookup::Unknown(AnyCause::Todo),
                _ => todo!(),
            },
            PointType::Redirect => {
                check_type_name(self.i_s, point.as_redirected_node_ref(self.i_s.db))
            }
            PointType::FileReference => {
                let file = self.i_s.db.loaded_python_file(point.file_index());
                TypeNameLookup::Module(file)
            }
            _ => todo!("{point:?}"),
        }
    }

    pub(super) fn compute_type_comment(
        &mut self,
        start: CodeIndex,
        s: &str,
        assignment_node_ref: NodeRef,
    ) -> TypeCommentDetails<'db> {
        let f: &'db PythonFile =
            self.file
                .new_annotation_file(self.i_s.db, start, s.trim_end_matches('\\').into());
        let mut inference = f.inference(self.i_s);
        if let Some(star_exprs) = f.tree.maybe_star_expressions() {
            match star_exprs.unpack() {
                StarExpressionContent::Expression(expr) => {
                    // It is kind of a hack to use the ANNOTATION_TO_EXPR_DIFFERENCE here. However this
                    // allows us to reuse the code for annotations completely and the nodes before the expr
                    // should really never be used by anything productive.
                    let expr_index = expr.index();
                    let index = expr_index - ANNOTATION_TO_EXPR_DIFFERENCE;
                    if let Some(tuple) = expr.maybe_tuple() {
                        let type_ =
                            inference.calc_type_comment_tuple(assignment_node_ref, tuple.iter());
                        NodeRef::new(f, index).set_point(Point::new_simple_specific(
                            Specific::AnnotationOrTypeCommentWithTypeVars,
                            Locality::Todo,
                        ));
                        NodeRef::new(f, expr_index)
                            .insert_complex(ComplexPoint::TypeInstance(type_), Locality::Todo);
                    } else {
                        let mut x = type_computation_for_variable_annotation;
                        let mut comp = TypeComputation::new(
                            &mut inference,
                            assignment_node_ref.as_link(),
                            &mut x,
                            TypeComputationOrigin::AssignmentTypeCommentOrAnnotation {
                                is_initialized: true,
                            },
                        );
                        comp.cache_annotation_or_type_comment(index, expr, false, None);
                        let type_vars = comp.into_type_vars(|inf, recalculate_type_vars| {
                            inf.recalculate_annotation_type_vars(index, recalculate_type_vars);
                        });
                        debug_assert!(type_vars.is_empty());
                    }
                    TypeCommentDetails {
                        inferred: Inferred::from_saved_node_ref(NodeRef::new(f, index)),
                        type_: inference
                            .use_cached_annotation_or_type_comment_type_internal(index, expr),
                    }
                }
                StarExpressionContent::Tuple(t) => {
                    let star_exprs_index = star_exprs.index();
                    let index = star_exprs_index - ANNOTATION_TO_EXPR_DIFFERENCE;
                    let type_ = inference.calc_type_comment_tuple(assignment_node_ref, t.iter());
                    NodeRef::new(f, index)
                        .insert_complex(ComplexPoint::TypeInstance(type_), Locality::Todo);
                    let complex_index = f.points.get(index).complex_index();
                    TypeCommentDetails {
                        inferred: Inferred::from_saved_node_ref(NodeRef::new(f, index)),
                        type_: if let ComplexPoint::TypeInstance(type_) =
                            f.complex_points.get(complex_index)
                        {
                            Cow::Borrowed(type_)
                        } else {
                            unreachable!()
                        },
                    }
                }
                StarExpressionContent::StarExpression(s) => todo!(),
            }
        } else {
            for stmt_or_error in f.tree.root().iter_stmts() {
                if let StmtOrError::Error(node_index) = stmt_or_error {
                    return TypeCommentDetails {
                        inferred: Inferred::new_any_from_error(),
                        type_: Cow::Borrowed(&Type::Any(AnyCause::FromError)),
                    };
                }
            }
            debug!("Found non-expression in annotation: {}", f.tree.code());
            self.file.add_issue(
                self.i_s,
                Issue {
                    start_position: start,
                    end_position: start + s.len() as CodeIndex,
                    type_: IssueType::InvalidSyntaxInTypeComment {
                        type_comment: s.trim().into(),
                    },
                },
            );
            return TypeCommentDetails {
                inferred: Inferred::new_any_from_error(),
                type_: Cow::Borrowed(&Type::Any(AnyCause::FromError)),
            };
        }
    }

    fn calc_type_comment_tuple<'s>(
        &mut self,
        assignment_node_ref: NodeRef,
        iterator: impl Iterator<Item = StarLikeExpression<'s>>,
    ) -> Type {
        let generics = iterator
            .map(|star_like| {
                let expr = match star_like {
                    StarLikeExpression::NamedExpression(named_expr) => named_expr.expression(),
                    StarLikeExpression::Expression(expr) => expr,
                    StarLikeExpression::StarNamedExpression(x) => todo!("{x:?}"),
                    StarLikeExpression::StarExpression(x) => todo!("{x:?}"),
                };
                if let Some(tuple) = expr.maybe_tuple() {
                    self.calc_type_comment_tuple(assignment_node_ref, tuple.iter())
                } else {
                    let expr_node_ref = NodeRef::new(self.file, expr.index());
                    let mut x = type_computation_for_variable_annotation;
                    let mut comp = TypeComputation::new(
                        self,
                        assignment_node_ref.as_link(),
                        &mut x,
                        TypeComputationOrigin::AssignmentTypeCommentOrAnnotation {
                            is_initialized: true,
                        },
                    );
                    let t = comp.compute_type(expr);
                    let mut type_ = comp.as_type(t, expr_node_ref);
                    let type_vars = comp.into_type_vars(|inf, recalculate_type_vars| {
                        type_ = recalculate_type_vars(&type_);
                    });
                    debug_assert!(type_vars.is_empty());
                    type_
                }
            })
            .collect();
        Type::Tuple(Rc::new(Tuple::new_fixed_length(generics)))
    }

    pub fn check_for_type_comment(
        &mut self,
        assignment: Assignment,
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
    pub fn compute_cast_target(&mut self, node_ref: NodeRef) -> Result<Inferred, ()> {
        let named_expr = node_ref.as_named_expression();
        let mut x = type_computation_for_variable_annotation;
        let mut comp = TypeComputation::new(
            self,
            node_ref.as_link(),
            &mut x,
            TypeComputationOrigin::CastTarget,
        );

        let t = comp.compute_type(named_expr.expression());
        let Some(mut type_) = comp.as_type_or_error(t, node_ref) else {
            return Err(())
        };
        let type_vars = comp.into_type_vars(|inf, recalculate_type_vars| {
            type_ = recalculate_type_vars(&type_);
        });
        debug_assert!(type_vars.is_empty());
        Ok(Inferred::from_type(type_))
    }

    pub fn compute_class_typed_dict_member(
        &mut self,
        name: StringSlice,
        annotation: Annotation,
        total: bool,
    ) -> TypedDictMember {
        let mut x = type_computation_for_variable_annotation;
        let mut comp = TypeComputation::new(
            self,
            NodeRef::new(self.file, annotation.index()).as_link(),
            &mut x,
            TypeComputationOrigin::TypedDictMember,
        );

        let mut member = comp.compute_typed_dict_member(name, annotation.expression(), total);
        let type_vars = comp.into_type_vars(|inf, recalculate_type_vars| {
            member.type_ = recalculate_type_vars(&member.type_);
        });
        debug_assert!(type_vars.is_empty());
        member
    }

    pub fn compute_type_var_constraint(&mut self, expr: Expression) -> Option<Type> {
        let mut on_type_var =
            |i_s: &InferenceState, _: &_, type_var_like: TypeVarLike, current_callable| {
                if let Some(class) = i_s.current_class() {
                    for (i, tvl) in class.type_vars(i_s).iter().enumerate() {
                        if type_var_like == *tvl {
                            return TypeVarCallbackReturn::TypeVarLike(
                                tvl.as_type_var_like_usage(i.into(), class.node_ref.as_link()),
                            );
                        }
                    }
                }
                todo!()
            };
        let node_ref = NodeRef::new(self.file, expr.index());
        let mut comp = TypeComputation::new(
            self,
            node_ref.as_link(),
            &mut on_type_var,
            TypeComputationOrigin::Constraint,
        );
        let t = comp.compute_type(expr);
        match t {
            TypeContent::InvalidVariable(invalid @ InvalidVariableType::Literal(_)) => {
                invalid.add_issue(
                    comp.inference.i_s.db,
                    |t| node_ref.add_issue(comp.inference.i_s, t),
                    comp.origin,
                );
                None
            }
            TypeContent::InvalidVariable(_) => {
                // TODO this is a bit weird and should probably generate other errors
                node_ref.add_issue(comp.inference.i_s, IssueType::TypeVarTypeExpected);
                None
            }
            _ => Some(comp.as_type(t, node_ref)),
        }
    }

    pub fn compute_new_type_constraint(&mut self, expr: Expression) -> Type {
        let mut x = type_computation_for_variable_annotation;
        let node_ref = NodeRef::new(self.file, expr.index());
        let mut comp = TypeComputation::new(
            self,
            node_ref.as_link(),
            &mut x,
            TypeComputationOrigin::Constraint,
        );
        match comp.compute_type(expr) {
            TypeContent::InvalidVariable(_) => {
                node_ref.add_issue(self.i_s, IssueType::NewTypeInvalidType);
                Type::Any(AnyCause::FromError)
            }
            t => {
                let t = comp.as_type(t, node_ref);
                if !t.is_subclassable(self.i_s.db) {
                    node_ref.add_issue(
                        self.i_s,
                        IssueType::NewTypeMustBeSubclassable {
                            got: t.format_short(self.i_s.db),
                        },
                    );
                }
                if t.maybe_class(self.i_s.db)
                    .is_some_and(|cls| cls.is_protocol(self.i_s.db))
                {
                    node_ref.add_issue(self.i_s, IssueType::NewTypeCannotUseProtocols);
                }
                t
            }
        }
    }
}

fn is_invalid_recursive_alias(db: &Database, t: &Type) -> bool {
    t.iter_with_unpacked_unions().any(|t| matches!(t, Type::RecursiveType(rec) if rec.has_alias_origin(db) && rec.calculating(db)))
}

fn detect_diverging_alias(db: &Database, type_var_likes: &TypeVarLikes, t: &Type) -> bool {
    !type_var_likes.is_empty()
        && t.find_in_type(&|t| match t {
            Type::RecursiveType(rec) if rec.has_alias_origin(db) && rec.generics.is_some() => {
                if rec.calculating(db) {
                    rec.generics.as_ref().is_some_and(|generics| {
                        let has_direct_type_var_like = generics.iter().any(|g| match g {
                            GenericItem::TypeArgument(t) => matches!(t, Type::TypeVar(_)),
                            GenericItem::TypeArguments(ts) => todo!(),
                            GenericItem::ParamSpecArgument(p) => {
                                matches!(p.params, CallableParams::WithParamSpec(_, _))
                            }
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
    if alias.type_if_valid().find_in_type(&|t| match t {
        Type::Type(t) => t.iter_with_unpacked_unions().any(|t| match t {
            Type::RecursiveType(recursive_alias) => {
                !recursive_alias.calculating(i_s.db)
                    && recursive_alias.has_alias_origin(i_s.db)
                    && recursive_alias
                        .calculated_type(i_s.db)
                        .iter_with_unpacked_unions()
                        .any(|t| matches!(t, Type::Type(_)))
            }
            _ => false,
        }),
        _ => false,
    }) {
        alias_origin.add_issue(i_s, IssueType::TypeCannotContainAnotherType);
        let alias = TypeAlias::new(alias.type_vars.clone(), alias.location, alias.name);
        alias.set_valid(Type::Any(AnyCause::FromError), false);
        save_alias(alias_origin, alias)
    }
}

fn save_alias(alias_origin: NodeRef, alias: TypeAlias) {
    let complex = ComplexPoint::TypeAlias(Box::new(alias));
    alias_origin.insert_complex(complex, Locality::Todo);
}

pub(super) fn assignment_type_node_ref<'x>(
    file: &'x PythonFile,
    assignment: Assignment,
) -> NodeRef<'x> {
    NodeRef::new(file, assignment.index() + ASSIGNMENT_TYPE_CACHE_OFFSET)
}

#[inline]
fn check_special_type(point: Point) -> Option<SpecialType> {
    if point.type_() == PointType::Specific {
        Some(match point.specific() {
            Specific::TypingUnion => SpecialType::Union,
            Specific::TypingOptional => SpecialType::Optional,
            Specific::TypingAny => SpecialType::Any,
            Specific::TypingGeneric => SpecialType::Generic,
            Specific::TypingProtocol => SpecialType::Protocol,
            Specific::TypingType => SpecialType::Type,
            Specific::TypingCallable => SpecialType::Callable,
            Specific::TypingLiteralString => SpecialType::LiteralString,
            Specific::TypingUnpack => SpecialType::Unpack,
            Specific::TypingConcatenateClass => SpecialType::Concatenate,
            Specific::TypingTypeAlias => SpecialType::TypeAlias,
            Specific::TypingLiteral => SpecialType::Literal,
            Specific::TypingFinal => SpecialType::Final,
            Specific::TypingSelf => SpecialType::Self_,
            Specific::TypingAnnotated => SpecialType::Annotated,
            Specific::TypingTuple => SpecialType::Tuple,
            Specific::TypingTypedDict => SpecialType::TypingTypedDict,
            Specific::TypingRequired => SpecialType::Required,
            Specific::TypingNotRequired => SpecialType::NotRequired,
            Specific::TypingClassVar => SpecialType::ClassVar,
            Specific::TypingNamedTuple => SpecialType::TypingNamedTuple,
            Specific::MypyExtensionsArg
            | Specific::MypyExtensionsDefaultArg
            | Specific::MypyExtensionsNamedArg
            | Specific::MypyExtensionsDefaultNamedArg
            | Specific::MypyExtensionsVarArg
            | Specific::MypyExtensionsKwArg => {
                SpecialType::MypyExtensionsParamType(point.specific())
            }
            _ => return None,
        })
    } else {
        None
    }
}

fn load_cached_type(node_ref: NodeRef) -> TypeNameLookup {
    if let Some(complex) = node_ref.complex() {
        match complex {
            ComplexPoint::TypeAlias(a) => {
                if a.calculating() {
                    // This means it's a recursive type definition.
                    TypeNameLookup::RecursiveAlias(node_ref.as_link())
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
                    TypeNameLookup::InvalidVariable(InvalidVariableType::Variable(NodeRef::new(
                        node_ref.file,
                        name_def.index(),
                    )))
                } else {
                    TypeNameLookup::TypeAlias(a)
                }
            }
            ComplexPoint::TypeVarLike(t) => TypeNameLookup::TypeVarLike(t.clone()),
            _ => unreachable!("{complex:?}"),
        }
    } else {
        let point = node_ref.point();
        if point.type_() == PointType::MultiDefinition {
            debug!("TODO check if this is the right place for this kind of stuff.");
            TypeNameLookup::InvalidVariable(InvalidVariableType::Variable(node_ref))
        } else {
            TypeNameLookup::SpecialType(
                check_special_type(point).unwrap_or_else(|| todo!("{point:?}")),
            )
        }
    }
}

pub(super) fn check_type_name<'db: 'file, 'file>(
    i_s: &InferenceState<'db, '_>,
    name_node_ref: NodeRef<'file>,
) -> TypeNameLookup<'file, 'file> {
    let point = name_node_ref.point();
    // First check redirects. These are probably one of the following cases:
    //
    // 1. imports
    // 2. Typeshed Aliases (special cases, see python_state.rs)
    // 3. Maybe simple assignments like `Foo = str`, though I'm not sure.
    //
    // It's important to check that it's a name. Otherwise it redirects to some random place.
    if point.calculated() {
        if point.type_() == PointType::Redirect {
            let new = point.as_redirected_node_ref(i_s.db);
            if new.maybe_name().is_some() {
                return check_type_name(i_s, new);
            }
        } else if point.type_() == PointType::FileReference {
            let file = i_s.db.loaded_python_file(point.file_index());
            return TypeNameLookup::Module(file);
        }

        if let Some(special) = check_special_type(point) {
            return TypeNameLookup::SpecialType(special);
        }
    }

    let new_name = name_node_ref.as_name();
    match new_name.expect_type() {
        TypeLike::ClassDef(c) => {
            let point = name_node_ref.point();
            if point.calculated() {
                if let Some(specific) = point.maybe_specific() {
                    debug!(
                        "Found an unexpected specific {specific:?} for {}",
                        new_name.as_code()
                    );
                    return TypeNameLookup::InvalidVariable(InvalidVariableType::Variable(
                        name_node_ref,
                    ));
                }
            }
            // At this point the class is not necessarily calculated and we therefore do this here.
            let name_def = NodeRef::new(
                name_node_ref.file,
                new_name.name_definition().unwrap().index(),
            );
            let from = NodeRef::new(name_node_ref.file, c.index());
            let class = Class::with_undefined_generics(from);
            if class.is_calculating_class_infos() {
                return TypeNameLookup::RecursiveClass(from);
            }

            name_def.file.inference(i_s).cache_class(name_def, c);
            match name_def.complex() {
                Some(ComplexPoint::TypeInstance(Type::Type(t))) => match t.as_ref() {
                    Type::Dataclass(d) => return TypeNameLookup::Dataclass(d.clone()),
                    Type::Enum(e) => return TypeNameLookup::Enum(e.clone()),
                    _ => (),
                },
                Some(ComplexPoint::TypedDictDefinition(t)) => match t.type_.as_ref() {
                    Type::TypedDict(td) => {
                        if td.calculating() {
                            return TypeNameLookup::RecursiveClass(NodeRef::from_link(
                                i_s.db,
                                td.defined_at,
                            ));
                        } else {
                            return TypeNameLookup::TypedDictDefinition(td.clone());
                        }
                    }
                    _ => unreachable!(),
                },
                _ => (),
            }
            TypeNameLookup::Class {
                node_ref: NodeRef::new(name_node_ref.file, c.index()),
            }
        }
        TypeLike::Assignment(assignment) => {
            let def_point = name_node_ref
                .file
                .points
                .get(new_name.name_definition().unwrap().index());
            let mut inference = name_node_ref.file.inference(i_s);
            if !def_point.calculated() || def_point.maybe_specific() != Some(Specific::Cycle) {
                inference.cache_assignment_nodes(assignment);
            }
            inference.compute_type_assignment(assignment, false)
        }
        TypeLike::Function(f) => TypeNameLookup::InvalidVariable(InvalidVariableType::Function({
            let name_def_ref =
                name_node_ref.add_to_node_index(-(NAME_DEF_TO_NAME_DIFFERENCE as i64));
            if let Some(special) = check_special_type(name_def_ref.point()) {
                return TypeNameLookup::SpecialType(special);
            }
            let point = name_node_ref.point();
            if point.calculated() && point.maybe_specific() == Some(Specific::CollectionsNamedTuple)
            {
                return TypeNameLookup::SpecialType(SpecialType::CollectionsNamedTuple);
            }
            Function::new(NodeRef::new(name_node_ref.file, f.index()), None)
        })),
        TypeLike::ImportFromAsName(_) | TypeLike::DottedAsName(_) => {
            let name_def_ref =
                name_node_ref.add_to_node_index(-(NAME_DEF_TO_NAME_DIFFERENCE as i64));
            let p = name_def_ref.point();
            if p.calculated() {
                if p.type_() == PointType::Redirect {
                    let new = p.as_redirected_node_ref(i_s.db);
                    if new.maybe_name().is_some() {
                        return check_type_name(i_s, new);
                    }
                } else if p.type_() == PointType::FileReference {
                    let file = i_s.db.loaded_python_file(p.file_index());
                    return TypeNameLookup::Module(file);
                }

                // When an import appears, this means that there's no redirect and the import leads
                // nowhere.
                if let Some(complex_index) = p.maybe_complex_index() {
                    if let ComplexPoint::TypeInstance(Type::Namespace(namespace)) =
                        name_def_ref.file.complex_points.get(complex_index)
                    {
                        return TypeNameLookup::Namespace(namespace.clone());
                    }
                }
                if p.maybe_specific() == Some(Specific::ModuleNotFound) {
                    TypeNameLookup::Unknown(AnyCause::ModuleNotFound)
                } else {
                    // This typically happens with a module __getattr__ and the type can be
                    // anything.
                    check_module_getattr_type(
                        i_s,
                        name_def_ref
                            .file
                            .inference(i_s)
                            .check_point_cache(name_def_ref.node_index)
                            .unwrap(),
                    )
                }
            } else {
                name_node_ref.file.inference(i_s).infer_name(new_name);
                check_type_name(i_s, name_node_ref)
            }
        }
        TypeLike::ParamName(annotation) => TypeNameLookup::InvalidVariable({
            let as_base_class_any = annotation
                .map(
                    |a| match use_cached_annotation_type(i_s.db, name_node_ref.file, a).as_ref() {
                        Type::Any(_) => true,
                        Type::Type(t) => match t.as_ref() {
                            Type::Any(_) => true,
                            Type::Class(GenericClass {
                                link,
                                generics: ClassGenerics::None,
                            }) => *link == i_s.db.python_state.object_node_ref().as_link(),
                            _ => false,
                        },
                        _ => false,
                    },
                )
                .unwrap_or(true);
            if as_base_class_any {
                InvalidVariableType::ParamNameAsBaseClassAny(name_node_ref)
            } else {
                InvalidVariableType::Variable(name_node_ref)
            }
        }),
        TypeLike::Other => {
            todo!()
        }
    }
}

pub(super) fn cache_name_on_class(cls: Class, file: &PythonFile, name: Name) -> PointType {
    // This is needed to lookup names on a class and set the redirect there. It does not modify the
    // class at all.
    let name_node_ref = NodeRef::new(file, name.index());
    let point = name_node_ref.point();
    if point.calculated() {
        return point.type_();
    }
    name_node_ref.set_point(
        if let Some(index) = cls
            .class_storage
            .class_symbol_table
            .lookup_symbol(name.as_str())
        {
            Point::new_redirect(cls.node_ref.file.file_index(), index, Locality::Todo)
        } else {
            Point::new_simple_specific(Specific::AnyDueToError, Locality::Todo)
        },
    );
    cache_name_on_class(cls, file, name)
}

fn check_module_getattr_type(
    i_s: &InferenceState,
    inf: Inferred,
) -> TypeNameLookup<'static, 'static> {
    if let Type::Any(cause) = inf.as_cow_type(i_s).as_ref() {
        TypeNameLookup::Unknown(*cause)
    } else {
        todo!()
    }
}

pub fn use_cached_simple_generic_type<'db>(
    db: &'db Database,
    file: &PythonFile,
    expr: Expression,
) -> Cow<'db, Type> {
    // The context of inference state is not important, because this is only a simple generic type.
    let i_s = &InferenceState::new(db);
    let mut inference = file.inference(i_s);
    debug_assert_eq!(
        inference.file.points.get(expr.index()).type_(),
        PointType::Redirect
    );
    let inferred = inference.check_point_cache(expr.index()).unwrap();
    inferred.expect_class_or_simple_generic(i_s)
}

pub fn use_cached_annotation_type<'db: 'file, 'file>(
    db: &'db Database,
    file: &'file PythonFile,
    annotation: Annotation,
) -> Cow<'file, Type> {
    file.inference(&InferenceState::new(db))
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
    ));
    definition
        .file
        .inference(i_s)
        .use_cached_annotation_or_type_comment_type_internal(
            definition.node_index,
            definition
                .add_to_node_index(ANNOTATION_TO_EXPR_DIFFERENCE as i64)
                .as_expression(),
        )
}

pub fn maybe_saved_annotation(node_ref: NodeRef) -> Option<&Type> {
    if matches!(
        node_ref.point().maybe_specific(),
        Some(
            Specific::AnnotationOrTypeCommentWithTypeVars
                | Specific::AnnotationOrTypeCommentWithoutTypeVars
                | Specific::AnnotationOrTypeCommentClassVar
        )
    ) {
        let Some(ComplexPoint::TypeInstance(t)) = node_ref
            .add_to_node_index(ANNOTATION_TO_EXPR_DIFFERENCE as i64)
            .complex() else {
            unreachable!()
        };
        return Some(t);
    }
    None
}

pub struct TypeCommentDetails<'db> {
    pub type_: Cow<'db, Type>,
    pub inferred: Inferred,
}
