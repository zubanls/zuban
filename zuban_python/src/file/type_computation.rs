use std::rc::Rc;

use parsa_python_ast::SliceType as ASTSliceType;
use parsa_python_ast::*;

use super::TypeVarFinder;
use crate::arguments::{ArgumentIterator, ArgumentKind, Arguments, SimpleArguments};
use crate::database::{
    CallableContent, CallableParam, CallableParams, CallableWithParent, ClassGenerics,
    ComplexPoint, Database, DbString, DbType, DoubleStarredParamSpecific, Enum, EnumMember,
    FunctionKind, GenericClass, GenericItem, GenericsList, Literal, LiteralKind, Locality,
    NamedTuple, Namespace, NewType, ParamSpecArgument, ParamSpecUsage, ParamSpecific, Point,
    PointLink, PointType, RecursiveAlias, Specific, StarredParamSpecific, StringSlice,
    TupleContent, TypeAlias, TypeArguments, TypeOrTypeVarTuple, TypeVar, TypeVarKind, TypeVarLike,
    TypeVarLikeUsage, TypeVarLikes, TypeVarManager, TypeVarTupleUsage, TypeVarUsage, UnionEntry,
    UnionType,
};
use crate::debug;
use crate::diagnostics::{Issue, IssueType};
use crate::file::File;
use crate::file::{Inference, PythonFile};
use crate::getitem::{SliceOrSimple, SliceType, SliceTypeIterator};
use crate::imports::{python_import, ImportResult};
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::matching::{FormatData, Generics, ResultContext, Type};
use crate::node_ref::NodeRef;
use crate::type_helpers::{start_namedtuple_params, Class, Function, Module};

pub(super) const ASSIGNMENT_TYPE_CACHE_OFFSET: u32 = 1;
const ANNOTATION_TO_EXPR_DIFFERENCE: u32 = 2;

#[derive(Debug)]
pub enum TypeVarCallbackReturn {
    TypeVarLike(TypeVarLikeUsage<'static>),
    UnboundTypeVar,
    NotFound,
}

type MapAnnotationTypeCallback<'a> =
    Option<&'a dyn Fn(&mut TypeComputation, TypeContent) -> DbType>;

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
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum TypeComputationOrigin {
    AssignmentTypeCommentOrAnnotation,
    ParamTypeCommentOrAnnotation,
    TypeApplication,
    TypeAlias,
    CastTarget,
    Constraint,
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
                IssueType::InvalidType(Box::from("Invalid type comment or annotation"))
            }
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
    TypeAlias(&'db TypeAlias),
    DbType(DbType),
    SpecialType(SpecialType),
    RecursiveAlias(PointLink),
    InvalidVariable(InvalidVariableType<'a>),
    TypeVarTuple(TypeVarTupleUsage),
    ParamSpec(ParamSpecUsage),
    Unpacked(TypeOrTypeVarTuple),
    Concatenate(CallableParams),
    ClassVar(DbType),
    EnumMember(EnumMember),
    Unknown,
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
    NamedTupleDefinition(DbType),
    Enum(Rc<Enum>),
    RecursiveAlias(PointLink),
    Unknown,
}

#[derive(Debug)]
pub enum CalculatedBaseClass {
    DbType(DbType),
    Protocol,
    NamedTuple(Rc<NamedTuple>),
    NewNamedTuple,
    Generic,
    Invalid,
    InvalidEnum(Rc<Enum>),
    Unknown,
}

macro_rules! compute_type_application {
    ($self:ident, $slice_type:expr, $from_alias_definition:expr, $method:ident $args:tt) => {{
        let mut on_type_var = |i_s: &InferenceState, _: &_, type_var_like: TypeVarLike, current_callable| {
            if let Some(class) = i_s.current_class() {
                if let Some(usage) = class
                    .type_vars(i_s)
                    .and_then(|t| t.find(type_var_like.clone(), class.node_ref.as_link()))
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
                    .and_then(|t| t.find(type_var_like.clone(), function.node_ref.as_link()))
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
            TypeVarCallbackReturn::NotFound
        };
        let mut tcomp = TypeComputation::new(
            $self,
            $slice_type.as_node_ref().as_link(),
            &mut on_type_var,
            TypeComputationOrigin::TypeApplication
        );
        let t = tcomp.$method $args;
        match t {
            TypeContent::Class{node_ref, ..} => {
                todo!()
            }
            TypeContent::SimpleGeneric{class_link, generics, ..} => {
                Inferred::from_type(DbType::Type(Rc::new(DbType::new_class(class_link, generics))))
            }
            TypeContent::DbType(mut db_type) => {
                let type_vars = tcomp.into_type_vars(|inf, recalculate_type_vars| {
                    db_type = recalculate_type_vars(&db_type);
                });
                if type_vars.len() > 0 {
                    if !$from_alias_definition {
                        todo!("{type_vars:?}")
                    }
                    Inferred::new_unsaved_complex(ComplexPoint::TypeAlias(Box::new(TypeAlias::new_valid(
                        Some(type_vars),
                        $slice_type.as_node_ref().as_link(),
                        None,
                        Rc::new(db_type),
                        false,
                    ))))
                } else {
                    Inferred::from_type(DbType::Type(Rc::new(db_type)))
                }
            },
            TypeContent::Unknown => Inferred::new_any(),
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
            .and_then(|t| t.find(type_var_like.clone(), class.node_ref.as_link()))
        {
            return TypeVarCallbackReturn::TypeVarLike(usage);
        }
    }
    if let Some(func) = i_s.current_function() {
        if let Some(type_vars) = func.type_vars(i_s) {
            let usage = type_vars.find(type_var_like, func.node_ref.as_link());
            if let Some(usage) = usage {
                return TypeVarCallbackReturn::TypeVarLike(usage);
            }
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
            todo!()
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
            TypeContent::SpecialType(SpecialType::Type) => {
                CalculatedBaseClass::DbType(DbType::new_class(
                    self.inference.i_s.db.python_state.type_node_ref().as_link(),
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
            TypeContent::DbType(DbType::Enum(e)) => CalculatedBaseClass::InvalidEnum(e),
            _ => {
                let db_type =
                    self.as_db_type(calculated, NodeRef::new(self.inference.file, expr.index()));
                match db_type {
                    DbType::Class(..) | DbType::Tuple(_) | DbType::Callable(_) => {
                        CalculatedBaseClass::DbType(db_type)
                    }
                    DbType::Type(t) if matches!(t.as_ref(), DbType::Any) => {
                        CalculatedBaseClass::DbType(DbType::new_class(
                            self.inference.i_s.db.python_state.type_node_ref().as_link(),
                            ClassGenerics::None,
                        ))
                    }
                    DbType::NamedTuple(nt) => {
                        // TODO performance: this is already an Rc and should not need to be
                        // duplicated.
                        CalculatedBaseClass::NamedTuple(nt)
                    }
                    DbType::Any => CalculatedBaseClass::Unknown,
                    DbType::NewType(_) => {
                        self.add_issue_for_index(expr.index(), IssueType::CannotSubclassNewType);
                        CalculatedBaseClass::Unknown
                    }
                    _ => CalculatedBaseClass::Invalid,
                }
            }
        }
    }

    pub fn cache_annotation(&mut self, annotation: Annotation, is_implicit_optional: bool) {
        let expr = annotation.expression();
        match annotation.simple_param_kind() {
            Some(SimpleParamKind::Normal) | None => self.cache_annotation_or_type_comment(
                annotation.index(),
                expr,
                is_implicit_optional,
                None,
            ),
            Some(SimpleParamKind::Starred) => self.cache_annotation_or_type_comment(
                annotation.index(),
                expr,
                false,
                Some(&|slf, t| {
                    wrap_starred(slf.as_db_type(t, NodeRef::new(self.inference.file, expr.index())))
                }),
            ),
            Some(SimpleParamKind::DoubleStarred) => self.cache_annotation_or_type_comment(
                annotation.index(),
                expr,
                false,
                Some(&|slf, t| {
                    wrap_double_starred(
                        self.inference.i_s.db,
                        slf.as_db_type(t, NodeRef::new(self.inference.file, expr.index())),
                    )
                }),
            ),
        };
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
        let mut db_type = match map_type_callback {
            Some(map_type_callback) => map_type_callback(self, type_),
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
                ) if self.origin == TypeComputationOrigin::AssignmentTypeCommentOrAnnotation => {
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
                    let i_s = self.inference.i_s;
                    if self.origin == TypeComputationOrigin::AssignmentTypeCommentOrAnnotation
                        && i_s.current_class().is_some()
                        && i_s.current_function().is_none()
                    {
                        todo!()
                    } else {
                        self.add_issue(node_ref, IssueType::ClassVarOnlyInAssignmentsInClass);
                        DbType::Any
                    }
                }
                TypeContent::ClassVar(t) => {
                    is_class_var = true;
                    if self.origin != TypeComputationOrigin::AssignmentTypeCommentOrAnnotation {
                        self.add_issue(node_ref, IssueType::ClassVarOnlyInAssignmentsInClass);
                        DbType::Any
                    } else if self.has_type_vars_or_self {
                        let i_s = self.inference.i_s;
                        let class = i_s.current_class().unwrap();
                        let mut uses_class_generics = false;
                        t.search_type_vars(&mut |usage| {
                            if usage.in_definition() == class.node_ref.as_link() {
                                uses_class_generics = true
                            }
                        });
                        if uses_class_generics {
                            self.add_issue(node_ref, IssueType::ClassVarCannotContainTypeVariables);
                            DbType::Any
                        } else if class.type_vars(i_s).is_some() && t.has_self_type() {
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
                _ => self.as_db_type(type_, node_ref),
            },
        };
        if is_implicit_optional {
            db_type.make_optional(self.inference.i_s.db)
        }
        Inferred::from_type(db_type).save_redirect(
            self.inference.i_s,
            self.inference.file,
            expr.index(),
        );
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

    fn as_db_type(&mut self, type_: TypeContent, node_ref: NodeRef) -> DbType {
        let db = self.inference.i_s.db;
        match type_ {
            TypeContent::Class { node_ref, .. } => {
                Class::with_undefined_generics(node_ref).as_db_type(db)
            }
            TypeContent::SimpleGeneric {
                class_link,
                generics,
                ..
            } => DbType::new_class(class_link, generics),
            TypeContent::DbType(d) => d,
            TypeContent::Module(file) => {
                self.add_module_issue(node_ref, &Module::new(file).qualified_name(db));
                DbType::Any
            }
            TypeContent::Namespace(n) => {
                self.add_module_issue(node_ref, &n.qualified_name());
                DbType::Any
            }
            TypeContent::TypeAlias(a) => {
                self.is_recursive_alias |= a.is_recursive();
                a.as_db_type_and_set_type_vars_any(db)
            }
            TypeContent::SpecialType(m) => match m {
                SpecialType::Callable => DbType::Callable(Rc::new(CallableContent::new_any())),
                SpecialType::Any => DbType::Any,
                SpecialType::Type => db.python_state.type_of_any.clone(),
                SpecialType::Tuple => DbType::Tuple(TupleContent::new_empty()),
                SpecialType::ClassVar => {
                    self.add_issue(node_ref, IssueType::ClassVarNestedInsideOtherType);
                    DbType::Any
                }
                SpecialType::LiteralString => DbType::new_class(
                    db.python_state.str_node_ref().as_link(),
                    ClassGenerics::None,
                ),
                SpecialType::Literal => {
                    self.add_issue(
                        node_ref,
                        IssueType::InvalidType(Box::from(
                            "Literal[...] must have at least one parameter",
                        )),
                    );
                    DbType::Any
                }
                SpecialType::Self_
                    if !matches!(
                        self.origin,
                        TypeComputationOrigin::Constraint | TypeComputationOrigin::BaseClass
                    ) && self.inference.i_s.current_class().is_some() =>
                {
                    if self.inference.i_s.current_class().unwrap().is_metaclass(db) {
                        self.add_issue(node_ref, IssueType::SelfTypeInMetaclass);
                        DbType::Any
                    } else {
                        self.has_type_vars_or_self = true;
                        DbType::Self_
                    }
                }
                SpecialType::Self_ => {
                    self.add_issue(
                        node_ref,
                        IssueType::InvalidType(Box::from(
                            "Self type is only allowed in annotations within class definition",
                        )),
                    );
                    DbType::Any
                }
                SpecialType::Annotated => {
                    self.add_issue(
                        node_ref,
                        IssueType::InvalidType(Box::from(
                            "Annotated[...] must have exactly one type argument and at least one annotation",
                        )),
                    );
                    DbType::Any
                }
                SpecialType::Optional => {
                    self.add_issue(node_ref, IssueType::OptionalMustHaveOneArgument);
                    DbType::Any
                }
                _ => {
                    self.add_issue(node_ref, IssueType::InvalidType(Box::from("Invalid type")));
                    DbType::Any
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
                DbType::Any
            }
            TypeContent::Unpacked(t) => DbType::Any, // TODO Should probably raise an error?
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
                DbType::Any
            }
            // TODO here we would need to check if the generics are actually valid.
            TypeContent::RecursiveAlias(link) => {
                self.is_recursive_alias = true;
                DbType::RecursiveAlias(Rc::new(RecursiveAlias::new(link, None)))
            }
            TypeContent::Unknown => DbType::Any,
            TypeContent::ClassVar(t) => {
                self.add_issue(node_ref, IssueType::ClassVarNestedInsideOtherType);
                DbType::Any
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
                DbType::Any
            }
            TypeContent::InvalidVariable(t) => {
                t.add_issue(
                    self.inference.i_s.db,
                    |t| self.add_issue(node_ref, t),
                    self.origin,
                );
                DbType::Any
            }
        }
    }

    fn compute_named_expr_db_type(&mut self, named_expr: NamedExpression) -> DbType {
        let t = self.compute_type(named_expr.expression());
        self.as_db_type(t, NodeRef::new(self.inference.file, named_expr.index()))
    }

    fn compute_slice_type(&mut self, slice: SliceOrSimple<'x>) -> TypeContent<'db, 'x> {
        match slice {
            SliceOrSimple::Simple(s) => self.compute_type(s.named_expr.expression()),
            SliceOrSimple::Slice(n) => TypeContent::InvalidVariable(InvalidVariableType::Slice),
        }
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
                    node_ref,
                    has_type_vars: true,
                } => {
                    let node_ref = *node_ref;
                    // This essentially means we have a class with Any generics. This is not what
                    // we want to be defined as a redirect and therefore we calculate Foo[Any, ...]
                    return TypeContent::DbType(self.as_db_type(type_content, node_ref));
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

    fn compute_slice_db_type(&mut self, slice: SliceOrSimple) -> DbType {
        let t = self.compute_slice_type(slice);
        self.as_db_type(t, slice.as_node_ref())
    }

    fn compute_slice_type_or_type_var_tuple(&mut self, slice: SliceOrSimple) -> TypeOrTypeVarTuple {
        let t = self.compute_slice_type(slice);
        self.convert_slice_type_or_type_var_tuple(t, slice)
    }

    fn convert_slice_type_or_type_var_tuple(
        &mut self,
        t: TypeContent,
        slice: SliceOrSimple,
    ) -> TypeOrTypeVarTuple {
        match t {
            TypeContent::Unpacked(x @ TypeOrTypeVarTuple::TypeVarTuple(_)) => x,
            TypeContent::Unpacked(TypeOrTypeVarTuple::Type(_)) => todo!(),
            t => TypeOrTypeVarTuple::Type(self.as_db_type(t, slice.as_node_ref())),
        }
    }

    fn compute_type_expression_part(&mut self, node: ExpressionPart<'x>) -> TypeContent<'db, 'x> {
        match node {
            ExpressionPart::Atom(atom) => self.compute_type_atom(atom),
            ExpressionPart::Primary(primary) => self.compute_type_primary(primary),
            ExpressionPart::BitwiseOr(bitwise_or) => {
                let (a, b) = bitwise_or.unpack();
                let first = self.compute_type_expression_part(a);
                let first = self.as_db_type(first, NodeRef::new(self.inference.file, b.index()));
                // TODO this should only merge in annotation contexts
                let second = self.compute_type_expression_part(b);
                let second = self.as_db_type(second, NodeRef::new(self.inference.file, b.index()));
                TypeContent::DbType(first.union(self.inference.i_s.db, second))
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
                    TypeContent::DbType(match new_typing_named_tuple(self.inference.i_s, &args) {
                        Some(rc) => DbType::NamedTuple(rc),
                        None => DbType::Any,
                    })
                }
                TypeContent::SpecialType(SpecialType::CollectionsNamedTuple) => {
                    let args = SimpleArguments::from_primary(
                        *self.inference.i_s,
                        self.inference.file,
                        primary,
                    );
                    TypeContent::DbType(
                        match new_collections_named_tuple(self.inference.i_s, &args) {
                            Some(rc) => DbType::NamedTuple(rc),
                            None => DbType::Any,
                        },
                    )
                }
                TypeContent::Unknown => TypeContent::Unknown,
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
                    TypeContent::SimpleGeneric {
                        class_link,
                        generics,
                        ..
                    } => {
                        todo!()
                    }
                    TypeContent::DbType(d) => match d {
                        DbType::Any => TypeContent::DbType(d),
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
                            TypeContent::DbType(DbType::Any)
                        }
                        SpecialType::Final => self.compute_type_get_item_on_final(s),
                        SpecialType::Unpack => self.compute_type_get_item_on_unpack(s),
                        SpecialType::Concatenate => self.compute_type_get_item_on_concatenate(s),
                        SpecialType::Annotated => self.compute_get_item_on_annotated(s),
                        SpecialType::ClassVar => self.compute_get_item_on_class_var(s),
                    },
                    TypeContent::RecursiveAlias(link) => {
                        self.is_recursive_alias = true;
                        let type_vars = RecursiveAlias::new(link, None)
                            .type_alias(self.inference.i_s.db)
                            .type_vars
                            .as_ref();
                        let generics = self.compute_generics_for_alias(s, type_vars);
                        TypeContent::DbType(DbType::RecursiveAlias(Rc::new(RecursiveAlias::new(
                            link,
                            Some(generics),
                        ))))
                    }
                    TypeContent::InvalidVariable(t) => {
                        t.add_issue(
                            self.inference.i_s.db,
                            |t| self.add_issue(s.as_node_ref(), t),
                            self.origin,
                        );
                        TypeContent::Unknown
                    }
                    TypeContent::TypeVarTuple(_) => todo!(),
                    TypeContent::ParamSpec(_) => todo!(),
                    TypeContent::Unpacked(_) => todo!(),
                    TypeContent::Concatenate(_) => todo!(),
                    TypeContent::ClassVar(_) => todo!(),
                    TypeContent::EnumMember(_) => todo!(),
                    TypeContent::Unknown => TypeContent::Unknown,
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
                    match Module::new(f).sub_module(db, name.as_str()) {
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
                            debug!("TypeComputation: Attribute on class not found");
                            self.add_issue_for_index(primary.index(), IssueType::TypeNotFound);
                            self.inference
                                .file
                                .points
                                .set(name.index(), Point::new_unknown(Locality::Todo));
                            TypeContent::Unknown
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
                        TypeContent::Unknown
                    }
                }
            }
            TypeContent::Class { node_ref, .. } => {
                let cls = Class::with_undefined_generics(node_ref);
                self.check_attribute_on_class(cls, primary, name)
            }
            TypeContent::SimpleGeneric {
                class_link,
                generics,
                ..
            } => {
                let cls = Class::from_generic_class_components(db, class_link, &generics);
                self.check_attribute_on_class(cls, primary, name)
            }
            TypeContent::DbType(t) => match t {
                DbType::Any => TypeContent::DbType(DbType::Any),
                DbType::Enum(e) => match Enum::lookup(&e, db, name.as_str()) {
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
            TypeContent::TypeAlias(_) | TypeContent::RecursiveAlias(_) => todo!(),
            TypeContent::SpecialType(m) => todo!(),
            TypeContent::TypeVarTuple(_) => todo!(),
            TypeContent::ParamSpec(param_spec) => match name.as_code() {
                "args" => TypeContent::DbType(DbType::ParamSpecArgs(param_spec)),
                "kwargs" => TypeContent::DbType(DbType::ParamSpecKwargs(param_spec)),
                _ => todo!(),
            },
            TypeContent::Unpacked(_) => todo!(),
            TypeContent::Concatenate(_) => todo!(),
            TypeContent::InvalidVariable(t) => TypeContent::InvalidVariable(t),
            TypeContent::ClassVar(_) => todo!(),
            TypeContent::EnumMember(_) => todo!(),
            TypeContent::Unknown => TypeContent::Unknown,
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
            debug_assert_eq!(point_type, PointType::Unknown);
            self.add_issue_for_index(primary.index(), IssueType::TypeNotFound);
            TypeContent::Unknown
        }
    }

    fn compute_generics_for_alias(
        &mut self,
        slice_type: SliceType,
        type_var_likes: Option<&TypeVarLikes>,
    ) -> GenericsList {
        let mut generics = vec![];
        let mut mismatch = false;
        self.calculate_type_arguments(
            slice_type,
            &mut generics,
            slice_type.iter(),
            type_var_likes,
            &|| Box::from("TODO alias name"),
            |slf: &mut Self, given_count, expected_count| {
                mismatch = true;
                slf.add_issue(
                    slice_type.as_node_ref(),
                    IssueType::TypeAliasArgumentIssue {
                        expected_count,
                        given_count,
                    },
                );
            },
        );
        // TODO merge this with class stuff
        if mismatch {
            if let Some(type_var_likes) = type_var_likes {
                generics.clear();
                for missing_type_var in type_var_likes.iter().skip(generics.len()) {
                    generics.push(missing_type_var.as_any_generic_item())
                }
            } else {
                generics.clear();
            }
        }
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
                let t = self.as_db_type(type_.clone(), s.as_node_ref());
                let i_s = &mut self.inference.i_s;
                let actual = Type::new(&t);
                let expected = Type::new(bound);
                if !expected.is_simple_super_type_of(i_s, &actual).bool() {
                    s.as_node_ref().add_issue(
                        i_s,
                        IssueType::TypeVarBoundViolation {
                            actual: actual.format_short(i_s.db),
                            of: get_of(),
                            expected: expected.format_short(i_s.db),
                        },
                    );
                }
            }
            TypeVarKind::Constraints(constraints) => {
                let t2 = self.as_db_type(type_.clone(), s.as_node_ref());
                let i_s = &mut self.inference.i_s;
                if let DbType::TypeVar(usage) = &t2 {
                    if let TypeVarKind::Constraints(constraints2) = &usage.type_var.kind {
                        if constraints2.iter().all(|t2| {
                            constraints.iter().any(|t| {
                                Type::new(t)
                                    .is_simple_super_type_of(i_s, &Type::new(t2))
                                    .bool()
                            })
                        }) {
                            // The provided type_var2 is a subset of the type_var constraints.
                            return;
                        }
                    }
                }
                let t2 = Type::new(&t2);
                if !constraints
                    .iter()
                    .any(|t| Type::new(t).is_simple_super_type_of(i_s, &t2).bool())
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

    fn compute_type_get_item_on_class(
        &mut self,
        class: Class,
        slice_type: SliceType,
        primary: Option<Primary>,
    ) -> TypeContent<'db, 'db> {
        if !matches!(class.generics(), Generics::None | Generics::NotDefinedYet) {
            todo!();
            //return TypeContent::InvalidVariable(InvalidVariableType::Other);
        }
        let type_var_likes = class.type_vars(self.inference.i_s);

        let mut iterator = slice_type.iter();
        let mut generics = vec![];

        if let Some(tvs) = type_var_likes {
            // First check if we can make a SimpleGeneric. This happens if all generics are
            // SimpleGeneric or classes.
            if let Some(result) = self.maybe_generic_class_without_type_var(
                class,
                slice_type,
                &mut generics,
                &mut iterator,
                tvs,
                primary,
            ) {
                return result;
            }
            if generics.is_empty() {
                // If some generics are given we just continue the iterator, otherwise we start
                // fresh. This is a bit weird but helps us avoid recalculating db types that have
                // already been calculated.
                iterator = slice_type.iter();
            }
        };
        self.calculate_type_arguments(
            slice_type,
            &mut generics,
            iterator,
            type_var_likes,
            &|| Box::from(class.name()),
            |slf: &mut Self, given_count, expected_count| {
                slf.add_issue(
                    slice_type.as_node_ref(),
                    IssueType::TypeArgumentIssue {
                        class: Box::from(class.name()),
                        given_count,
                        expected_count,
                    },
                );
            },
        );
        TypeContent::DbType(match type_var_likes {
            None => DbType::new_class(class.node_ref.as_link(), ClassGenerics::None),
            Some(type_vars) => {
                // Need to fill the generics, because we might have been in a
                // SimpleGeneric case where the generic count is wrong.
                if generics.is_empty() {
                    for missing_type_var in type_vars.iter().skip(generics.len()) {
                        generics.push(missing_type_var.as_any_generic_item())
                    }
                    let expected_count = type_var_likes.map(|t| t.len()).unwrap_or(0);
                    generics.truncate(expected_count);
                }
                DbType::new_class(
                    class.node_ref.as_link(),
                    ClassGenerics::List(GenericsList::generics_from_vec(generics)),
                )
            }
        })
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
    ) -> Option<TypeContent<'db, 'db>> {
        if primary.is_none() || self.origin != TypeComputationOrigin::ParamTypeCommentOrAnnotation {
            return None;
        }
        for (i, type_var_like) in tvs.iter().enumerate() {
            let TypeVarLike::TypeVar(type_var) = type_var_like else {
                return None
            };
            if let Some(slice_content) = iterator.next() {
                let t = self.compute_slice_type(slice_content);
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
                            self.compute_slice_db_type(slice_content),
                        ));
                    }
                    generics.push(GenericItem::TypeArgument(
                        self.as_db_type(t, slice_content.as_node_ref()),
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
            Some(TypeContent::SimpleGeneric {
                node_ref,
                class_link: class.node_ref.as_link(),
                generics: match slice_type.ast_node {
                    ASTSliceType::NamedExpression(n) => ClassGenerics::ExpressionWithClassType(
                        PointLink::new(node_ref.file_index(), n.expression().index()),
                    ),
                    ASTSliceType::Slices(slices) => ClassGenerics::SlicesWithClassTypes(
                        PointLink::new(node_ref.file_index(), slices.index()),
                    ),
                    ASTSliceType::Slice(_) => unreachable!(),
                },
            })
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
        type_var_likes: Option<&TypeVarLikes>,
        get_of: &impl Fn() -> Box<str>,
        on_count_mismatch: impl FnOnce(&mut Self, usize, usize),
    ) {
        let mut given_count = generics.len();
        let expected_count = type_var_likes.map(|t| t.len()).unwrap_or(0);
        if let Some(type_var_likes) = type_var_likes {
            for type_var_like in type_var_likes.iter().skip(generics.len()) {
                let generic_item = match type_var_like {
                    TypeVarLike::TypeVar(type_var) => {
                        if let Some(slice_content) = iterator.next() {
                            let t = self.compute_slice_type(slice_content);
                            self.check_constraints(type_var, &slice_content, &t, get_of);
                            given_count += 1;
                            GenericItem::TypeArgument(
                                self.as_db_type(t, slice_content.as_node_ref()),
                            )
                        } else {
                            type_var_like.as_any_generic_item()
                        }
                    }
                    TypeVarLike::TypeVarTuple(_) => {
                        let fetch =
                            slice_type.iter().count() as isize + 1 - expected_count as isize;
                        GenericItem::TypeArguments(TypeArguments::new_fixed_length(
                            if let Ok(fetch) = fetch.try_into() {
                                given_count += 1;
                                iterator
                                    .by_ref()
                                    .take(fetch)
                                    .map(|s| self.compute_slice_type_or_type_var_tuple(s))
                                    .collect()
                            } else {
                                // If not enough type arguments are given, an error is raised elsewhere.
                                Rc::new([])
                            },
                        ))
                    }
                    TypeVarLike::ParamSpec(_) => {
                        given_count += 1;
                        if expected_count == 1 && slice_type.iter().count() != 1 {
                            // PEP 612 allows us to write C[int, str] instead of C[[int, str]],
                            // because "for aesthetic purposes we allow these to be omitted".
                            let params =
                                self.calculate_simplified_param_spec_generics(&mut iterator);
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
        }
        for slice_content in iterator {
            // Still calculate errors for the rest of the types given. After all they are still
            // expected to be types.
            self.compute_slice_db_type(slice_content);
            given_count += 1;
        }
        if given_count != expected_count {
            on_count_mismatch(self, given_count, expected_count);
            generics.clear();
        }
    }

    fn compute_type_get_item_on_tuple(&mut self, slice_type: SliceType) -> TypeContent<'db, 'db> {
        let mut iterator = slice_type.iter();
        let first = iterator.next().unwrap();
        let generics: Rc<[_]> = if let Some(slice_or_simple) = iterator.next() {
            if let SliceOrSimple::Simple(s) = slice_or_simple {
                if s.named_expr.is_ellipsis_literal() {
                    let t = self.compute_slice_db_type(first);
                    return TypeContent::DbType(DbType::Tuple(Rc::new(
                        TupleContent::new_arbitrary_length(t),
                    )));
                }
            }
            slice_type
                .iter()
                .map(|slice_content| {
                    self.compute_slice_type_or_type_var_tuple(slice_content)
                    /*
                     * TODO TypeVarTuple
                    if matches!(t, DbType::TypeVar(ref t) if t.is_type_var_tuple()) {
                        todo!()
                    }
                    */
                })
                .collect()
        } else {
            let t = self.compute_slice_type(first);
            // Handle Tuple[()]
            match t {
                TypeContent::InvalidVariable(InvalidVariableType::Tuple { tuple_length: 0 }) => {
                    Rc::new([])
                }
                _ => Rc::new([self.convert_slice_type_or_type_var_tuple(t, first)]),
            }
        };
        TypeContent::DbType(DbType::Tuple(Rc::new(TupleContent::new_fixed_length(
            generics,
        ))))
    }

    fn calculate_simplified_param_spec_generics<'y, I: Iterator<Item = SliceOrSimple<'y>>>(
        &mut self,
        iterator: &mut I,
    ) -> CallableParams {
        let mut params = vec![];
        for s in iterator {
            let t = self.compute_slice_type(s);
            self.add_param(&mut params, t, s.as_node_ref().node_index)
        }
        CallableParams::Simple(Rc::from(params))
    }

    fn check_param(&mut self, t: TypeContent, index: NodeIndex) -> CallableParam {
        if let TypeContent::SpecialType(SpecialType::CallableParam(p)) = t {
            p
        } else {
            CallableParam {
                param_specific: ParamSpecific::PositionalOnly(
                    self.as_db_type(t, NodeRef::new(self.inference.file, index)),
                ),
                has_default: false,
                name: None,
            }
        }
    }

    fn add_param(&mut self, params: &mut Vec<CallableParam>, t: TypeContent, index: NodeIndex) {
        let p = self.check_param(t, index);
        if let Some(previous) = params.last() {
            let prev_kind = previous.param_specific.param_kind();
            let current_kind = p.param_specific.param_kind();
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
                ParamKind::Starred if current_kind <= prev_kind => {
                    Some("Var args may not appear after named or var args")
                }
                ParamKind::KeywordOnly if current_kind <= prev_kind => {
                    Some("A **kwargs argument must be the last argument")
                }
                ParamKind::DoubleStarred if current_kind == prev_kind => {
                    Some("You may only have one **kwargs argument")
                }
                _ => None,
            };
            if let Some(msg) = msg {
                self.add_issue_for_index(index, IssueType::InvalidType(Box::from(msg)));
                return;
            }

            if let Some(param_name) = p.name {
                let param_name = param_name.as_str(self.inference.i_s.db);
                for other in params.iter() {
                    if let Some(other_name) = other.name {
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
            |slf: &mut Self| match slf.compute_slice_type(first) {
                TypeContent::ParamSpec(p) => CallableParams::WithParamSpec(Rc::new([]), p),
                TypeContent::SpecialType(SpecialType::Any) if from_class_generics => {
                    CallableParams::Any
                }
                TypeContent::Unknown => CallableParams::Any,
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
                    CallableParams::Any
                }
            };
        if let ExpressionContent::ExpressionPart(ExpressionPart::Atom(atom)) =
            n.named_expr.expression().unpack()
        {
            match atom.unpack() {
                AtomContent::List(list) => {
                    let mut params = vec![];
                    for i in list.unpack() {
                        if let StarLikeExpression::NamedExpression(n) = i {
                            let t = self.compute_type(n.expression());
                            self.add_param(&mut params, t, n.index())
                        } else {
                            todo!()
                        }
                    }
                    CallableParams::Simple(Rc::from(params))
                }
                AtomContent::Ellipsis => CallableParams::Any,
                _ => calc_params(self),
            }
        } else {
            calc_params(self)
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
            let result_type = iterator
                .next()
                .map(|slice_content| self.compute_slice_db_type(slice_content))
                .unwrap_or(DbType::Any);
            CallableContent {
                name: None,
                class_name: None,
                defined_at,
                kind: FunctionKind::Function,
                type_vars: None,
                params,
                result_type,
            }
        } else {
            self.add_issue(slice_type.as_node_ref(), IssueType::InvalidCallableArgCount);
            CallableContent::new_any()
        };
        self.current_callable = old;
        TypeContent::DbType(DbType::Callable(Rc::new(content)))
    }

    fn compute_type_get_item_on_union(
        &mut self,
        slice_type: SliceType,
    ) -> TypeContent<'static, 'static> {
        let iterator = slice_type.iter();
        if let SliceTypeIterator::SliceOrSimple(s) = iterator {
            let t = self.compute_slice_type(s);
            let t = self.as_db_type(t, s.as_node_ref());
            TypeContent::DbType(t)
        } else {
            let mut t = UnionType::new(
                iterator
                    .enumerate()
                    .map(|(format_index, slice_or_simple)| {
                        let t = self.compute_slice_type(slice_or_simple);
                        UnionEntry {
                            type_: self.as_db_type(t, slice_or_simple.as_node_ref()),
                            format_index,
                        }
                    })
                    .collect(),
            );
            t.sort_for_priority();
            TypeContent::DbType(DbType::Union(t))
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
        let t = self.compute_slice_db_type(first);
        let format_as_optional = !Type::new(&t).is_union();
        let mut t = t.union_with_details(self.inference.i_s.db, DbType::None, format_as_optional);
        let DbType::Union(union_type) = &mut t else {unreachable!()};
        union_type.sort_for_priority();
        TypeContent::DbType(t)
    }

    fn compute_type_get_item_on_type(&mut self, slice_type: SliceType) -> TypeContent<'db, 'db> {
        let mut iterator = slice_type.iter();
        let content = iterator.next().unwrap();
        if iterator.count() > 0 {
            todo!()
        }
        TypeContent::DbType(DbType::Type(Rc::new(self.compute_slice_db_type(content))))
    }

    fn compute_type_get_item_on_alias(
        &mut self,
        alias: &TypeAlias,
        slice_type: SliceType,
    ) -> TypeContent<'db, 'db> {
        let generics = self.compute_generics_for_alias(slice_type, alias.type_vars.as_ref());
        self.is_recursive_alias |= alias.is_recursive();
        TypeContent::DbType(
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
        if iterator.count() == 0 {
            TypeContent::DbType(self.compute_slice_db_type(first))
        } else {
            todo!()
        }
    }

    fn compute_type_get_item_on_unpack(&mut self, slice_type: SliceType) -> TypeContent<'db, 'db> {
        let mut iterator = slice_type.iter();
        let first = iterator.next().unwrap();
        if iterator.count() == 0 {
            TypeContent::Unpacked(match self.compute_slice_type(first) {
                TypeContent::TypeVarTuple(t) => TypeOrTypeVarTuple::TypeVarTuple(t),
                t => TypeOrTypeVarTuple::Type(self.as_db_type(t, first.as_node_ref())),
            })
        } else {
            todo!()
        }
    }

    fn compute_type_get_item_on_concatenate(
        &mut self,
        slice_type: SliceType,
    ) -> TypeContent<'db, 'db> {
        let count = slice_type.iter().count();
        let mut iterator = slice_type.iter();
        let types = iterator
            .by_ref()
            .take(count - 1)
            .map(|s| self.compute_slice_db_type(s))
            .collect();
        match self.compute_slice_type(iterator.next().unwrap()) {
            TypeContent::ParamSpec(p) => {
                TypeContent::Concatenate(CallableParams::WithParamSpec(types, p))
            }
            TypeContent::Concatenate(_) => {
                self.add_issue(slice_type.as_node_ref(), IssueType::NestedConcatenate);
                TypeContent::Unknown
            }
            TypeContent::Unknown => TypeContent::Unknown,
            t => todo!("{t:?}"),
        }
    }

    fn compute_get_item_on_literal(&mut self, slice_type: SliceType) -> TypeContent<'db, 'db> {
        let mut iterator = slice_type.iter();
        let first = iterator.next().unwrap();
        if iterator.next().is_some() {
            TypeContent::DbType(DbType::Union(UnionType::new(
                slice_type
                    .iter()
                    .enumerate()
                    .map(|(i, s)| UnionEntry {
                        type_: {
                            let t = self.compute_get_item_on_literal_item(s, i + 1);
                            self.as_db_type(t, s.as_node_ref())
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
                TypeContent::Unknown
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
                            return TypeContent::Unknown;
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
                            return TypeContent::Unknown;
                        }
                        AtomContent::Name(_) | AtomContent::NoneLiteral => None,
                        _ => return expr_not_allowed(self),
                    };
                    if let Some(kind) = maybe {
                        return TypeContent::DbType(DbType::Literal(Literal {
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
                                    return TypeContent::DbType(DbType::Literal(Literal {
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
        match self.compute_slice_type(slice) {
            TypeContent::SpecialType(SpecialType::Any) => {
                self.add_issue(
                    slice.as_node_ref(),
                    IssueType::InvalidType(
                        format!("Parameter {index} of Literal[...] cannot be of type \"Any\"")
                            .into(),
                    ),
                );
                TypeContent::Unknown
            }
            TypeContent::InvalidVariable(_) => {
                self.add_issue(
                    slice.as_node_ref(),
                    IssueType::InvalidType(
                        format!("Parameter {index} of Literal[...] is invalid").into(),
                    ),
                );
                TypeContent::Unknown
            }
            TypeContent::EnumMember(e) => TypeContent::DbType(DbType::EnumMember(e)),
            t => match self.as_db_type(t, slice.as_node_ref()) {
                DbType::Any => TypeContent::Unknown,
                t @ (DbType::None | DbType::Literal(_)) => TypeContent::DbType(t),
                DbType::Union(u)
                    if u.iter().all(|t| {
                        matches!(t, DbType::Literal(_) | DbType::None | DbType::EnumMember(_))
                    }) =>
                {
                    TypeContent::DbType(DbType::Union(u))
                }
                _ => {
                    self.add_issue(
                        slice.as_node_ref(),
                        IssueType::InvalidType(
                            format!("Parameter {} of Literal[...] is invalid", index).into(),
                        ),
                    );
                    TypeContent::Unknown
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
            TypeContent::Unknown
        } else {
            TypeContent::DbType(self.compute_slice_db_type(first))
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
            TypeContent::Unknown
        } else {
            let i_s = self.inference.i_s;
            if i_s.current_class().is_none() || i_s.current_function().is_some() {
                self.add_issue(
                    slice_type.as_node_ref(),
                    IssueType::ClassVarOnlyInAssignmentsInClass,
                );
                TypeContent::Unknown
            } else {
                TypeContent::ClassVar(self.compute_slice_db_type(first))
            }
        }
    }

    fn expect_type_var_like_args(&mut self, slice_type: SliceType, class: &'static str) {
        for (i, s) in slice_type.iter().enumerate() {
            let result = self.compute_slice_type(s);
            let unpacked_type_var_tuple = matches!(
                &result,
                TypeContent::Unpacked(TypeOrTypeVarTuple::TypeVarTuple(t))
                    if t.in_definition == self.for_definition
            );
            if !matches!(result, TypeContent::ParamSpec(_))
                && !matches!(
                    result,
                    TypeContent::DbType(DbType::TypeVar(usage))
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
            AtomContent::NoneLiteral => TypeContent::DbType(DbType::None),
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
                has_type_vars: Class::with_undefined_generics(node_ref)
                    .type_vars(self.inference.i_s)
                    .is_some(),
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
                        Some(TypeContent::DbType(DbType::TypeVar(usage.into_owned())))
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
                        Some(TypeContent::Unknown)
                    }
                    TypeVarCallbackReturn::NotFound => None,
                }
                .unwrap_or_else(|| {
                    let index = self
                        .type_var_manager
                        .add(type_var_like.clone(), self.current_callable);
                    match type_var_like {
                        TypeVarLike::TypeVar(type_var) => {
                            TypeContent::DbType(DbType::TypeVar(TypeVarUsage {
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
            TypeNameLookup::NewType(n) => TypeContent::DbType(DbType::NewType(n)),
            TypeNameLookup::NamedTupleDefinition(t) => TypeContent::DbType(t),
            TypeNameLookup::Enum(t) => TypeContent::DbType(DbType::Enum(t)),
            TypeNameLookup::InvalidVariable(t) => TypeContent::InvalidVariable(t),
            TypeNameLookup::Unknown => TypeContent::Unknown,
            TypeNameLookup::SpecialType(special) => TypeContent::SpecialType(special),
            TypeNameLookup::RecursiveAlias(link) => TypeContent::RecursiveAlias(link),
        }
    }

    fn execute_mypy_extension_param(
        &mut self,
        primary: Primary,
        specific: Specific,
        details: ArgumentsDetails,
    ) -> TypeContent<'db, 'db> {
        let mut name = None;
        let mut db_type = None;
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
                    Some(slf.as_db_type(t, NodeRef::new(self.inference.file, expr.index())))
                };
                let arg = iterator.next().unwrap();
                match arg {
                    // The first arg is always there
                    Argument::Positional(n) => db_type = type_from_expr(self, n.expression()),
                    Argument::Keyword(kwarg) if kwarg.unpack().0.as_code() == "type" => {
                        db_type = type_from_expr(self, kwarg.unpack().1)
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
                            db_type = type_from_expr(self, kwarg.unpack().1)
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
            Specific::MypyExtensionsVarArg => ParamKind::Starred,
            Specific::MypyExtensionsKwArg => ParamKind::DoubleStarred,
            _ => unreachable!(),
        };
        let db_type = db_type.unwrap_or(DbType::Any);
        TypeContent::SpecialType(SpecialType::CallableParam(CallableParam {
            param_specific: match param_kind {
                ParamKind::PositionalOnly => ParamSpecific::PositionalOnly(db_type),
                ParamKind::PositionalOrKeyword => ParamSpecific::PositionalOrKeyword(db_type),
                ParamKind::KeywordOnly => ParamSpecific::KeywordOnly(db_type),
                ParamKind::Starred => {
                    ParamSpecific::Starred(StarredParamSpecific::ArbitraryLength(db_type))
                }
                ParamKind::DoubleStarred => {
                    ParamSpecific::DoubleStarred(DoubleStarredParamSpecific::ValueType(db_type))
                }
            },
            name,
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
            let ExpressionContent::ExpressionPart(ExpressionPart::Atom(atom)) = ne.expression().unpack() else {
                todo!()
            };
            let mut parts = match atom.unpack() {
                AtomContent::Tuple(tup) => tup.iter(),
                _ => {
                    NodeRef::new(self.inference.file, atom.index()).add_issue(
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
            let t = self.compute_named_expr_db_type(type_expr);
            params.push(CallableParam {
                param_specific: ParamSpecific::PositionalOrKeyword(t),
                name: Some(name),
                has_default: false,
            });
        }
        Some(params)
    }

    pub fn into_type_vars<C>(self, on_type_var_recalculation: C) -> TypeVarLikes
    where
        C: FnOnce(&Inference, &dyn Fn(&DbType) -> DbType),
    {
        if self.type_var_manager.has_late_bound_type_vars() {
            on_type_var_recalculation(self.inference, &|t| {
                Type::new(t).rewrite_late_bound_callables(&self.type_var_manager)
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
    pub fn ensure_cached_annotation(&mut self, annotation: Annotation) {
        if !self.file.points.get(annotation.index()).calculated() {
            let mut x = type_computation_for_variable_annotation;
            let mut comp = TypeComputation::new(
                self,
                PointLink::new(self.file_index, annotation.index()),
                &mut x,
                TypeComputationOrigin::AssignmentTypeCommentOrAnnotation,
            );
            comp.cache_annotation(annotation, false);
            comp.into_type_vars(|inf, recalculate_type_vars| {
                inf.recalculate_annotation_type_vars(annotation.index(), recalculate_type_vars);
            });
        }
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

    pub fn compute_type_application_on_alias(
        &mut self,
        alias: &TypeAlias,
        slice_type: SliceType,
        from_alias_definition: bool,
    ) -> Inferred {
        if !alias.is_class() {
            slice_type
                .as_node_ref()
                .add_issue(self.i_s, IssueType::OnlyClassTypeApplication);
            return Inferred::new_any();
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
    ) -> Type<'file> {
        self.use_cached_annotation_or_type_comment_type_internal(
            annotation.index(),
            annotation.expression(),
        )
    }

    pub fn use_cached_annotation_type(&mut self, annotation: Annotation) -> Type<'file> {
        self.use_cached_annotation_or_type_comment_type_internal(
            annotation.index(),
            annotation.expression(),
        )
    }

    fn use_cached_annotation_or_type_comment_type_internal(
        &mut self,
        annotation_index: NodeIndex,
        expr: Expression,
    ) -> Type<'file> {
        let point = self.file.points.get(annotation_index);
        assert!(point.calculated(), "Expr: {:?}", expr);
        if point.specific() == Specific::AnnotationOrTypeCommentSimpleClassInstance {
            return self
                .infer_expression(expr)
                .expect_class_or_simple_generic(self.i_s);
        }
        debug_assert!(matches!(
            point.specific(),
            Specific::AnnotationOrTypeCommentWithTypeVars
                | Specific::AnnotationOrTypeCommentWithoutTypeVars
                | Specific::AnnotationOrTypeCommentClassVar
        ));
        let complex_index = self.file.points.get(expr.index()).complex_index();
        match self.file.complex_points.get(complex_index) {
            ComplexPoint::TypeInstance(t) => Type::new(t),
            _ => unreachable!(),
        }
    }

    pub fn recalculate_annotation_type_vars(
        &self,
        node_index: NodeIndex,
        recalculate: impl Fn(&DbType) -> DbType,
    ) {
        if matches!(
            self.file.points.get(node_index).specific(),
            Specific::AnnotationOrTypeCommentWithTypeVars
                | Specific::AnnotationOrTypeCommentClassVar
        ) {
            let new_t = recalculate(
                use_cached_annotation_or_type_comment(
                    self.i_s,
                    NodeRef::new(self.file, node_index),
                )
                .as_ref(),
            );
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
        let cached_type_node_ref =
            NodeRef::new(file, assignment.index() + ASSIGNMENT_TYPE_CACHE_OFFSET);
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
            let node_ref = NodeRef::new(file, name.index());
            debug_assert!(node_ref.point().calculated());
            return check_type_name(self.i_s, node_ref);
        }
        if let Some((name_def, annotation, expr)) =
            assignment.maybe_simple_type_expression_assignment()
        {
            if let Some((_, type_)) = self.check_for_type_comment(assignment) {
                // This case is a bit weird in Mypy, but it makes it possible to use a type
                // definition like:
                //
                //     Foo = 1  # Any
                if type_.is_any() {
                    return TypeNameLookup::Unknown;
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
            let inferred = self.check_point_cache(name_def.index()).unwrap();
            let in_definition = cached_type_node_ref.as_link();
            if inferred.maybe_saved_specific(self.i_s.db) == Some(Specific::Any) {
                // Happens e.g. when an invalid enum is defined somewhere.
                TypeNameLookup::Unknown
            } else if let Some(tv) = inferred.maybe_type_var_like(self.i_s) {
                TypeNameLookup::TypeVarLike(tv)
            } else if let Some(n) = inferred.maybe_new_type(self.i_s) {
                TypeNameLookup::NewType(n)
            } else if let Some(t) = inferred.maybe_named_tuple_definition(self.i_s) {
                TypeNameLookup::NamedTupleDefinition(t)
            } else if let Some(t) = inferred.maybe_enum_definition(self.i_s) {
                TypeNameLookup::Enum(t)
            } else {
                cached_type_node_ref.set_point(Point::new_calculating());
                let type_var_likes = TypeVarFinder::find_alias_type_vars(self, expr);
                let complex = ComplexPoint::TypeAlias(Box::new(TypeAlias::new(
                    (!type_var_likes.is_empty()).then_some(type_var_likes),
                    in_definition,
                    Some(PointLink::new(file.file_index(), name_def.name().index())),
                )));
                cached_type_node_ref.insert_complex(complex, Locality::Todo);
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
                    self,
                    in_definition,
                    &mut type_var_callback,
                    TypeComputationOrigin::TypeAlias,
                );
                comp.errors_already_calculated = p.calculated();
                let t = comp.compute_type(expr);
                let ComplexPoint::TypeAlias(alias) = cached_type_node_ref.complex().unwrap() else {
                    unreachable!()
                };
                match t {
                    TypeContent::InvalidVariable(t) if !is_explicit => {
                        alias.set_invalid();
                    }
                    _ => {
                        let node_ref = NodeRef::new(file, expr.index());
                        let db_type = comp.as_db_type(t, node_ref);
                        debug_assert!(!comp.type_var_manager.has_type_vars());
                        let is_recursive = comp.is_recursive_alias;
                        let type_var_likes = type_var_manager.into_type_vars();
                        let ComplexPoint::TypeAlias(alias) = cached_type_node_ref.complex().unwrap() else {
                            unreachable!()
                        };
                        alias.set_valid(db_type, is_recursive);
                    }
                };
                load_cached_type(cached_type_node_ref)
            }
        } else {
            if let Some(annotation) = assignment.maybe_annotation() {
                self.cache_assignment_nodes(assignment);
                if self.use_cached_annotation_type(annotation).is_any() {
                    return TypeNameLookup::Unknown;
                }
            }
            TypeNameLookup::InvalidVariable(InvalidVariableType::Other)
        }
    }

    pub(super) fn compute_explicit_type_assignment(&mut self, assignment: Assignment) {
        self.compute_type_assignment(assignment, true);
    }

    pub(super) fn lookup_type_name(&mut self, name: Name<'x>) -> TypeNameLookup<'db, 'x> {
        let point = self.file.points.get(name.index());
        debug_assert!(self.file.points.get(name.index()).calculated());
        match point.type_() {
            PointType::Specific => todo!(),
            PointType::Redirect => {
                check_type_name(self.i_s, point.as_redirected_node_ref(self.i_s.db))
            }
            PointType::FileReference => {
                let file = self.i_s.db.loaded_python_file(point.file_index());
                //TypeNameLookup::Module(file)
                todo!();
            }
            PointType::Unknown => TypeNameLookup::Unknown,
            _ => todo!("{point:?}"),
        }
    }

    pub(super) fn compute_type_comment(
        &mut self,
        start: CodeIndex,
        s: &str,
        assignment_node_ref: NodeRef,
    ) -> (Inferred, Type<'db>) {
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
                        let db_type =
                            inference.calc_type_comment_tuple(assignment_node_ref, tuple.iter());
                        NodeRef::new(f, index).set_point(Point::new_simple_specific(
                            Specific::AnnotationOrTypeCommentWithTypeVars,
                            Locality::Todo,
                        ));
                        Inferred::from_type(db_type).save_redirect(inference.i_s, f, expr_index);
                    } else {
                        let mut x = type_computation_for_variable_annotation;
                        let mut comp = TypeComputation::new(
                            &mut inference,
                            assignment_node_ref.as_link(),
                            &mut x,
                            TypeComputationOrigin::AssignmentTypeCommentOrAnnotation,
                        );
                        comp.cache_annotation_or_type_comment(index, expr, false, None);
                        let type_vars = comp.into_type_vars(|inf, recalculate_type_vars| {
                            inf.recalculate_annotation_type_vars(index, recalculate_type_vars);
                        });
                        debug_assert!(type_vars.is_empty());
                    }
                    (
                        Inferred::from_saved_node_ref(NodeRef::new(f, index)),
                        inference.use_cached_annotation_or_type_comment_type_internal(index, expr),
                    )
                }
                StarExpressionContent::Tuple(t) => {
                    let star_exprs_index = star_exprs.index();
                    let index = star_exprs_index - ANNOTATION_TO_EXPR_DIFFERENCE;
                    let db_type = inference.calc_type_comment_tuple(assignment_node_ref, t.iter());
                    let unsaved = Inferred::from_type(db_type);
                    unsaved.save_redirect(self.i_s, f, index);
                    let complex_index = f.points.get(index).complex_index();
                    (
                        Inferred::from_saved_node_ref(NodeRef::new(f, index)),
                        if let ComplexPoint::TypeInstance(db_type) =
                            f.complex_points.get(complex_index)
                        {
                            Type::new(db_type)
                        } else {
                            unreachable!()
                        },
                    )
                }
                StarExpressionContent::StarExpression(s) => todo!(),
            }
        } else {
            for stmt_or_error in f.tree.root().iter_stmts() {
                if let StmtOrError::Error(node_index) = stmt_or_error {
                    return (Inferred::new_any(), Type::new(&DbType::Any));
                }
            }
            debug!("Found non-expression in annotation: {}", f.tree.code());
            self.file.add_issue(
                self.i_s,
                Issue {
                    start_position: start,
                    end_position: start + s.len() as CodeIndex,
                    type_: IssueType::InvalidSyntaxInTypeComment {
                        type_comment: s.into(),
                    },
                },
            );
            return (Inferred::new_any(), Type::new(&DbType::Any));
        }
    }

    fn calc_type_comment_tuple<'s>(
        &mut self,
        assignment_node_ref: NodeRef,
        iterator: impl Iterator<Item = StarLikeExpression<'s>>,
    ) -> DbType {
        let generics = iterator
            .map(|star_like| {
                let expr = match star_like {
                    StarLikeExpression::NamedExpression(named_expr) => named_expr.expression(),
                    StarLikeExpression::Expression(expr) => expr,
                    StarLikeExpression::StarNamedExpression(x) => todo!("{x:?}"),
                    StarLikeExpression::StarExpression(x) => todo!("{x:?}"),
                };
                TypeOrTypeVarTuple::Type(if let Some(tuple) = expr.maybe_tuple() {
                    self.calc_type_comment_tuple(assignment_node_ref, tuple.iter())
                } else {
                    let expr_node_ref = NodeRef::new(self.file, expr.index());
                    let mut x = type_computation_for_variable_annotation;
                    let mut comp = TypeComputation::new(
                        self,
                        assignment_node_ref.as_link(),
                        &mut x,
                        TypeComputationOrigin::AssignmentTypeCommentOrAnnotation,
                    );
                    let t = comp.compute_type(expr);
                    let mut db_type = comp.as_db_type(t, expr_node_ref);
                    let type_vars = comp.into_type_vars(|inf, recalculate_type_vars| {
                        db_type = recalculate_type_vars(&db_type);
                    });
                    debug_assert!(type_vars.is_empty());
                    db_type
                })
            })
            .collect();
        DbType::Tuple(Rc::new(TupleContent::new_fixed_length(generics)))
    }

    pub fn check_for_type_comment(
        &mut self,
        assignment: Assignment,
    ) -> Option<(Inferred, Type<'db>)> {
        const TYPE: &str = "# type:";
        let suffix = assignment.suffix();
        if let Some(start) = suffix.find(TYPE) {
            let mut start = start + TYPE.len();
            let with_spaces = &suffix[start..];
            let full_rest = with_spaces.trim_start_matches(' ');
            // Use only the part before the comment after the type definition.
            let s = full_rest.split('#').next().unwrap();
            start += with_spaces.len() - full_rest.len();
            debug!("Infer type comment {s:?} on {:?}", assignment.as_code());
            if maybe_type_ignore(s).is_none() {
                return Some(self.compute_type_comment(
                    assignment.end() + start as CodeIndex,
                    s,
                    NodeRef::new(self.file, assignment.index()),
                ));
            }
        }
        None
    }
    pub fn compute_cast_target(&mut self, node_ref: NodeRef) -> Inferred {
        let named_expr = node_ref.as_named_expression();
        let mut x = type_computation_for_variable_annotation;
        let mut comp = TypeComputation::new(
            self,
            node_ref.as_link(),
            &mut x,
            TypeComputationOrigin::CastTarget,
        );

        let t = comp.compute_type(named_expr.expression());
        let mut db_type = comp.as_db_type(t, node_ref);
        let type_vars = comp.into_type_vars(|inf, recalculate_type_vars| {
            db_type = recalculate_type_vars(&db_type);
        });
        debug_assert!(type_vars.is_empty());
        Inferred::from_type(db_type)
    }

    pub fn compute_type_var_constraint(&mut self, expr: Expression) -> Option<DbType> {
        let mut on_type_var =
            |i_s: &InferenceState, _: &_, type_var_like: TypeVarLike, current_callable| {
                if let Some(class) = i_s.current_class() {
                    if let Some(type_var_likes) = class.type_vars(i_s) {
                        for (i, tvl) in type_var_likes.iter().enumerate() {
                            if type_var_like == *tvl {
                                return TypeVarCallbackReturn::TypeVarLike(
                                    tvl.as_type_var_like_usage(i.into(), class.node_ref.as_link()),
                                );
                            }
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
            _ => Some(comp.as_db_type(t, node_ref)),
        }
    }

    pub fn compute_new_type_constraint(&mut self, expr: Expression) -> DbType {
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
                DbType::Any
            }
            t => {
                let t = comp.as_db_type(t, node_ref);
                if !t.is_subclassable() {
                    node_ref.add_issue(
                        self.i_s,
                        IssueType::NewTypeMustBeSubclassable {
                            got: t.format_short(self.i_s.db),
                        },
                    );
                }
                t
            }
        }
    }
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
            Specific::TypingClassVar => SpecialType::ClassVar,
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
                } else if a.is_invalid() {
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

fn check_type_name<'db: 'file, 'file>(
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
                match point.maybe_specific() {
                    Some(Specific::TypingType) => {
                        return TypeNameLookup::SpecialType(SpecialType::Type);
                    }
                    Some(Specific::TypingTuple) => {
                        return TypeNameLookup::SpecialType(SpecialType::Tuple);
                    }
                    Some(Specific::TypingNamedTuple) => {
                        return TypeNameLookup::SpecialType(SpecialType::TypingNamedTuple);
                    }
                    Some(s) => {
                        debug!(
                            "Found an unexpected specific {s:?} for {}",
                            new_name.as_code()
                        );
                        return TypeNameLookup::InvalidVariable(InvalidVariableType::Variable(
                            name_node_ref,
                        ));
                    }
                    _ => (),
                }
            }
            // At this point the class is not necessarily calculated and we therefore do this here.
            let name_def = NodeRef::new(
                name_node_ref.file,
                new_name.name_definition().unwrap().index(),
            );
            name_def.file.inference(i_s).cache_class(name_def, c);
            if let Some(ComplexPoint::TypeInstance(DbType::Type(t))) = name_def.complex() {
                if let DbType::Enum(e) = t.as_ref() {
                    return TypeNameLookup::Enum(e.clone());
                }
            }
            // Classes can be defined recursive, so use the NamedTuple stuff here.
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
        TypeLike::Import => {
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
                    if let ComplexPoint::TypeInstance(DbType::Namespace(namespace)) =
                        name_def_ref.file.complex_points.get(complex_index)
                    {
                        return TypeNameLookup::Namespace(namespace.clone());
                    }
                }
                debug_assert_eq!(p.type_(), PointType::Unknown);
                TypeNameLookup::Unknown
            } else {
                name_node_ref.file.inference(i_s).infer_name(new_name);
                check_type_name(i_s, name_node_ref)
            }
        }
        TypeLike::ParamName(annotation) => TypeNameLookup::InvalidVariable({
            let as_base_class_any = annotation
                .map(
                    |a| match use_cached_annotation_type(i_s.db, name_node_ref.file, a).as_ref() {
                        DbType::Any => true,
                        DbType::Type(t) => match t.as_ref() {
                            DbType::Any => true,
                            DbType::Class(GenericClass {
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
            Point::new_unknown(Locality::Todo)
        },
    );
    cache_name_on_class(cls, file, name)
}

fn wrap_starred(t: DbType) -> DbType {
    match &t {
        DbType::ParamSpecArgs(_) => t,
        _ => DbType::Tuple(Rc::new(TupleContent::new_arbitrary_length(t))),
    }
}

fn wrap_double_starred(db: &Database, t: DbType) -> DbType {
    match &t {
        DbType::ParamSpecKwargs(_) => t,
        _ => DbType::new_class(
            db.python_state.dict_node_ref().as_link(),
            ClassGenerics::List(GenericsList::new_generics(Rc::new([
                GenericItem::TypeArgument(db.python_state.str_db_type()),
                GenericItem::TypeArgument(t),
            ]))),
        ),
    }
}

pub fn use_cached_simple_generic_type<'db>(
    db: &'db Database,
    file: &PythonFile,
    expr: Expression,
) -> Type<'db> {
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
) -> Type<'file> {
    file.inference(&InferenceState::new(db))
        .use_cached_annotation_or_type_comment_type_internal(
            annotation.index(),
            annotation.expression(),
        )
}

pub fn use_cached_annotation_or_type_comment<'db: 'file, 'file>(
    i_s: &InferenceState<'db, '_>,
    definition: NodeRef<'file>,
) -> Type<'file> {
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

fn check_named_tuple_name<'x, 'y>(
    i_s: &InferenceState,
    executable_name: &'static str,
    args: &'y dyn Arguments<'x>,
) -> Option<(StringSlice, NodeRef<'y>, Atom<'y>, ArgumentIterator<'x, 'y>)> {
    let mut iterator = args.iter();
    let Some(first_arg) = iterator.next() else {
        todo!()
    };
    let ArgumentKind::Positional { node_ref, .. } = first_arg.kind else {
        first_arg.as_node_ref().add_issue(i_s, IssueType::UnexpectedArgumentsTo { name: "namedtuple" });
        return None
    };
    let expr = node_ref.as_named_expression().expression();
    let first = expr
        .maybe_single_string_literal()
        .map(|py_string| (node_ref, py_string));
    let Some(string_slice) = StringSlice::from_string_in_expression(node_ref.file_index(), expr) else {
        node_ref.add_issue(i_s, IssueType::NamedTupleExpectsStringLiteralAsFirstArg { name: executable_name });
        return None
    };
    let Some(second_arg) = iterator.next() else {
        // TODO this is only done for namedtuple and not NamedTuple
        // Detected by execution of namedtuple
        return None
    };
    let ArgumentKind::Positional { node_ref, .. } = second_arg.kind else {
        todo!()
    };
    let ExpressionContent::ExpressionPart(ExpressionPart::Atom(atom)) = node_ref.as_named_expression().expression().unpack() else {
        todo!()
    };
    Some((string_slice, node_ref, atom, iterator))
}

pub fn new_typing_named_tuple(
    i_s: &InferenceState,
    args: &dyn Arguments,
) -> Option<Rc<NamedTuple>> {
    let Some((name, second_node_ref, atom, mut iterator)) = check_named_tuple_name(i_s, "NamedTuple", args) else {
        return None
    };
    if iterator.next().is_some() {
        args.as_node_ref().add_issue(
            i_s,
            IssueType::TooManyArguments(" for \"NamedTuple()\"".into()),
        );
        return None;
    }
    let list_iterator = match atom.unpack() {
        AtomContent::List(list) => list.unpack(),
        AtomContent::Tuple(tup) => tup.iter(),
        _ => {
            second_node_ref.add_issue(
                i_s,
                IssueType::InvalidSecondArgumentToNamedTuple { name: "NamedTuple" },
            );
            return None;
        }
    };
    let args_node_ref = args.as_node_ref();
    let on_type_var = &mut |i_s: &InferenceState, _: &_, _, _| TypeVarCallbackReturn::NotFound;
    let mut inference = args_node_ref.file.inference(i_s);
    let mut comp = TypeComputation::new(
        &mut inference,
        args.as_node_ref().as_link(),
        on_type_var,
        TypeComputationOrigin::Constraint,
    );
    if let Some(params) = comp.compute_named_tuple_initializer(args_node_ref, list_iterator) {
        check_named_tuple_has_no_fields_with_underscore(i_s, "NamedTuple", args, &params);
        let type_var_likes = comp.into_type_vars(|_, _| ());
        let callable = CallableContent {
            name: Some(name),
            class_name: None,
            defined_at: args_node_ref.as_link(),
            kind: FunctionKind::Function,
            type_vars: (!type_var_likes.is_empty()).then_some(type_var_likes),
            params: CallableParams::Simple(Rc::from(params)),
            result_type: DbType::Self_,
        };
        Some(Rc::new(NamedTuple::new(name, callable)))
    } else {
        None
    }
}

pub fn new_collections_named_tuple(
    i_s: &InferenceState,
    args: &dyn Arguments,
) -> Option<Rc<NamedTuple>> {
    let Some((name, second_node_ref, atom, mut iterator)) = check_named_tuple_name(i_s, "namedtuple", args) else {
        return None
    };
    if iterator.next().is_some() {
        return None;
    }
    let args_node_ref = args.as_node_ref();
    let mut params = start_namedtuple_params(i_s.db);

    let mut add_param = |name| {
        params.push(CallableParam {
            param_specific: ParamSpecific::PositionalOrKeyword(DbType::Any),
            name: Some(name),
            has_default: false,
        })
    };

    let mut add_from_iterator = |iterator| {
        for element in iterator {
            let StarLikeExpression::NamedExpression(ne) = element else {
            todo!()
        };
            let Some(string_slice) = StringSlice::from_string_in_expression(args_node_ref.file.file_index(), ne.expression()) else {
                NodeRef::new(second_node_ref.file, ne.index())
                    .add_issue(i_s, IssueType::StringLiteralExpectedAsNamedTupleItem);
                continue
            };
            add_param(string_slice)
        }
    };
    match atom.unpack() {
        AtomContent::List(list) => add_from_iterator(list.unpack()),
        AtomContent::Tuple(tup) => add_from_iterator(tup.iter()),
        AtomContent::Strings(s) => match s.maybe_single_string_literal() {
            Some(s) => {
                let (mut start, _) = s.content_start_and_end_in_literal();
                start += s.start();
                for part in s.content().split(&[',', ' ']) {
                    add_param(StringSlice::new(
                        args_node_ref.file_index(),
                        start,
                        start + part.len() as CodeIndex,
                    ));
                    start += part.len() as CodeIndex + 1;
                }
            }
            _ => todo!(),
        },
        _ => {
            second_node_ref.add_issue(
                i_s,
                IssueType::InvalidSecondArgumentToNamedTuple { name: "namedtuple" },
            );
            return None;
        }
    };
    check_named_tuple_has_no_fields_with_underscore(i_s, "namedtuple", args, &params);
    let callable = CallableContent {
        name: Some(name),
        class_name: None,
        defined_at: args_node_ref.as_link(),
        kind: FunctionKind::Function,
        type_vars: None,
        params: CallableParams::Simple(Rc::from(params)),
        result_type: DbType::Self_,
    };
    Some(Rc::new(NamedTuple::new(name, callable)))
}

fn check_named_tuple_has_no_fields_with_underscore(
    i_s: &InferenceState,
    name: &'static str,
    args: &dyn Arguments,
    params: &[CallableParam],
) {
    let field_names_with_underscore: Vec<_> = params
        .iter()
        .filter_map(|p| {
            p.name.and_then(|name| {
                let name_str = name.as_str(i_s.db);
                name_str.starts_with('_').then_some(name_str)
            })
        })
        .collect();
    if !field_names_with_underscore.is_empty() {
        args.as_node_ref().add_issue(
            i_s,
            IssueType::NamedTupleNamesCannotStartWithUnderscore {
                name,
                field_names: field_names_with_underscore.join(", ").into(),
            },
        );
    }
}
