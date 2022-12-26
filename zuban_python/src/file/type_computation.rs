use std::rc::Rc;

use parsa_python_ast::*;

use crate::database::{
    CallableContent, CallableParam, CallableParams, CallableWithParent, ComplexPoint, Database,
    DbType, DoubleStarredParamSpecific, GenericItem, GenericsList, Literal, Locality, NewType,
    ParamSpecArgument, ParamSpecUsage, ParamSpecific, Point, PointLink, PointType, RecursiveAlias,
    Specific, StarredParamSpecific, StringSlice, TupleContent, TypeAlias, TypeArguments,
    TypeOrTypeVarTuple, TypeVar, TypeVarLike, TypeVarLikeUsage, TypeVarLikes, TypeVarManager,
    TypeVarTupleUsage, TypeVarUsage, UnionEntry, UnionType,
};
use crate::debug;
use crate::diagnostics::IssueType;
use crate::file::File;
use crate::file::{Inference, PythonFile};
use crate::getitem::{SliceOrSimple, SliceType, SliceTypeIterator};
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::matching::{FormatData, Generics, ResultContext, Type};
use crate::node_ref::NodeRef;
use crate::value::{Class, Function, Module, Value};

pub enum TypeVarCallbackReturn {
    TypeVarLike(TypeVarLikeUsage<'static>),
    UnboundTypeVar,
    NotFound,
}

type MapAnnotationTypeCallback<'a> =
    Option<&'a dyn Fn(&mut TypeComputation, TypeContent) -> DbType>;

type TypeVarCallback<'db, 'x> = &'x mut dyn FnMut(
    &mut InferenceState<'db, '_>,
    &TypeVarManager,
    TypeVarLike,
    Option<PointLink>, // current_callable
) -> TypeVarCallbackReturn;
const ANNOTATION_TO_EXPR_DIFFERENCE: u32 = 2;

#[derive(Debug, Clone)]
pub(super) enum SpecialType {
    Union,
    Optional,
    Any,
    Protocol,
    ProtocolWithGenerics,
    Generic,
    GenericWithGenerics,
    Callable,
    Type,
    Tuple,
    Literal,
    LiteralString,
    Unpack,
    Concatenate,
    TypeAlias,
    MypyExtensionsParamType(Specific),
    CallableParam(CallableParam),
}

#[derive(Debug, Clone)]
pub(super) enum InvalidVariableType<'a> {
    List,
    Tuple { tuple_length: usize },
    Execution,
    Function(Function<'a>),
    Literal(&'a str),
    Variable(NodeRef<'a>),
    Other,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum TypeComputationOrigin {
    TypeAliasTypeCommentOrAnnotation,
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
        add_typing_issue: impl Fn(IssueType),
        origin: TypeComputationOrigin,
    ) {
        add_typing_issue(match self {
            Self::Variable(var_ref) => {
                add_typing_issue(IssueType::InvalidType(
                    format!(
                        "Variable \"{}.{}\" is not valid as a type",
                        var_ref.in_module(db).qualified_name(db),
                        var_ref.as_code().to_owned(),
                    )
                    .into(),
                ));
                IssueType::Note(
                    Box::from("See https://mypy.readthedocs.io/en/stable/common_issues.html#variables-vs-type-aliases"),
                )
            }
            Self::Execution => {
                IssueType::InvalidType(Box::from("Invalid type comment or annotation"))
            }
            Self::Function(func) => {
                add_typing_issue(IssueType::InvalidType(
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
                add_typing_issue(IssueType::InvalidType(Box::from(
                    "Bracketed expression \"[...]\" is not valid as a type",
                )));
                IssueType::Note(Box::from("Did you mean \"List[...]\"?"))
            }
            Self::Tuple { tuple_length } => {
                add_typing_issue(IssueType::InvalidType(Box::from(
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
            Self::Other => match origin {
                TypeComputationOrigin::CastTarget => IssueType::InvalidCastTarget,
                _ => todo!(),
            },
        })
    }
}

#[derive(Debug, Clone)]
enum TypeContent<'db, 'a> {
    Module(&'db PythonFile),
    ClassWithoutTypeVar(Inferred),
    TypeAlias(&'db TypeAlias),
    DbType(DbType),
    SpecialType(SpecialType),
    RecursiveAlias(PointLink),
    InvalidVariable(InvalidVariableType<'a>),
    TypeVarTuple(TypeVarTupleUsage),
    ParamSpec(ParamSpecUsage),
    Unpacked(TypeOrTypeVarTuple),
    Concatenate(CallableParams),
    Unknown,
}

pub(super) enum TypeNameLookup<'db, 'a> {
    Module(&'db PythonFile),
    Class(Inferred),
    TypeVarLike(TypeVarLike),
    TypeAlias(&'db TypeAlias),
    NewType(NewType),
    SpecialType(SpecialType),
    InvalidVariable(InvalidVariableType<'a>),
    RecursiveAlias(PointLink),
    Unknown,
}

#[derive(Debug)]
pub enum BaseClass {
    DbType(DbType),
    Protocol,
    Generic,
    Invalid,
}

macro_rules! compute_type_application {
    ($self:ident, $slice_type:expr, $from_alias_definition:expr, $method:ident $args:tt) => {{
        let mut on_type_var = |i_s: &mut InferenceState, _: &_, type_var_like: TypeVarLike, current_callable| {
            if let Some(class) = i_s.current_class() {
                if class
                    .type_vars(i_s)
                    .and_then(|t| t.find(type_var_like.clone(), class.node_ref.as_link()))
                    .is_some()
                {
                    if $from_alias_definition {
                        $slice_type.as_node_ref().add_typing_issue(
                            i_s.db,
                            IssueType::BoundTypeVarInAlias{
                                name: Box::from(type_var_like.name(i_s.db))
                            },
                        );
                    }
                }
            }
            if let Some(function) = i_s.current_function() {
                if function
                    .type_vars(i_s)
                    .and_then(|t| t.find(type_var_like.clone(), function.node_ref.as_link()))
                    .is_some()
                {
                    if $from_alias_definition {
                        $slice_type.as_node_ref().add_typing_issue(
                            i_s.db,
                            IssueType::BoundTypeVarInAlias{
                                name: Box::from(type_var_like.name(i_s.db))
                            },
                        );
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
        Inferred::new_unsaved_complex(match t {
            TypeContent::ClassWithoutTypeVar(inf) => return inf,
            TypeContent::DbType(mut db_type) => {
                let type_vars = tcomp.into_type_vars(|inf, recalculate_type_vars| {
                    db_type = recalculate_type_vars(&db_type);
                });
                if type_vars.len() > 0 {
                    ComplexPoint::TypeAlias(Box::new(TypeAlias::new(
                        type_vars,
                        $slice_type.as_node_ref().as_link(),
                        None,
                        Rc::new(db_type),
                        false,
                    )))
                } else {
                    ComplexPoint::TypeInstance(Box::new(DbType::Type(Rc::new(db_type))))
                }
            },
            _ => todo!("{t:?}"),
        })
    }}
}

pub(super) fn type_computation_for_variable_annotation(
    i_s: &mut InferenceState,
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

pub struct TypeComputation<'db, 'file, 'a, 'b, 'c> {
    inference: &'c mut Inference<'db, 'file, 'a, 'b>,
    for_definition: PointLink,
    current_callable: Option<PointLink>,
    type_var_manager: TypeVarManager,
    type_var_callback: TypeVarCallback<'db, 'c>,
    // This is only for type aliases. Type aliases are also allowed to be used by Python itself.
    // It's therefore unclear if type inference or type computation is needed. So once we encounter
    // a type alias we check in the database if the error was already calculated and set the flag.
    errors_already_calculated: bool,
    pub has_type_vars: bool,
    origin: TypeComputationOrigin,
    is_recursive_alias: bool,
}

impl<'db: 'x + 'file, 'file, 'a, 'b, 'c, 'x> TypeComputation<'db, 'file, 'a, 'b, 'c> {
    pub fn new(
        inference: &'c mut Inference<'db, 'file, 'a, 'b>,
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
            has_type_vars: false,
            origin,
            is_recursive_alias: false,
        }
    }

    fn compute_forward_reference(
        &mut self,
        start: CodeIndex,
        string: String,
    ) -> TypeContent<'db, 'db> {
        let f: &'db PythonFile =
            self.inference
                .file
                .new_annotation_file(self.inference.i_s.db, start, string);
        if let Some(star_exprs) = f.tree.maybe_star_expressions() {
            let compute_type =
                |comp: &mut TypeComputation<'db, '_, '_, '_, '_>| match star_exprs.unpack() {
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
                has_type_vars: false,
                origin: self.origin,
                is_recursive_alias: false,
            };
            let type_ = compute_type(&mut comp);
            self.type_var_manager = comp.type_var_manager;
            self.has_type_vars |= comp.has_type_vars;
            self.is_recursive_alias |= comp.is_recursive_alias;
            type_
        } else {
            debug!("Found non-expression in annotation: {}", f.tree.code());
            todo!()
        }
    }

    pub fn compute_base_class(&mut self, expr: Expression) -> BaseClass {
        let calculated = self.compute_type(expr);
        match calculated {
            TypeContent::SpecialType(SpecialType::GenericWithGenerics) => BaseClass::Generic,
            TypeContent::SpecialType(SpecialType::Protocol) => BaseClass::Protocol,
            TypeContent::SpecialType(SpecialType::ProtocolWithGenerics) => BaseClass::Protocol,
            TypeContent::SpecialType(SpecialType::Type) => {
                BaseClass::DbType(self.inference.i_s.db.python_state.type_of_any.clone())
            }
            TypeContent::Unknown => BaseClass::Invalid,
            TypeContent::ParamSpec(_) => {
                self.add_typing_issue_for_index(expr.index(), IssueType::InvalidBaseClass);
                BaseClass::Invalid
            }
            _ => {
                let db_type =
                    self.as_db_type(calculated, NodeRef::new(self.inference.file, expr.index()));
                if matches!(db_type, DbType::Class(_, _) | DbType::Tuple(_)) {
                    BaseClass::DbType(db_type)
                } else {
                    self.add_typing_issue_for_index(expr.index(), IssueType::InvalidBaseClass);
                    BaseClass::Invalid
                }
            }
        }
    }

    pub fn compute_annotation(&mut self, annotation: Annotation) {
        let expr = annotation.expression();
        match annotation.simple_param_kind() {
            Some(SimpleParamKind::Normal) | None => {
                self.cache_annotation_internal(annotation.index(), expr, None)
            }
            Some(SimpleParamKind::Starred) => self.cache_annotation_internal(
                annotation.index(),
                expr,
                Some(&|slf, t| {
                    wrap_starred(slf.as_db_type(t, NodeRef::new(self.inference.file, expr.index())))
                }),
            ),
            Some(SimpleParamKind::DoubleStarred) => self.cache_annotation_internal(
                annotation.index(),
                expr,
                Some(&|slf, t| {
                    wrap_double_starred(
                        self.inference.i_s.db,
                        slf.as_db_type(t, NodeRef::new(self.inference.file, expr.index())),
                    )
                }),
            ),
        };
    }

    pub fn compute_return_annotation(&mut self, annotation: ReturnAnnotation) {
        self.cache_annotation_internal(annotation.index(), annotation.expression(), None);
    }

    fn cache_annotation_internal(
        &mut self,
        annotation_index: NodeIndex,
        expr: Expression,
        map_type_callback: MapAnnotationTypeCallback,
    ) {
        let point = self.inference.file.points.get(annotation_index);
        if point.calculated() {
            return;
        }
        debug!(
            "Infer annotation expression class on {:?}: {:?}",
            self.inference.file.byte_to_line_column(expr.start()),
            expr.as_code()
        );

        let type_ = self.compute_type(expr);

        let db_type = match map_type_callback {
            Some(map_type_callback) => map_type_callback(self, type_),
            None => match type_ {
                TypeContent::ClassWithoutTypeVar(i) => {
                    debug_assert!(self.inference.file.points.get(expr.index()).calculated());
                    self.inference.file.points.set(
                        annotation_index,
                        Point::new_simple_specific(
                            Specific::AnnotationClassInstance,
                            Locality::Todo,
                        ),
                    );
                    return;
                }
                TypeContent::DbType(d) => {
                    if self.has_type_vars {
                        Inferred::new_unsaved_complex(ComplexPoint::TypeInstance(Box::new(d)))
                            .save_redirect(
                                self.inference.i_s.db,
                                self.inference.file,
                                expr.index(),
                            );
                        self.inference.file.points.set(
                            annotation_index,
                            Point::new_simple_specific(
                                Specific::AnnotationWithTypeVars,
                                Locality::Todo,
                            ),
                        );
                        return;
                    } else {
                        d
                    }
                }
                TypeContent::SpecialType(SpecialType::TypeAlias)
                    if self.origin == TypeComputationOrigin::TypeAliasTypeCommentOrAnnotation =>
                {
                    self.inference.file.points.set(
                        annotation_index,
                        Point::new_simple_specific(Specific::TypingTypeAlias, Locality::Todo),
                    );
                    return;
                }
                _ => self.as_db_type(type_, NodeRef::new(self.inference.file, expr.index())),
            },
        };
        let unsaved = Inferred::new_unsaved_complex(ComplexPoint::TypeInstance(Box::new(db_type)));
        unsaved.save_redirect(self.inference.i_s.db, self.inference.file, annotation_index);
    }

    fn as_db_type(&mut self, type_: TypeContent, node_ref: NodeRef) -> DbType {
        match type_ {
            TypeContent::ClassWithoutTypeVar(i) => i
                .maybe_class(self.inference.i_s)
                .unwrap()
                .as_db_type(self.inference.i_s),
            TypeContent::DbType(d) => d,
            TypeContent::Module(m) => {
                self.add_typing_issue(
                    node_ref,
                    IssueType::InvalidType(
                        format!(
                            "Module {:?} is not valid as a type",
                            Module::new(self.inference.i_s.db, m)
                                .qualified_name(self.inference.i_s.db),
                        )
                        .into(),
                    ),
                );
                self.add_typing_issue(
                    node_ref,
                    IssueType::Note(Box::from(
                        "Perhaps you meant to use a protocol matching the module structure?",
                    )),
                );
                DbType::Any
            }
            TypeContent::TypeAlias(a) => {
                self.is_recursive_alias = a.is_recursive;
                a.as_db_type_and_set_type_vars_any()
            }
            TypeContent::SpecialType(m) => match m {
                SpecialType::Callable => DbType::Callable(Box::new(CallableContent {
                    name: None,
                    class_name: None,
                    defined_at: node_ref.as_link(),
                    type_vars: None,
                    params: CallableParams::Any,
                    result_type: DbType::Any,
                })),
                SpecialType::Any => DbType::Any,
                SpecialType::Type => DbType::Type(Rc::new(DbType::Class(
                    self.inference.i_s.db.python_state.object().as_link(),
                    None,
                ))),
                SpecialType::Tuple => DbType::Tuple(TupleContent::new_empty()),
                SpecialType::LiteralString => DbType::Class(
                    self.inference.i_s.db.python_state.str_node_ref().as_link(),
                    None,
                ),
                SpecialType::Literal => {
                    self.add_typing_issue(
                        node_ref,
                        IssueType::InvalidType(Box::from(
                            "Literal[...] must have at least one parameter",
                        )),
                    );
                    DbType::Any
                }
                _ => {
                    self.add_typing_issue(
                        node_ref,
                        IssueType::InvalidType(Box::from("Invalid type")),
                    );
                    DbType::Any
                }
            },
            TypeContent::TypeVarTuple(t) => todo!(),
            TypeContent::ParamSpec(p) => {
                self.add_typing_issue(
                    node_ref,
                    IssueType::InvalidType(
                        format!(
                            "Invalid location for ParamSpec \"{}\"",
                            p.param_spec.name(self.inference.i_s.db),
                        )
                        .into(),
                    ),
                );
                self.add_typing_issue(
                    node_ref,
                    IssueType::Note(Box::from("You can use ParamSpec as the first argument to Callable, e.g., 'Callable[P, int]'"))
                );
                DbType::Any
            }
            TypeContent::Unpacked(t) => DbType::Any, // TODO Should probably raise an error?
            TypeContent::Concatenate(_) => {
                self.add_typing_issue(
                    node_ref,
                    IssueType::InvalidType(Box::from("Invalid location for Concatenate")),
                );
                self.add_typing_issue(
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
            TypeContent::InvalidVariable(t) => {
                t.add_issue(
                    self.inference.i_s.db,
                    |t| self.add_typing_issue(node_ref, t),
                    self.origin,
                );
                DbType::Any
            }
        }
    }

    fn compute_slice_type(&mut self, slice: SliceOrSimple<'x>) -> TypeContent<'db, 'x> {
        match slice {
            SliceOrSimple::Simple(s) => self.compute_type(s.named_expr.expression()),
            SliceOrSimple::Slice(n) => todo!(),
        }
    }

    fn compute_type(&mut self, expr: Expression<'x>) -> TypeContent<'db, 'x> {
        let type_content = match expr.unpack() {
            ExpressionContent::ExpressionPart(n) => self.compute_type_expression_part(n),
            ExpressionContent::Lambda(_) => todo!(),
            ExpressionContent::Ternary(t) => todo!(),
        };
        if !self.inference.file.points.get(expr.index()).calculated() {
            if let TypeContent::ClassWithoutTypeVar(inferred) = &type_content {
                inferred.clone().save_redirect(
                    self.inference.i_s.db,
                    self.inference.file,
                    expr.index(),
                );
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
                TypeContent::DbType(first.union(second))
            }
            _ => TypeContent::InvalidVariable(InvalidVariableType::Other),
        }
    }

    fn compute_type_primary(&mut self, primary: Primary<'x>) -> TypeContent<'db, 'x> {
        let base = self.compute_type_primary_or_atom(primary.first());
        match primary.second() {
            PrimaryContent::Attribute(name) => match base {
                TypeContent::Module(f) => {
                    let db = self.inference.i_s.db;
                    if let Some(index) = f.symbol_table.lookup_symbol(name.as_str()) {
                        self.inference.file.points.set(
                            name.index(),
                            Point::new_redirect(f.file_index(), index, Locality::Todo),
                        );
                        self.compute_type_name(name)
                    } else if let Some(file_index) =
                        Module::new(db, f).sub_module(db, name.as_str())
                    {
                        db.add_invalidates(file_index, self.inference.file.file_index());
                        self.inference.file.points.set(
                            name.index(),
                            Point::new_file_reference(file_index, Locality::Todo),
                        );
                        TypeContent::Module(db.loaded_python_file(file_index))
                    } else {
                        let node_ref = NodeRef::new(self.inference.file, primary.index());
                        debug!("TypeComputation: Attribute on class not found");
                        self.add_typing_issue_for_index(primary.index(), IssueType::TypeNotFound);
                        self.inference.file.points.set(
                            name.index(),
                            Point::new_unknown(f.file_index(), Locality::Todo),
                        );
                        TypeContent::Unknown
                    }
                }
                TypeContent::ClassWithoutTypeVar(i) => {
                    let cls = i.maybe_class(self.inference.i_s).unwrap();
                    let point_type = cache_name_on_class(cls, self.inference.file, name);
                    if point_type == PointType::Redirect {
                        self.compute_type_name(name)
                    } else {
                        debug!("TypeComputation: Attribute on class not found");
                        debug_assert_eq!(point_type, PointType::Unknown);
                        self.add_typing_issue_for_index(primary.index(), IssueType::TypeNotFound);
                        TypeContent::Unknown
                    }
                }
                TypeContent::DbType(t) => match t {
                    DbType::Class(c, g) => todo!(),
                    DbType::Any => TypeContent::DbType(DbType::Any),
                    _ => todo!("{primary:?} {t:?}"),
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
                TypeContent::Unknown => TypeContent::Unknown,
            },
            PrimaryContent::Execution(details) => match base {
                TypeContent::SpecialType(SpecialType::MypyExtensionsParamType(s)) => {
                    self.execute_mypy_extension_param(primary, s, details)
                }
                TypeContent::Unknown => TypeContent::Unknown,
                _ => TypeContent::InvalidVariable(InvalidVariableType::Execution),
            },
            PrimaryContent::GetItem(slice_type) => {
                let s = SliceType::new(self.inference.file, primary.index(), slice_type);
                match base {
                    TypeContent::ClassWithoutTypeVar(i) => {
                        let cls = i.maybe_class(self.inference.i_s).unwrap();
                        self.compute_type_get_item_on_class(cls, s, Some(primary))
                    }
                    TypeContent::DbType(d) => match d {
                        DbType::Any => TypeContent::DbType(d),
                        _ => TypeContent::InvalidVariable(InvalidVariableType::Other),
                    },
                    TypeContent::Module(m) => todo!("{primary:?}"),
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
                        SpecialType::Callable => self.compute_type_get_item_on_callable(s),
                        SpecialType::MypyExtensionsParamType(_) => todo!(),
                        SpecialType::CallableParam(_) => todo!(),
                        SpecialType::Literal => self.compute_get_item_on_literal(s),
                        SpecialType::LiteralString => todo!(),
                        SpecialType::TypeAlias => todo!(),
                        SpecialType::Unpack => self.compute_type_get_item_on_unpack(s),
                        SpecialType::Concatenate => self.compute_type_get_item_on_concatenate(s),
                    },
                    TypeContent::RecursiveAlias(link) => {
                        self.is_recursive_alias = true;
                        TypeContent::DbType(DbType::RecursiveAlias(Rc::new(RecursiveAlias::new(
                            link,
                            Some(self.compute_generics(s.iter())),
                        ))))
                    }
                    TypeContent::InvalidVariable(t) => {
                        t.add_issue(
                            self.inference.i_s.db,
                            |t| self.add_typing_issue(s.as_node_ref(), t),
                            self.origin,
                        );
                        TypeContent::Unknown
                    }
                    TypeContent::TypeVarTuple(_) => todo!(),
                    TypeContent::ParamSpec(_) => todo!(),
                    TypeContent::Unpacked(_) => todo!(),
                    TypeContent::Concatenate(_) => todo!(),
                    TypeContent::Unknown => TypeContent::Unknown,
                }
            }
        }
    }

    fn compute_generics(&mut self, s: SliceTypeIterator) -> GenericsList {
        let generics = s.map(|c| GenericItem::TypeArgument(self.compute_slice_db_type(c)));
        // TODO use type vars
        GenericsList::generics_from_vec(generics.collect())
    }

    fn check_restrictions(
        &mut self,
        class: Class,
        type_var: &TypeVar,
        s: &SliceOrSimple,
        type_: &TypeContent,
    ) {
        if let Some(bound) = &type_var.bound {
            // Performance: This could be optimized to not create new objects all the time.
            let t = self.as_db_type(type_.clone(), s.as_node_ref());
            let i_s = &mut self.inference.i_s;
            let actual = Type::new(&t);
            let expected = Type::new(bound);
            if !expected.is_simple_super_type_of(i_s, &actual).bool() {
                s.as_node_ref().add_typing_issue(
                    i_s.db,
                    IssueType::TypeVarBoundViolation {
                        actual: actual.format(&FormatData::new_short(i_s.db)),
                        executable: Box::from(class.name()),
                        expected: expected.format(&FormatData::new_short(i_s.db)),
                    },
                );
            }
        } else if !type_var.restrictions.is_empty() {
            let t2 = self.as_db_type(type_.clone(), s.as_node_ref());
            let i_s = &mut self.inference.i_s;
            let t2 = Type::new(&t2);
            if !type_var
                .restrictions
                .iter()
                .any(|t| Type::new(t).is_simple_super_type_of(i_s, &t2).bool())
            {
                s.as_node_ref().add_typing_issue(
                    i_s.db,
                    IssueType::InvalidTypeVarValue {
                        type_var_name: Box::from(type_var.name(i_s.db)),
                        func: format!("{:?}", class.name()).into(),
                        actual: t2.format(&FormatData::new_short(i_s.db)),
                    },
                );
            }
        }
    }

    fn compute_type_get_item_on_class(
        &mut self,
        class: Class,
        slice_type: SliceType,
        primary: Option<Primary>,
    ) -> TypeContent<'db, 'db> {
        if !matches!(class.generics(), Generics::None | Generics::Any) {
            todo!();
            //return TypeContent::InvalidVariable(InvalidVariableType::Other);
        }
        let type_vars = class.type_vars(self.inference.i_s);
        let expected_count = type_vars.map(|t| t.len()).unwrap_or(0);
        let mut given_count = 0;
        let mut had_valid_type_var_tuple = false;
        let mut generics = vec![];
        let mut iterator = slice_type.iter();
        let backfill = |inference: &mut Self, generics: &mut Vec<_>, count| {
            for slice_content in slice_type.iter().take(count) {
                generics.push(GenericItem::TypeArgument(
                    inference.compute_slice_db_type(slice_content),
                ));
            }
        };
        if let Some(type_vars) = type_vars {
            for type_var_like in type_vars.iter() {
                let generic_item = match type_var_like {
                    TypeVarLike::TypeVar(type_var) => {
                        if let Some(slice_content) = iterator.next() {
                            let t = self.compute_slice_type(slice_content);
                            self.check_restrictions(class, type_var, &slice_content, &t);
                            given_count += 1;
                            if generics.is_empty() {
                                if matches!(t, TypeContent::ClassWithoutTypeVar(_))
                                    && primary.is_some()
                                {
                                    continue;
                                } else {
                                    backfill(self, &mut generics, given_count - 1)
                                }
                            }
                            GenericItem::TypeArgument(
                                self.as_db_type(t, slice_content.as_node_ref()),
                            )
                        } else {
                            if generics.is_empty() {
                                backfill(self, &mut generics, given_count);
                            }
                            type_var_like.as_any_generic_item()
                        }
                    }
                    TypeVarLike::TypeVarTuple(_) => {
                        if generics.is_empty() {
                            backfill(self, &mut generics, given_count);
                        }
                        let fetch =
                            slice_type.iter().count() as isize + 1 - expected_count as isize;
                        GenericItem::TypeArguments(TypeArguments::new_fixed_length(
                            if let Ok(fetch) = fetch.try_into() {
                                had_valid_type_var_tuple = true;
                                iterator
                                    .by_ref()
                                    .take(fetch)
                                    .map(|s| self.compute_slice_type_or_type_var_tuple(s))
                                    .collect()
                            } else {
                                // If not enough type arguments are given, an error is raised elsewhere.
                                Box::new([])
                            },
                        ))
                    }
                    TypeVarLike::ParamSpec(_) => {
                        if generics.is_empty() {
                            backfill(self, &mut generics, given_count);
                        }
                        let params = self.calculate_callable_params(iterator.next().unwrap(), true);
                        given_count += 1;
                        GenericItem::ParamSpecArgument(ParamSpecArgument::new(params, None))
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
        let result = if generics.is_empty()
            && given_count == expected_count
            && self.origin == TypeComputationOrigin::ParamTypeCommentOrAnnotation
        {
            match primary {
                Some(primary) => TypeContent::ClassWithoutTypeVar(
                    Inferred::new_unsaved_specific(Specific::SimpleGeneric).save_if_unsaved(
                        self.inference.i_s.db,
                        self.inference.file,
                        primary.index(),
                    ),
                ),
                None => unreachable!(),
            }
        } else {
            TypeContent::DbType(match type_vars {
                None => DbType::Class(class.node_ref.as_link(), None),
                Some(type_vars) => {
                    // Need to fill the generics, because we might have been in a
                    // ClassWithoutTypeVar case where the generic count is wrong.
                    if generics.is_empty() {
                        backfill(self, &mut generics, given_count);
                        for missing_type_var in type_vars.iter().skip(given_count) {
                            generics.push(missing_type_var.as_any_generic_item())
                        }
                        generics.truncate(expected_count);
                    }
                    DbType::Class(
                        class.node_ref.as_link(),
                        Some(GenericsList::generics_from_vec(generics)),
                    )
                }
            })
        };
        if given_count != expected_count && !had_valid_type_var_tuple {
            self.add_typing_issue(
                slice_type.as_node_ref(),
                IssueType::TypeArgumentIssue {
                    class: Box::from(class.name()),
                    expected_count,
                    given_count,
                },
            );
        }
        result
    }

    fn compute_type_get_item_on_tuple(&mut self, slice_type: SliceType) -> TypeContent<'db, 'db> {
        let mut iterator = slice_type.iter();
        let first = iterator.next().unwrap();
        let generics: Box<[_]> = if let Some(slice_or_simple) = iterator.next() {
            if let SliceOrSimple::Simple(s) = slice_or_simple {
                if s.named_expr.is_ellipsis_literal() {
                    let t = self.compute_slice_db_type(first);
                    return TypeContent::DbType(DbType::Tuple(TupleContent::new_arbitrary_length(
                        t,
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
                    Box::new([])
                }
                _ => Box::new([self.convert_slice_type_or_type_var_tuple(t, first)]),
            }
        };
        TypeContent::DbType(DbType::Tuple(TupleContent::new_fixed_length(generics)))
    }

    fn calculate_callable_params(
        &mut self,
        first: SliceOrSimple,
        from_class_generics: bool,
    ) -> CallableParams {
        let SliceOrSimple::Simple(n) = first else {
            todo!();
        };
        let add_param = |slf: &mut Self,
                         params: &mut Vec<CallableParam>,
                         element: StarLikeExpression| {
            if let StarLikeExpression::NamedExpression(n) = element {
                let t = slf.compute_type(n.expression());
                let p = if let TypeContent::SpecialType(SpecialType::CallableParam(p)) = t {
                    p
                } else {
                    CallableParam {
                        param_specific: ParamSpecific::PositionalOnly(
                            slf.as_db_type(t, NodeRef::new(slf.inference.file, n.index())),
                        ),
                        has_default: false,
                        name: None,
                    }
                };
                if let Some(previous) = params.last() {
                    let prev_kind = previous.param_specific.param_kind();
                    let current_kind = p.param_specific.param_kind();
                    let msg = match current_kind {
                        ParamKind::PositionalOnly if current_kind < prev_kind || previous.has_default && !p.has_default => Some(
                            "Required positional args may not appear after default, named or var args",
                        ),
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
                        ParamKind::Starred if current_kind <= prev_kind => Some(
                            "Var args may not appear after named or var args",
                        ),
                        ParamKind::KeywordOnly if current_kind <= prev_kind => Some(
                            "A **kwargs argument must be the last argument"
                        ),
                        ParamKind::DoubleStarred if current_kind == prev_kind => Some(
                            "You may only have one **kwargs argument"
                        ),
                        _ => None,
                    };
                    if let Some(msg) = msg {
                        slf.add_typing_issue_for_index(
                            n.index(),
                            IssueType::InvalidType(Box::from(msg)),
                        );
                        return;
                    }

                    if let Some(param_name) = p.name {
                        let param_name = param_name.as_str(slf.inference.i_s.db);
                        for other in params.iter() {
                            if let Some(other_name) = other.name {
                                let other_name = other_name.as_str(slf.inference.i_s.db);
                                if param_name == other_name {
                                    slf.add_typing_issue_for_index(
                                        n.index(),
                                        IssueType::InvalidType(
                                            format!(
                                                "Duplicate argument \"{param_name}\" in Callable",
                                            )
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
            } else {
                todo!()
            }
        };

        let calc_params = |slf: &mut Self| match slf.compute_slice_type(first) {
            TypeContent::ParamSpec(p) => CallableParams::WithParamSpec(Box::new([]), p),
            TypeContent::SpecialType(SpecialType::Any) if from_class_generics => {
                CallableParams::Any
            }
            TypeContent::Unknown => CallableParams::Any,
            TypeContent::Concatenate(p) => p,
            _ => {
                slf.add_typing_issue(n.as_node_ref(), IssueType::InvalidCallableParams);
                CallableParams::Any
            }
        };
        if let ExpressionContent::ExpressionPart(ExpressionPart::Atom(atom)) =
            n.named_expr.expression().unpack()
        {
            match atom.unpack() {
                AtomContent::List(list) => {
                    let mut params = vec![];
                    if let Some(iterator) = list.unpack() {
                        for i in iterator {
                            add_param(self, &mut params, i)
                        }
                    }
                    CallableParams::Simple(params.into_boxed_slice())
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
            let params = self.calculate_callable_params(iterator.next().unwrap(), false);
            let result_type = iterator
                .next()
                .map(|slice_content| self.compute_slice_db_type(slice_content))
                .unwrap_or(DbType::Any);
            CallableContent {
                name: None,
                class_name: None,
                defined_at,
                type_vars: None,
                params,
                result_type,
            }
        } else {
            self.add_typing_issue(slice_type.as_node_ref(), IssueType::InvalidCallableArgCount);
            CallableContent {
                name: None,
                class_name: None,
                defined_at,
                type_vars: None,
                params: CallableParams::Any,
                result_type: DbType::Any,
            }
        };
        self.current_callable = old;
        TypeContent::DbType(DbType::Callable(Box::new(content)))
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
            todo!()
        }
        let mut t = self.compute_slice_db_type(first).union(DbType::None);
        match &mut t {
            DbType::Union(union_type) => union_type.format_as_optional = true,
            _ => unreachable!(),
        }
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
        let expected_count = alias.type_vars.len();
        let mut given_count = 0;
        let mut generics = vec![];
        for type_var_like in alias.type_vars.iter() {
            match type_var_like {
                TypeVarLike::TypeVar(_) => (),
                _ => todo!(),
            }
        }
        for slice_or_simple in slice_type.iter() {
            given_count += 1;
            generics.push(GenericItem::TypeArgument(
                self.compute_slice_db_type(slice_or_simple),
            ))
        }
        let mismatch = given_count != expected_count;
        if mismatch {
            self.add_typing_issue(
                slice_type.as_node_ref(),
                IssueType::TypeAliasArgumentIssue {
                    expected_count,
                    given_count,
                },
            );
        }
        self.is_recursive_alias |= alias.is_recursive;
        TypeContent::DbType(
            alias
                .replace_type_var_likes(false, &mut |usage| {
                    if mismatch {
                        usage.as_type_var_like().as_any_generic_item()
                    } else {
                        generics[usage.index().as_usize()].clone()
                    }
                })
                .into_owned(),
        )
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
                self.add_typing_issue(slice_type.as_node_ref(), IssueType::NestedConcatenate);
                TypeContent::Unknown
            }
            _ => todo!(),
        }
    }

    fn compute_get_item_on_literal(&mut self, slice_type: SliceType) -> TypeContent<'db, 'db> {
        let mut iterator = slice_type.iter();
        let first = iterator.next().unwrap();
        if iterator.next().is_some() {
            todo!()
        }
        if let SliceOrSimple::Simple(s) = first {
            if let ExpressionContent::ExpressionPart(ExpressionPart::Atom(atom)) =
                s.named_expr.expression().unpack()
            {
                let maybe = match atom.unpack() {
                    AtomContent::Int(i) => Some((i.index(), Specific::IntegerLiteral)),
                    AtomContent::Strings(s) => s
                        .maybe_single_string_literal()
                        .map(|s| (s.index(), Specific::StringLiteral)),
                    AtomContent::Boolean(keyword) => {
                        Some((keyword.index(), Specific::BooleanLiteral))
                    }
                    _ => None,
                };
                if let Some((index, specific)) = maybe {
                    let node_ref = NodeRef::new(self.inference.file, index);
                    node_ref.set_point(Point::new_simple_specific(specific, Locality::Todo));
                    return TypeContent::DbType(DbType::Literal(Literal {
                        definition: node_ref.as_link(),
                        implicit: false,
                    }));
                }
            }
        }
        match self.compute_slice_type(first) {
            TypeContent::Unknown => todo!(),
            TypeContent::SpecialType(SpecialType::Any) => todo!(),
            t => match self.as_db_type(t, first.as_node_ref()) {
                DbType::Any => TypeContent::Unknown,
                DbType::None => TypeContent::DbType(DbType::None),
                _ => todo!(),
            },
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
                self.add_typing_issue(s.as_node_ref(), IssueType::TypeVarExpected { class })
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
                Some(PythonString::Ref(start, s)) => {
                    self.compute_forward_reference(start, s.to_owned())
                }
                Some(PythonString::String(start, s)) => self.compute_forward_reference(start, s),
                Some(PythonString::FString) => todo!(),
                None => todo!(),
            },
            AtomContent::NoneLiteral => TypeContent::DbType(DbType::None),
            AtomContent::List(_) => TypeContent::InvalidVariable(InvalidVariableType::List),
            AtomContent::Int(n) => {
                TypeContent::InvalidVariable(InvalidVariableType::Literal(n.as_code()))
            }
            AtomContent::Tuple(t) => TypeContent::InvalidVariable(InvalidVariableType::Tuple {
                tuple_length: t.iter().count(),
            }),
            AtomContent::Ellipsis => TypeContent::InvalidVariable(InvalidVariableType::Other),
            _ => todo!("{atom:?}"),
        }
    }

    fn compute_type_name(&mut self, name: Name<'x>) -> TypeContent<'db, 'x> {
        match self.inference.lookup_type_name(name) {
            TypeNameLookup::Module(f) => TypeContent::Module(f),
            TypeNameLookup::Class(i) => TypeContent::ClassWithoutTypeVar(i),
            TypeNameLookup::TypeVarLike(type_var_like) => {
                self.has_type_vars = true;
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
                        node_ref.add_typing_issue(
                            self.inference.i_s.db,
                            IssueType::UnboundTypeVarLike {
                                type_var_like: type_var_like.clone(),
                            },
                        );
                        Some(TypeContent::DbType(DbType::Any))
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
                    if let Some(literal) = expr.maybe_single_string_literal() {
                        let (start, end) = literal.content_start_and_end_in_literal();
                        let s = literal.start();
                        Some(StringSlice::new(
                            self.inference.file.file_index(),
                            s + start,
                            s + end,
                        ))
                    } else {
                        if !expr.is_none_literal() {
                            todo!()
                        }
                        None
                    }
                };
                let type_from_expr = |slf: &mut Self, expr: Expression| {
                    let t = slf.compute_type(expr);
                    Some(slf.as_db_type(t, NodeRef::new(self.inference.file, expr.index())))
                };
                let arg = iterator.next().unwrap();
                match arg {
                    // The first arg is always there
                    Argument::Positional(n) => db_type = type_from_expr(self, n.expression()),
                    Argument::Keyword(key, expr) if key.as_code() == "type" => {
                        db_type = type_from_expr(self, expr)
                    }
                    Argument::Keyword(key, expr) if key.as_code() == "name" => {
                        name = name_from_expr(self, expr)
                    }
                    _ => (),
                };
                if let Some(named_arg) = iterator.next() {
                    match named_arg {
                        Argument::Positional(named_expr) => {
                            name = name_from_expr(self, named_expr.expression())
                        }
                        Argument::Keyword(key, expr) if key.as_code() == "name" => {
                            name = name_from_expr(self, expr)
                        }
                        Argument::Keyword(key, expr) if key.as_code() == "type" => {
                            db_type = type_from_expr(self, expr)
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

    pub fn into_type_vars<C>(self, on_type_var_recalculation: C) -> TypeVarLikes
    where
        C: FnOnce(&Inference, &dyn Fn(&DbType) -> DbType),
    {
        if self.type_var_manager.has_late_bound_type_vars() {
            on_type_var_recalculation(self.inference, &|t| {
                t.rewrite_late_bound_callables(&self.type_var_manager)
            })
        }
        self.type_var_manager.into_type_vars()
    }

    fn add_typing_issue(&self, node_ref: NodeRef, issue_type: IssueType) {
        if !self.errors_already_calculated {
            node_ref.add_typing_issue(self.inference.i_s.db, issue_type)
        }
    }

    fn add_typing_issue_for_index(&self, index: NodeIndex, issue_type: IssueType) {
        self.add_typing_issue(NodeRef::new(self.inference.file, index), issue_type)
    }
}

impl<'db: 'x, 'file, 'a, 'b, 'x> Inference<'db, 'file, 'a, 'b> {
    pub fn compute_type_application_on_class(
        &mut self,
        class: Class,
        slice_type: SliceType,
        //from_alias_definition: bool,
    ) -> Inferred {
        let from_alias_definition = true; // TODO add this
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
    ) -> Inferred {
        if !alias.is_class() {
            slice_type
                .as_node_ref()
                .add_typing_issue(self.i_s.db, IssueType::OnlyClassTypeApplication);
            return Inferred::new_any();
        }
        compute_type_application!(
            self,
            slice_type,
            false,
            compute_type_get_item_on_alias(alias, slice_type)
        )
    }

    pub fn compute_type_application_on_typing_class(
        &mut self,
        specific: Specific,
        slice_type: SliceType,
        //from_alias_definition: bool,
    ) -> Inferred {
        let from_alias_definition = true; // TODO add this
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
            _ => unreachable!("{:?}", specific),
        }
    }

    pub(super) fn use_cached_annotation(&mut self, annotation: Annotation) -> Inferred {
        if std::cfg!(debug_assertions) {
            let point = self.file.points.get(annotation.index());
            if point.type_() == PointType::Specific {
                if point.specific() != Specific::AnnotationClassInstance {
                    debug_assert_eq!(point.specific(), Specific::AnnotationWithTypeVars);
                }
            } else {
                debug_assert_eq!(point.type_(), PointType::Complex, "{annotation:?}");
                debug_assert!(matches!(
                    self.file.complex_points.get(point.complex_index()),
                    ComplexPoint::TypeInstance(_)
                ));
            }
        }
        self.check_point_cache(annotation.index()).unwrap()
    }

    pub fn use_cached_return_annotation(&mut self, annotation: ReturnAnnotation) -> Inferred {
        if std::cfg!(debug_assertions) {
            let point = self.file.points.get(annotation.index());
            assert!(point.calculated());
            if point.type_() == PointType::Specific {
                if point.specific() != Specific::AnnotationClassInstance {
                    debug_assert_eq!(point.specific(), Specific::AnnotationWithTypeVars);
                }
            } else {
                debug_assert_eq!(point.type_(), PointType::Complex, "{annotation:?}");
                debug_assert!(matches!(
                    self.file.complex_points.get(point.complex_index()),
                    ComplexPoint::TypeInstance(_)
                ));
            }
        }
        self.check_point_cache(annotation.index()).unwrap()
    }

    pub fn use_cached_return_annotation_type(
        &mut self,
        annotation: ReturnAnnotation,
    ) -> Type<'file> {
        self.use_cached_annotation_type_internal(annotation.index(), annotation.expression())
    }

    pub fn use_cached_annotation_type(&mut self, annotation: Annotation) -> Type<'file> {
        self.use_cached_annotation_type_internal(annotation.index(), annotation.expression())
    }

    fn use_cached_annotation_type_internal(
        &mut self,
        annotation_index: NodeIndex,
        expr: Expression,
    ) -> Type<'file> {
        let point = self.file.points.get(annotation_index);
        assert!(point.calculated(), "Expr: {:?}", expr);
        let complex_index = if point.type_() == PointType::Specific {
            if point.specific() == Specific::AnnotationClassInstance {
                return Type::Class(self.infer_expression(expr).maybe_class(self.i_s).unwrap());
            } else {
                debug_assert_eq!(point.specific(), Specific::AnnotationWithTypeVars);
                self.file.points.get(expr.index()).complex_index()
            }
        } else {
            debug_assert_eq!(point.type_(), PointType::Complex, "{expr:?}");
            debug_assert!(matches!(
                self.file.complex_points.get(point.complex_index()),
                ComplexPoint::TypeInstance(_)
            ));
            point.complex_index()
        };
        if let ComplexPoint::TypeInstance(db_type) = self.file.complex_points.get(complex_index) {
            Type::new(db_type)
        } else {
            unreachable!()
        }
    }

    pub fn use_cached_simple_generic_type(&mut self, expression: Expression) -> Type<'db> {
        debug_assert_eq!(
            self.file.points.get(expression.index()).type_(),
            PointType::Redirect
        );
        let inferred = self.check_point_cache(expression.index()).unwrap();
        Type::Class(inferred.maybe_class(self.i_s).unwrap())
    }

    pub fn use_db_type_of_annotation(&self, node_index: NodeIndex) -> &'file DbType {
        debug_assert_eq!(
            self.file.points.get(node_index).specific(),
            Specific::AnnotationWithTypeVars
        );
        // annotations look like `":" expr`
        let complex_index = self
            .file
            .points
            .get(node_index + ANNOTATION_TO_EXPR_DIFFERENCE)
            .complex_index();
        if let ComplexPoint::TypeInstance(db_type) = self.file.complex_points.get(complex_index) {
            db_type
        } else {
            unreachable!()
        }
    }

    pub fn recalculate_annotation_type_vars(
        &self,
        node_index: NodeIndex,
        recalculate: impl Fn(&DbType) -> DbType,
    ) {
        if self.file.points.get(node_index).specific() == Specific::AnnotationWithTypeVars {
            let new_t = recalculate(self.use_db_type_of_annotation(node_index));
            self.file.complex_points.insert(
                &self.file.points,
                node_index + ANNOTATION_TO_EXPR_DIFFERENCE,
                ComplexPoint::TypeInstance(Box::new(new_t)),
                Locality::Todo,
            )
        }
    }

    fn compute_type_assignment(
        &mut self,
        assignment: Assignment<'x>,
    ) -> TypeNameLookup<'file, 'file> {
        // Use the node star_targets or single_target, because they are not used otherwise.
        let file = self.file;
        let cached_type_node_ref = NodeRef::new(file, assignment.index() + 1);
        let point = cached_type_node_ref.point();
        if point.calculated() {
            return load_cached_type(cached_type_node_ref);
        } else if point.calculating() {
            // This means it's a recursive type definition.
            return TypeNameLookup::RecursiveAlias(cached_type_node_ref.as_link());
        }
        if let Some(name) = assignment.maybe_simple_type_reassignment() {
            // For very simple cases like `Foo = int`. Not sure yet if this going to stay.
            let node_ref = NodeRef::new(file, name.index());
            debug_assert!(node_ref.point().calculated());
            return check_type_name(self.i_s, node_ref);
        }
        if let Some((name_def, expr)) = assignment.maybe_simple_type_expression_assignment() {
            debug_assert!(file.points.get(name_def.index()).calculated());
            let inferred = self.check_point_cache(name_def.index()).unwrap();
            let in_definition = cached_type_node_ref.as_link();
            if let Some(tv) = inferred.maybe_type_var_like(self.i_s) {
                TypeNameLookup::TypeVarLike(tv)
            } else if let Some(n) = inferred.maybe_new_type(self.i_s) {
                TypeNameLookup::NewType(n)
            } else {
                cached_type_node_ref.set_point(Point::new_calculating());
                let mut type_var_manager = TypeVarManager::default();
                let mut type_var_callback =
                    |_: &mut InferenceState, _: &_, type_var_like: TypeVarLike, _| {
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
                let complex = match t {
                    TypeContent::ClassWithoutTypeVar(i) => {
                        cached_type_node_ref.set_point(Point::new_uncalculated());
                        return TypeNameLookup::Class(i);
                    }
                    TypeContent::InvalidVariable(t) => {
                        cached_type_node_ref.set_point(Point::new_uncalculated());
                        return TypeNameLookup::InvalidVariable(InvalidVariableType::Variable(
                            NodeRef::new(file, name_def.index()),
                        ));
                    }
                    _ => {
                        let node_ref = NodeRef::new(file, expr.index());
                        let db_type = comp.as_db_type(t, node_ref);
                        debug_assert!(!comp.type_var_manager.has_type_vars());
                        let is_recursive = comp.is_recursive_alias;
                        ComplexPoint::TypeAlias(Box::new(TypeAlias::new(
                            type_var_manager.into_type_vars(),
                            in_definition,
                            Some(PointLink::new(file.file_index(), name_def.name().index())),
                            Rc::new(db_type),
                            is_recursive,
                        )))
                    }
                };
                cached_type_node_ref.insert_complex(complex, Locality::Todo);
                load_cached_type(cached_type_node_ref)
            }
        } else {
            debug!("TODO invalid type def");
            TypeNameLookup::Unknown
        }
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
                .new_annotation_file(self.i_s.db, start, s.trim_end_matches('\\').to_owned());
        let mut inference = f.inference(self.i_s);
        if let Some(star_exprs) = f.tree.maybe_star_expressions() {
            match star_exprs.unpack() {
                StarExpressionContent::Expression(expr) => {
                    // It is kind of a hack to use the ANNOTATION_TO_EXPR_DIFFERENCE here. However this
                    // allows us to reuse the code for annotations completely and the nodes before the expr
                    // should really never be used by anything productive.
                    let index = expr.index() - ANNOTATION_TO_EXPR_DIFFERENCE;
                    if let Some(tuple) = expr.maybe_tuple() {
                        let db_type =
                            inference.calc_type_comment_tuple(assignment_node_ref, tuple.iter());
                        let unsaved = Inferred::new_unsaved_complex(ComplexPoint::TypeInstance(
                            Box::new(db_type),
                        ));
                        unsaved.save_redirect(inference.i_s.db, f, index);
                    } else {
                        let mut x = type_computation_for_variable_annotation;
                        let mut comp = TypeComputation::new(
                            &mut inference,
                            assignment_node_ref.as_link(),
                            &mut x,
                            TypeComputationOrigin::TypeAliasTypeCommentOrAnnotation,
                        );
                        comp.cache_annotation_internal(index, expr, None);
                        let type_vars = comp.into_type_vars(|inf, recalculate_type_vars| {
                            inf.recalculate_annotation_type_vars(index, recalculate_type_vars);
                        });
                        debug_assert!(type_vars.is_empty());
                    }
                    (
                        Inferred::new_saved2(f, index),
                        inference.use_cached_annotation_type_internal(index, expr),
                    )
                }
                StarExpressionContent::Tuple(t) => {
                    let index = star_exprs.index() - ANNOTATION_TO_EXPR_DIFFERENCE;
                    let db_type = inference.calc_type_comment_tuple(assignment_node_ref, t.iter());
                    let unsaved = Inferred::new_unsaved_complex(ComplexPoint::TypeInstance(
                        Box::new(db_type),
                    ));
                    unsaved.save_redirect(self.i_s.db, f, index);
                    let complex_index = f.points.get(index).complex_index();
                    (
                        Inferred::new_saved2(f, index),
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
            debug!("Found non-expression in annotation: {}", f.tree.code());
            todo!()
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
                        TypeComputationOrigin::TypeAliasTypeCommentOrAnnotation,
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
        DbType::Tuple(TupleContent::new_fixed_length(generics))
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
        Inferred::execute_db_type(self.i_s, db_type)
    }

    pub fn compute_type_var_constraint(&mut self, expr: Expression) -> Option<DbType> {
        let mut on_type_var = |_: &mut InferenceState, _: &_, type_var, current_callable| todo!();
        let node_ref = NodeRef::new(self.file, expr.index());
        let mut comp = TypeComputation::new(
            self,
            node_ref.as_link(),
            &mut on_type_var,
            TypeComputationOrigin::Constraint,
        );
        let t = comp.compute_type(expr);
        if matches!(t, TypeContent::InvalidVariable(_)) {
            // TODO this is a bit weird and should probably generate other errors
            node_ref.add_typing_issue(comp.inference.i_s.db, IssueType::TypeVarTypeExpected);
            return None;
        }
        (!comp.has_type_vars).then(|| comp.as_db_type(t, node_ref))
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
            ComplexPoint::TypeAlias(t) => TypeNameLookup::TypeAlias(t),
            ComplexPoint::TypeVarLike(t) => TypeNameLookup::TypeVarLike(t.clone()),
            _ => unreachable!(),
        }
    } else {
        let point = node_ref.point();
        if point.type_() == PointType::MultiDefinition {
            debug!("TODO check if this is the right place for this kind of stuff.");
            TypeNameLookup::InvalidVariable(InvalidVariableType::Variable(node_ref))
        } else {
            let specific = point.maybe_specific().unwrap();
            TypeNameLookup::SpecialType(match specific {
                Specific::TypingType => SpecialType::Type,
                Specific::TypingCallable => SpecialType::Callable,
                Specific::TypingLiteralString => SpecialType::LiteralString,
                Specific::TypingUnpack => SpecialType::Unpack,
                Specific::TypingConcatenateClass => SpecialType::Concatenate,
                Specific::TypingTypeAlias => SpecialType::TypeAlias,
                Specific::TypingLiteral => SpecialType::Literal,
                _ => unreachable!(),
            })
        }
    }
}

fn check_type_name<'db: 'file, 'file>(
    i_s: &mut InferenceState<'db, '_>,
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
                    _ => (),
                }
            }
            TypeNameLookup::Class(Inferred::new_saved(
                name_node_ref.file,
                c.index(),
                name_node_ref.file.points.get(c.index()),
            ))
        }
        TypeLike::Assignment(assignment) => {
            if name_node_ref.point().calculated() {
                // TODO This is mostly for loading Callable and other builtins. Should probably be
                //      changed/removed
                return load_cached_type(name_node_ref);
            }
            let def_point = name_node_ref
                .file
                .points
                .get(new_name.name_definition().unwrap().index());
            let mut inference = name_node_ref.file.inference(i_s);
            if !def_point.calculated() || def_point.maybe_specific() != Some(Specific::Cycle) {
                inference.cache_assignment_nodes(assignment);
            }
            inference.compute_type_assignment(assignment)
        }
        TypeLike::Function(f) => TypeNameLookup::InvalidVariable(InvalidVariableType::Function(
            Function::new(NodeRef::new(name_node_ref.file, f.index()), None),
        )),
        TypeLike::Import => {
            if point.calculated() {
                // When an import appears, this means that there's no redirect and the import leads
                // nowhere.
                debug_assert!(
                    point.type_() == PointType::Unknown
                        || point.type_() == PointType::MultiDefinition
                );
                TypeNameLookup::Unknown
            } else {
                name_node_ref.file.inference(i_s).infer_name(new_name);
                check_type_name(i_s, name_node_ref)
            }
        }
        TypeLike::Other => {
            todo!()
        }
    }
}

pub(super) fn cache_name_on_class(cls: Class, file: &PythonFile, name: Name) -> PointType {
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
            Point::new_unknown(cls.node_ref.file.file_index(), Locality::Todo)
        },
    );
    cache_name_on_class(cls, file, name)
}

fn wrap_starred(t: DbType) -> DbType {
    match &t {
        DbType::ParamSpecArgs(_) => t,
        _ => DbType::Tuple(TupleContent::new_arbitrary_length(t)),
    }
}

fn wrap_double_starred(db: &Database, t: DbType) -> DbType {
    match &t {
        DbType::ParamSpecKwargs(_) => t,
        _ => DbType::Class(
            db.python_state.builtins_point_link("dict"),
            Some(GenericsList::new_generics(Box::new([
                GenericItem::TypeArgument(DbType::Class(
                    db.python_state.builtins_point_link("str"),
                    None,
                )),
                GenericItem::TypeArgument(t),
            ]))),
        ),
    }
}
