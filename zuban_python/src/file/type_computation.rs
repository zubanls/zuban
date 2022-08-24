use std::rc::Rc;

use parsa_python_ast::*;

use crate::database::{
    CallableContent, CallableParam, CallableWithParent, ComplexPoint, Database, DbType,
    FormatStyle, GenericsList, Locality, Point, PointLink, PointType, Specific, TupleContent,
    TypeAlias, TypeVar, TypeVarManager, TypeVarUsage, TypeVars, UnionEntry, UnionType, Variance,
};
use crate::debug;
use crate::diagnostics::IssueType;
use crate::file::{PythonFile, PythonInference};
use crate::file_state::File;
use crate::getitem::{SliceOrSimple, SliceType, SliceTypeIterator};
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::matching::{Generics, Type};
use crate::node_ref::NodeRef;
use crate::value::{Class, Function, Module, Value};

type TypeVarCallback<'db, 'x> = &'x mut dyn FnMut(
    &mut InferenceState<'db, '_>,
    Rc<TypeVar>,
    NodeRef<'db>,
    Option<PointLink>, // current_callable
) -> Option<DbType>;
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
}

#[derive(Debug, Clone)]
pub(super) enum InvalidVariableType<'db, 'a> {
    List,
    Tuple { tuple_length: usize },
    Execution,
    Function(Function<'db, 'db>),
    Literal(&'a str),
    Variable(NodeRef<'db>),
    Other,
}

#[derive(Clone, Copy)]
enum TypeComputationOrigin {
    TypeCommentOrAnnotation,
    CastTarget,
}

impl InvalidVariableType<'_, '_> {
    fn add_issue(&self, db: &Database, node_ref: NodeRef, origin: TypeComputationOrigin) {
        match self {
            Self::Variable(var_ref) => {
                node_ref.add_typing_issue(
                    db,
                    IssueType::InvalidType(
                        format!(
                            "Variable \"{}.{}\" is not valid as a type",
                            var_ref.in_module(db).qualified_name(db),
                            var_ref.as_code().to_owned(),
                        )
                        .into(),
                    ),
                );
                node_ref.add_typing_issue(
                    db,
                    IssueType::Note(
                        Box::from("See https://mypy.readthedocs.io/en/stable/common_issues.html#variables-vs-type-aliases"),
                    ),
                );
            }
            Self::Execution => {
                todo!()
            }
            Self::Function(func) => {
                node_ref.add_typing_issue(
                    db,
                    IssueType::InvalidType(
                        format!(
                            "Function {:?} is not valid as a type",
                            func.qualified_name(db),
                        )
                        .into(),
                    ),
                );
                node_ref.add_typing_issue(
                    db,
                    IssueType::Note(Box::from(match func.name() {
                        "any" => "Perhaps you meant \"typing.Any\" instead of \"any\"?",
                        "callable" => {
                            "Perhaps you meant \"typing.Callable\" instead of \"callable\"?"
                        }
                        _ => "Perhaps you need \"Callable[...]\" or a callback protocol?",
                    })),
                );
            }
            Self::List => {
                node_ref.add_typing_issue(
                    db,
                    IssueType::InvalidType(Box::from(
                        "Bracketed expression \"[...]\" is not valid as a type",
                    )),
                );
                node_ref.add_typing_issue(
                    db,
                    IssueType::Note(Box::from("Did you mean \"List[...]\"?")),
                );
            }
            Self::Tuple { .. } => {
                node_ref.add_typing_issue(
                    db,
                    IssueType::InvalidType(Box::from("Syntax error in type annotation")),
                );
                node_ref.add_typing_issue(
                    db,
                    IssueType::Note(Box::from(
                        "Suggestion: Use Tuple[T1, ..., Tn] instead of (T1, ..., Tn)",
                    )),
                );
            }
            Self::Literal(s) => {
                node_ref.add_typing_issue(
                    db,
                    IssueType::InvalidType(
                        format!("Invalid type: try using Literal[{s}] instead?").into(),
                    ),
                );
            }
            Self::Other => node_ref.add_typing_issue(
                db,
                match origin {
                    TypeComputationOrigin::TypeCommentOrAnnotation => todo!(),
                    TypeComputationOrigin::CastTarget => IssueType::InvalidCastTarget,
                },
            ),
        }
    }
}

#[derive(Debug, Clone)]
enum TypeContent<'db, 'a> {
    Module(&'db PythonFile),
    ClassWithoutTypeVar(Inferred<'db>),
    TypeAlias(&'db TypeAlias),
    DbType(DbType),
    SpecialType(SpecialType),
    InvalidVariable(InvalidVariableType<'db, 'a>),
    Unknown,
}

pub(super) enum TypeNameLookup<'db, 'a> {
    Module(&'db PythonFile),
    Class(Inferred<'db>),
    TypeVar(Rc<TypeVar>),
    TypeAlias(&'db TypeAlias),
    SpecialType(SpecialType),
    InvalidVariable(InvalidVariableType<'db, 'a>),
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
    ($self:ident, $slice_type:expr, $method:ident $args:tt) => {{
        let mut tcomp = TypeComputation::new($self, $slice_type.as_node_ref().as_link(), None);
        let t = tcomp.$method $args;
        Inferred::new_unsaved_complex(match t {
            TypeContent::ClassWithoutTypeVar(inf) => return inf,
            TypeContent::DbType(mut db_type) => {
                let type_vars = tcomp.into_type_vars(|inf, recalculate_type_vars| {
                    db_type = recalculate_type_vars(&db_type);
                });
                if type_vars.len() > 0 {
                    ComplexPoint::TypeAlias(Box::new(TypeAlias {
                        type_vars,
                        location: $slice_type.as_node_ref().as_link(),
                        db_type: Rc::new(db_type),
                    }))
                } else {
                    ComplexPoint::TypeInstance(Box::new(DbType::Type(Box::new(db_type))))
                }
            },
            _ => todo!("{t:?}"),
        })
    }}
}

impl<'db> TypeContent<'db, '_> {
    fn union(self, i_s: &mut InferenceState<'db, '_>, other: Self) -> Self {
        let other_t = match other {
            Self::ClassWithoutTypeVar(i) => i.maybe_class(i_s).unwrap().as_db_type(i_s),
            Self::DbType(t) => t,
            Self::Module(m) => todo!(),
            Self::TypeAlias(m) => todo!(),
            Self::SpecialType(m) => todo!(),
            Self::Unknown => DbType::Any,
            Self::InvalidVariable(t) => return Self::InvalidVariable(t),
        };
        Self::DbType(match self {
            Self::ClassWithoutTypeVar(inf) => {
                inf.maybe_class(i_s).unwrap().as_db_type(i_s).union(other_t)
            }
            Self::DbType(t) => t.union(other_t),
            Self::Module(m) => todo!(),
            Self::TypeAlias(m) => todo!(),
            Self::SpecialType(s) => match s {
                // `Any | something` always is Any
                SpecialType::Any => DbType::Any,
                SpecialType::Type => DbType::Type(Box::new(DbType::Any)).union(other_t),
                _ => todo!("{s:?}"),
            },
            // `Any | something` always is Any
            Self::Unknown => DbType::Any,
            Self::InvalidVariable(t) => return Self::InvalidVariable(t),
        })
    }
}

pub(super) fn type_computation_for_variable_annotation(
    i_s: &mut InferenceState,
    type_var: Rc<TypeVar>,
    node_ref: NodeRef,
    current_callable: Option<PointLink>,
) -> Option<DbType> {
    if let Some(class) = i_s.current_class() {
        if let Some(usage) = class
            .type_vars(i_s)
            .and_then(|t| t.find(type_var.clone(), class.node_ref.as_link()))
        {
            return Some(DbType::TypeVar(usage));
        }
    }
    if let Some(func) = i_s.current_function() {
        if let Some(type_vars) = func.type_vars(i_s) {
            let usage = type_vars.find(type_var.clone(), func.node_ref.as_link());
            if let Some(usage) = usage {
                return Some(DbType::TypeVar(usage));
            }
        }
    }
    current_callable.is_none().then(|| {
        node_ref.add_typing_issue(i_s.db, IssueType::UnboundTypeVar { type_var });
        DbType::Any
    })
}

pub struct TypeComputation<'db, 'a, 'b, 'c> {
    inference: &'c mut PythonInference<'db, 'a, 'b>,
    for_definition: PointLink,
    current_callable: Option<PointLink>,
    type_var_manager: TypeVarManager,
    type_var_callback: Option<TypeVarCallback<'db, 'c>>,
    // This is only for type aliases. Type aliases are also allowed to be used by Python itself.
    // It's therefore unclear if type inference or type computation is needed. So once we encounter
    // a type alias we check in the database if the error was already calculated and set the flag.
    errors_already_calculated: bool,
    pub has_type_vars: bool,
    origin: TypeComputationOrigin,
}

impl<'db: 'x, 'a, 'b, 'c, 'x> TypeComputation<'db, 'a, 'b, 'c> {
    pub fn new(
        inference: &'c mut PythonInference<'db, 'a, 'b>,
        for_definition: PointLink,
        type_var_callback: Option<TypeVarCallback<'db, 'c>>,
    ) -> Self {
        Self {
            inference,
            for_definition,
            current_callable: None,
            type_var_manager: TypeVarManager::default(),
            type_var_callback,
            errors_already_calculated: false,
            has_type_vars: false,
            origin: TypeComputationOrigin::TypeCommentOrAnnotation,
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
                |comp: &mut TypeComputation<'db, '_, '_, '_>| match star_exprs.unpack() {
                    StarExpressionContent::Expression(expr) => comp.compute_type(expr),
                    StarExpressionContent::Tuple(t) => todo!(),
                    StarExpressionContent::StarExpression(s) => todo!(),
                };
            let old_manager = std::mem::take(&mut self.type_var_manager);
            // TODO why do we duplicate this code??? (answer because option<mut> sucks?)
            if let Some(type_var_callback) = self.type_var_callback.as_mut() {
                let mut comp = TypeComputation {
                    inference: &mut f.inference(self.inference.i_s),
                    type_var_manager: old_manager,
                    current_callable: self.current_callable,
                    for_definition: self.for_definition,
                    type_var_callback: Some(type_var_callback),
                    errors_already_calculated: self.errors_already_calculated,
                    has_type_vars: false,
                    origin: self.origin,
                };
                let type_ = compute_type(&mut comp);
                self.type_var_manager = comp.type_var_manager;
                self.has_type_vars |= comp.has_type_vars;
                type_
            } else {
                let mut comp = TypeComputation {
                    inference: &mut f.inference(self.inference.i_s),
                    type_var_manager: old_manager,
                    current_callable: self.current_callable,
                    for_definition: self.for_definition,
                    type_var_callback: None,
                    errors_already_calculated: self.errors_already_calculated,
                    has_type_vars: false,
                    origin: self.origin,
                };
                let type_ = compute_type(&mut comp);
                self.type_var_manager = comp.type_var_manager;
                self.has_type_vars |= comp.has_type_vars;
                type_
            }
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
                BaseClass::DbType(DbType::Type(Box::new(DbType::Any)))
            }
            TypeContent::Unknown => BaseClass::Invalid,
            _ => {
                let db_type =
                    self.as_db_type(calculated, NodeRef::new(self.inference.file, expr.index()));
                if matches!(db_type, DbType::Class(_, _) | DbType::Tuple(_)) {
                    BaseClass::DbType(db_type)
                } else {
                    NodeRef::new(self.inference.file, expr.index())
                        .add_typing_issue(self.inference.i_s.db, IssueType::InvalidBaseClass);
                    BaseClass::Invalid
                }
            }
        }
    }

    pub fn compute_annotation(&mut self, annotation: Annotation) {
        self.cache_annotation_internal(annotation.index(), annotation.expression());
    }

    pub fn compute_return_annotation(&mut self, annotation: ReturnAnnotation) {
        self.cache_annotation_internal(annotation.index(), annotation.expression());
    }

    fn cache_annotation_internal(&mut self, annotation_index: NodeIndex, expr: Expression) {
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

        let db_type = match type_ {
            TypeContent::ClassWithoutTypeVar(i) => {
                debug_assert!(self.inference.file.points.get(expr.index()).calculated());
                self.inference.file.points.set(
                    annotation_index,
                    Point::new_simple_specific(Specific::AnnotationClassInstance, Locality::Todo),
                );
                return;
            }
            TypeContent::DbType(d) => {
                if self.has_type_vars {
                    Inferred::new_unsaved_complex(ComplexPoint::TypeInstance(Box::new(d)))
                        .save_redirect(self.inference.file, expr.index());
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
            _ => self.as_db_type(type_, NodeRef::new(self.inference.file, expr.index())),
        };
        let unsaved = Inferred::new_unsaved_complex(ComplexPoint::TypeInstance(Box::new(db_type)));
        unsaved.save_redirect(self.inference.file, annotation_index);
    }

    fn as_db_type(&mut self, type_: TypeContent<'db, '_>, node_ref: NodeRef<'db>) -> DbType {
        match type_ {
            TypeContent::ClassWithoutTypeVar(i) => i
                .maybe_class(self.inference.i_s)
                .unwrap()
                .as_db_type(self.inference.i_s),
            TypeContent::DbType(d) => d,
            TypeContent::Module(m) => {
                if !self.errors_already_calculated {
                    node_ref.add_typing_issue(
                        self.inference.i_s.db,
                        IssueType::InvalidType(
                            format!(
                                "Module {:?} is not valid as a type",
                                Module::new(self.inference.i_s.db, m)
                                    .qualified_name(self.inference.i_s.db),
                            )
                            .into(),
                        ),
                    );
                }
                DbType::Any
            }
            TypeContent::TypeAlias(a) => a.as_db_type(),
            TypeContent::SpecialType(m) => match m {
                SpecialType::Callable => DbType::Callable(Box::new(CallableContent {
                    defined_at: node_ref.as_link(),
                    type_vars: None,
                    params: None,
                    return_class: DbType::Any,
                })),
                SpecialType::Any => DbType::Any,
                SpecialType::Type => DbType::Type(Box::new(DbType::Class(
                    self.inference.i_s.db.python_state.object().as_link(),
                    None,
                ))),
                SpecialType::Tuple => DbType::Tuple(TupleContent {
                    generics: None,
                    arbitrary_length: true,
                }),
                _ => todo!("{m:?}"),
            },
            TypeContent::Unknown => DbType::Any,
            TypeContent::InvalidVariable(t) => {
                if !self.errors_already_calculated {
                    t.add_issue(self.inference.i_s.db, node_ref, self.origin);
                }
                DbType::Any
            }
        }
    }

    fn compute_slice_type(&mut self, slice: SliceOrSimple<'x, 'x>) -> TypeContent<'db, 'x> {
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
                inferred
                    .clone()
                    .save_redirect(self.inference.file, expr.index());
            }
        }
        type_content
    }

    fn compute_slice_db_type(&mut self, slice: SliceOrSimple<'db, '_>) -> DbType {
        let t = self.compute_slice_type(slice);
        self.as_db_type(t, slice.as_node_ref())
    }

    fn compute_type_expression_part(&mut self, node: ExpressionPart<'x>) -> TypeContent<'db, 'x> {
        match node {
            ExpressionPart::Atom(atom) => self.compute_type_atom(atom),
            ExpressionPart::Primary(primary) => self.compute_type_primary(primary),
            ExpressionPart::BitwiseOr(bitwise_or) => {
                let (a, b) = bitwise_or.unpack();
                // TODO this should only merge in annotation contexts
                let other = self.compute_type_expression_part(b);
                self.compute_type_expression_part(a)
                    .union(self.inference.i_s, other)
            }
            _ => TypeContent::InvalidVariable(InvalidVariableType::Other),
        }
    }

    fn compute_type_primary(&mut self, primary: Primary<'x>) -> TypeContent<'db, 'x> {
        let base = self.compute_type_primary_or_atom(primary.first());
        match primary.second() {
            PrimaryContent::Attribute(name) => {
                match base {
                    TypeContent::Module(f) => {
                        // TODO this is a bit weird. shouldn't this just do a goto?
                        if let Some(index) = f.symbol_table.lookup_symbol(name.as_str()) {
                            self.inference.file.points.set(
                                name.index(),
                                Point::new_redirect(f.file_index(), index, Locality::Todo),
                            );
                            self.compute_type_name(name)
                        } else {
                            let node_ref = NodeRef::new(self.inference.file, primary.index());
                            if !self.errors_already_calculated {
                                node_ref.add_typing_issue(
                                    self.inference.i_s.db,
                                    IssueType::TypeNotFound,
                                );
                                self.inference.file.points.set(
                                    name.index(),
                                    Point::new_unknown(f.file_index(), Locality::Todo),
                                );
                            }
                            TypeContent::Unknown
                        }
                    }
                    TypeContent::ClassWithoutTypeVar(i) => {
                        let cls = i.maybe_class(self.inference.i_s).unwrap();
                        let point_type = cache_name_on_class(cls, self.inference.file, name);
                        if point_type == PointType::Redirect {
                            self.compute_type_name(name)
                        } else {
                            debug_assert_eq!(point_type, PointType::Unknown);
                            let node_ref = NodeRef::new(self.inference.file, primary.index());
                            node_ref
                                .add_typing_issue(self.inference.i_s.db, IssueType::TypeNotFound);
                            TypeContent::Unknown
                        }
                    }
                    TypeContent::DbType(t) => match t {
                        DbType::Class(c, g) => todo!(),
                        DbType::Any => TypeContent::DbType(DbType::Any),
                        _ => todo!("{primary:?} {t:?}"),
                    },
                    TypeContent::TypeAlias(m) => todo!(),
                    TypeContent::SpecialType(m) => todo!(),
                    TypeContent::InvalidVariable(t) => TypeContent::InvalidVariable(t),
                    TypeContent::Unknown => TypeContent::Unknown,
                }
            }
            PrimaryContent::Execution(details) => {
                TypeContent::InvalidVariable(InvalidVariableType::Execution)
            }
            PrimaryContent::GetItem(slice_type) => {
                let s = SliceType::new(self.inference.file, primary.index(), slice_type);
                match base {
                    TypeContent::ClassWithoutTypeVar(i) => {
                        let cls = i.maybe_class(self.inference.i_s).unwrap();
                        self.compute_type_get_item_on_class(cls, s, Some(primary))
                    }
                    TypeContent::DbType(d) => match d {
                        DbType::Any => TypeContent::DbType(d),
                        _ => todo!("{d:?}"),
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
                            self.expect_type_var_args(s, "Protocol");
                            TypeContent::SpecialType(SpecialType::ProtocolWithGenerics)
                        }
                        SpecialType::ProtocolWithGenerics => todo!(),
                        SpecialType::Generic => {
                            self.expect_type_var_args(s, "Generic");
                            TypeContent::SpecialType(SpecialType::GenericWithGenerics)
                        }
                        SpecialType::GenericWithGenerics => todo!(),
                        SpecialType::Callable => self.compute_type_get_item_on_callable(s),
                    },
                    TypeContent::InvalidVariable(t) => todo!(),
                    TypeContent::Unknown => TypeContent::Unknown,
                }
            }
        }
    }

    fn compute_type_get_item_on_class(
        &mut self,
        class: Class<'db, '_>,
        slice_type: SliceType<'db, 'x>,
        primary: Option<Primary>,
    ) -> TypeContent<'db, 'x> {
        if !matches!(class.generics(), Generics::None) {
            return TypeContent::InvalidVariable(InvalidVariableType::Other);
        }
        let type_vars = class.type_vars(self.inference.i_s);
        let expected_count = type_vars.map(|t| t.len()).unwrap_or(0);
        let mut given_count = 0;
        let mut generics = vec![];
        let mut iterator = slice_type.iter();
        let backfill = |inference: &mut Self, generics: &mut Vec<_>, count| {
            for slice_content in slice_type.iter().take(count) {
                generics.push(inference.compute_slice_db_type(slice_content));
            }
        };
        if let Some(type_vars) = type_vars {
            for type_var in type_vars.iter() {
                let db_type = if let Some(slice_content) = iterator.next() {
                    let t = self.compute_slice_type(slice_content);
                    if let Some(bound) = &type_var.bound {
                        // Performance: This could be optimized to not create new objects all the time.
                        let t = self.as_db_type(t.clone(), slice_content.as_node_ref());
                        let i_s = &mut self.inference.i_s;
                        let actual = Type::new(&t);
                        let expected = Type::new(bound);
                        if !expected
                            .matches(i_s, None, &actual, Variance::Covariant)
                            .bool()
                        {
                            slice_content.as_node_ref().add_typing_issue(
                                i_s.db,
                                IssueType::TypeVarBoundViolation {
                                    actual: actual.format(i_s, None, FormatStyle::Short),
                                    executable: Box::from(class.name()),
                                    expected: expected.format(i_s, None, FormatStyle::Short),
                                },
                            );
                        }
                    } else if !type_var.restrictions.is_empty() {
                        let t2 = self.as_db_type(t.clone(), slice_content.as_node_ref());
                        let i_s = &mut self.inference.i_s;
                        let t2 = Type::new(&t2);
                        if !type_var.restrictions.iter().any(|t| {
                            Type::new(t)
                                .matches(i_s, None, &t2, Variance::Covariant)
                                .bool()
                        }) {
                            slice_content.as_node_ref().add_typing_issue(
                                i_s.db,
                                IssueType::InvalidTypeVarValue {
                                    type_var: Box::from(type_var.name(i_s.db)),
                                    func: format!("{:?}", class.name()).into(),
                                    actual: t2.format(i_s, None, FormatStyle::Short),
                                },
                            );
                        }
                    }
                    given_count += 1;
                    if generics.is_empty() {
                        if matches!(t, TypeContent::ClassWithoutTypeVar(_)) && primary.is_some() {
                            continue;
                        } else {
                            backfill(self, &mut generics, given_count - 1)
                        }
                    }
                    self.as_db_type(t, slice_content.as_node_ref())
                } else {
                    for slice_content in slice_type.iter().take(given_count) {
                        generics.push(self.compute_slice_db_type(slice_content));
                    }
                    DbType::Any
                };
                generics.push(db_type);
            }
        }
        for slice_content in iterator {
            // Still calculate errors for the rest of the types given. After all they are still
            // expected to be types.
            self.compute_slice_db_type(slice_content);
            given_count += 1;
        }
        let result = if generics.is_empty() && given_count == expected_count {
            match primary {
                Some(primary) => TypeContent::ClassWithoutTypeVar(
                    Inferred::new_unsaved_specific(Specific::SimpleGeneric)
                        .save_if_unsaved(self.inference.file, primary.index()),
                ),
                None => unreachable!(),
            }
        } else {
            TypeContent::DbType(match expected_count {
                0 => DbType::Class(class.node_ref.as_link(), None),
                _ => {
                    // Need to fill the generics, because we might have been in a
                    // ClassWithoutTypeVar case.
                    if generics.is_empty() {
                        backfill(self, &mut generics, expected_count);
                        generics.resize(expected_count, DbType::Any);
                    }
                    DbType::Class(
                        class.node_ref.as_link(),
                        Some(GenericsList::generics_from_vec(generics)),
                    )
                }
            })
        };
        if given_count != expected_count && !self.errors_already_calculated {
            slice_type.as_node_ref().add_typing_issue(
                self.inference.i_s.db,
                IssueType::TypeArgumentIssue {
                    class: Box::from(class.name()),
                    expected_count,
                    given_count,
                },
            );
        }
        result
    }

    fn compute_type_get_item_on_tuple(
        &mut self,
        slice_type: SliceType<'db, 'x>,
    ) -> TypeContent<'db, 'x> {
        let mut iterator = slice_type.iter();
        let first = iterator.next().unwrap();
        let generics: Box<[_]> = if let Some(slice_or_simple) = iterator.next() {
            if let SliceOrSimple::Simple(s) = slice_or_simple {
                if s.named_expr.is_ellipsis_literal() {
                    let t = self.compute_slice_db_type(first);
                    return TypeContent::DbType(DbType::Tuple(TupleContent {
                        generics: Some(GenericsList::new_generics(Box::new([t]))),
                        arbitrary_length: true,
                    }));
                }
            }
            slice_type
                .iter()
                .map(|slice_content| self.compute_slice_db_type(slice_content))
                .collect()
        } else {
            let t = self.compute_slice_type(first);
            // Handle Tuple[()]
            match t {
                TypeContent::InvalidVariable(InvalidVariableType::Tuple { tuple_length: 0 }) => {
                    Box::new([])
                }
                _ => Box::new([self.as_db_type(t, first.as_node_ref())]),
            }
        };
        TypeContent::DbType(DbType::Tuple(TupleContent {
            generics: Some(GenericsList::new_generics(generics)),
            arbitrary_length: false,
        }))
    }

    fn compute_type_get_item_on_callable(
        &mut self,
        slice_type: SliceType<'db, 'x>,
    ) -> TypeContent<'db, 'x> {
        let defined_at = slice_type.as_node_ref().as_link();
        self.type_var_manager.register_callable(CallableWithParent {
            defined_at,
            parent_callable: self.current_callable,
        });
        let old = std::mem::replace(&mut self.current_callable, Some(defined_at));

        let mut params = Some(vec![]);
        let db = self.inference.i_s.db;
        let mut add_param = |params: &mut Option<Vec<CallableParam>>,
                             element: StarLikeExpression| {
            if let StarLikeExpression::NamedExpression(n) = element {
                let t = self.compute_type(n.expression());
                params.as_mut().unwrap().push(CallableParam {
                    param_type: ParamType::PositionalOnly,
                    has_default: false,
                    name: None,
                    db_type: self.as_db_type(t, NodeRef::new(self.inference.file, n.index())),
                })
            } else {
                todo!()
            }
        };

        let content = if slice_type.iter().count() == 2 {
            let mut iterator = slice_type.iter();
            let param_node = iterator.next().map(|slice_content| match slice_content {
                SliceOrSimple::Simple(n) => {
                    if let ExpressionContent::ExpressionPart(ExpressionPart::Atom(atom)) =
                        n.named_expr.expression().unpack()
                    {
                        match atom.unpack() {
                            AtomContent::List(list) => {
                                if let Some(iterator) = list.unpack() {
                                    for i in iterator {
                                        add_param(&mut params, i)
                                    }
                                }
                            }
                            AtomContent::Ellipsis => params = None,
                            _ => {
                                n.as_node_ref()
                                    .add_typing_issue(db, IssueType::InvalidCallableParams);
                                params = None
                            }
                        }
                    }
                }
                SliceOrSimple::Slice(s) => todo!(),
            });
            let return_class = iterator
                .next()
                .map(|slice_content| self.compute_slice_db_type(slice_content))
                .unwrap_or(DbType::Any);
            CallableContent {
                defined_at,
                type_vars: None,
                params: params.map(|p| p.into_boxed_slice()),
                return_class,
            }
        } else {
            slice_type
                .as_node_ref()
                .add_typing_issue(db, IssueType::InvalidCallableArgCount);
            CallableContent {
                defined_at,
                type_vars: None,
                params: None,
                return_class: DbType::Any,
            }
        };
        self.current_callable = old;
        TypeContent::DbType(DbType::Callable(Box::new(content)))
    }

    fn compute_type_get_item_on_union(
        &mut self,
        slice_type: SliceType<'db, 'x>,
    ) -> TypeContent<'db, 'x> {
        let iterator = slice_type.iter();
        if let SliceTypeIterator::SliceOrSimple(s) = iterator {
            self.compute_slice_type(s)
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
        slice_type: SliceType<'db, 'x>,
    ) -> TypeContent<'db, 'x> {
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

    fn compute_type_get_item_on_type(
        &mut self,
        slice_type: SliceType<'db, 'x>,
    ) -> TypeContent<'db, 'x> {
        let mut iterator = slice_type.iter();
        let content = iterator.next().unwrap();
        if iterator.count() > 0 {
            todo!()
        }
        TypeContent::DbType(DbType::Type(Box::new(self.compute_slice_db_type(content))))
    }

    fn compute_type_get_item_on_alias(
        &mut self,
        alias: &TypeAlias,
        slice_type: SliceType<'db, 'x>,
    ) -> TypeContent<'db, 'x> {
        let expected_count = alias.type_vars.len();
        let mut given_count = 0;
        let mut generics = vec![];
        for slice_or_simple in slice_type.iter() {
            given_count += 1;
            generics.push(self.compute_slice_db_type(slice_or_simple))
        }
        let mismatch = given_count != expected_count;
        if mismatch {
            slice_type.as_node_ref().add_typing_issue(
                self.inference.i_s.db,
                IssueType::TypeAliasArgumentIssue {
                    expected_count,
                    given_count,
                },
            );
        }
        TypeContent::DbType(alias.db_type.replace_type_vars(&mut |usage| {
            if mismatch {
                DbType::Any
            } else {
                generics[usage.index.as_usize()].clone()
            }
        }))
    }

    fn expect_type_var_args(&mut self, slice_type: SliceType<'db, '_>, class: &'static str) {
        for (i, s) in slice_type.iter().enumerate() {
            if !matches!(
                self.compute_slice_type(s),
                TypeContent::DbType(DbType::TypeVar(usage))
                    if usage.in_definition == self.for_definition
            ) {
                s.as_node_ref()
                    .add_typing_issue(self.inference.i_s.db, IssueType::TypeVarExpected { class })
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
                Some(PythonString::String(start, s)) => todo!(),
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
            _ => todo!("{atom:?}"),
        }
    }

    fn compute_type_name(&mut self, name: Name<'x>) -> TypeContent<'db, 'x> {
        match self.inference.lookup_type_name(name) {
            TypeNameLookup::Module(f) => TypeContent::Module(f),
            TypeNameLookup::Class(i) => TypeContent::ClassWithoutTypeVar(i),
            TypeNameLookup::TypeVar(type_var) => {
                self.has_type_vars = true;
                TypeContent::DbType({
                    self.type_var_callback
                        .as_mut()
                        .and_then(|callback| {
                            callback(
                                self.inference.i_s,
                                type_var.clone(),
                                NodeRef::new(self.inference.file, name.index()),
                                self.current_callable,
                            )
                        })
                        .unwrap_or_else(|| {
                            let index = self
                                .type_var_manager
                                .add(type_var.clone(), self.current_callable);
                            DbType::TypeVar(TypeVarUsage {
                                type_var,
                                index,
                                in_definition: self.for_definition,
                            })
                        })
                })
            }
            TypeNameLookup::TypeAlias(alias) => TypeContent::TypeAlias(alias),
            TypeNameLookup::InvalidVariable(t) => TypeContent::InvalidVariable(t),
            TypeNameLookup::Unknown => TypeContent::Unknown,
            TypeNameLookup::SpecialType(special) => TypeContent::SpecialType(special),
        }
    }

    pub fn into_type_vars<C>(self, mut on_type_var_recalculation: C) -> TypeVars
    where
        C: FnMut(&PythonInference<'db, '_, '_>, &dyn Fn(&DbType) -> DbType),
    {
        if self.type_var_manager.has_late_bound_type_vars() {
            on_type_var_recalculation(self.inference, &|t| {
                t.rewrite_late_bound_callables(&self.type_var_manager)
            })
        }
        self.type_var_manager.into_type_vars()
    }
}

impl<'db: 'x, 'a, 'b, 'x> PythonInference<'db, 'a, 'b> {
    pub fn compute_type_application_on_class(
        &mut self,
        class: Class<'db, '_>,
        slice_type: SliceType<'db, '_>,
    ) -> Inferred<'db> {
        compute_type_application!(
            self,
            slice_type,
            compute_type_get_item_on_class(class, slice_type, None)
        )
    }

    pub fn compute_type_application_on_alias(
        &mut self,
        alias: &TypeAlias,
        slice_type: SliceType<'db, '_>,
    ) -> Inferred<'db> {
        if !matches!(alias.db_type.as_ref(), DbType::Class(_, _)) {
            slice_type
                .as_node_ref()
                .add_typing_issue(self.i_s.db, IssueType::OnlyClassTypeApplication);
            return Inferred::new_any();
        }
        compute_type_application!(
            self,
            slice_type,
            compute_type_get_item_on_alias(alias, slice_type)
        )
    }

    pub fn compute_type_application_on_typing_class(
        &mut self,
        specific: Specific,
        slice_type: SliceType<'db, '_>,
    ) -> Inferred<'db> {
        match specific {
            Specific::TypingGeneric | Specific::TypingProtocol => {
                todo!()
            }
            Specific::TypingTuple => {
                compute_type_application!(
                    self,
                    slice_type,
                    compute_type_get_item_on_tuple(slice_type)
                )
            }
            Specific::TypingCallable => {
                compute_type_application!(
                    self,
                    slice_type,
                    compute_type_get_item_on_callable(slice_type)
                )
            }
            Specific::TypingUnion => {
                compute_type_application!(
                    self,
                    slice_type,
                    compute_type_get_item_on_union(slice_type)
                )
            }
            Specific::TypingOptional => {
                compute_type_application!(
                    self,
                    slice_type,
                    compute_type_get_item_on_optional(slice_type)
                )
            }
            Specific::TypingType => {
                compute_type_application!(
                    self,
                    slice_type,
                    compute_type_get_item_on_type(slice_type)
                )
            }
            _ => unreachable!("{:?}", specific),
        }
    }

    pub(super) fn use_cached_annotation(&mut self, annotation: Annotation) -> Inferred<'db> {
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
        self.check_point_cache(annotation.index()).unwrap()
    }

    pub fn use_cached_return_annotation(&mut self, annotation: ReturnAnnotation) -> Inferred<'db> {
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
        self.check_point_cache(annotation.index()).unwrap()
    }

    pub fn use_cached_return_annotation_type(
        &mut self,
        annotation: ReturnAnnotation,
    ) -> Type<'db, 'db> {
        self.use_cached_annotation_type_internal(annotation.index(), annotation.expression())
    }

    pub fn use_cached_annotation_type(&mut self, annotation: Annotation) -> Type<'db, 'db> {
        self.use_cached_annotation_type_internal(annotation.index(), annotation.expression())
    }

    fn use_cached_annotation_type_internal(
        &mut self,
        annotation_index: NodeIndex,
        expr: Expression,
    ) -> Type<'db, 'db> {
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

    pub fn use_cached_simple_generic_type(&mut self, expression: Expression) -> Type<'db, 'db> {
        debug_assert_eq!(
            self.file.points.get(expression.index()).type_(),
            PointType::Redirect
        );
        let inferred = self.check_point_cache(expression.index()).unwrap();
        Type::Class(inferred.maybe_class(self.i_s).unwrap())
    }

    pub fn use_db_type_of_annotation(&self, node_index: NodeIndex) -> &'db DbType {
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

    fn compute_type_assignment(&mut self, assignment: Assignment<'x>) -> TypeNameLookup<'db, 'x> {
        // Use the node star_targets or single_target, because they are not used otherwise.
        let file = self.file;
        let cached_type_node_ref = NodeRef::new(file, assignment.index() + 1);
        if cached_type_node_ref.point().calculated() {
            return load_cached_type(cached_type_node_ref);
        }
        self.cache_assignment_nodes(assignment);
        if let Some(name) = assignment.maybe_simple_type_reassignment() {
            // For very simple cases like `Foo = int`. Not sure yet if this going to stay.
            let node_ref = NodeRef::new(file, name.index());
            debug_assert!(node_ref.point().calculated());
            return check_type_name(self.i_s, node_ref);
        }
        if let Some((name_def, expr)) = assignment.maybe_simple_type_expression_assignment() {
            debug_assert!(file.points.get(name_def.index()).calculated());
            let inferred = self.check_point_cache(name_def.index()).unwrap();
            let in_definition = NodeRef::new(file, assignment.index()).as_link();
            if let Some(tv) = inferred.maybe_type_var(self.i_s) {
                TypeNameLookup::TypeVar(tv)
            } else {
                let mut type_var_manager = TypeVarManager::default();
                let mut type_var_callback =
                    |_: &mut InferenceState, type_var: Rc<TypeVar>, _, _| {
                        // Here we avoid all late bound type var calculation for callable, which is how
                        // mypy works. The default behavior without a type_var_callback would be to
                        // just calculate all late bound type vars, but that would mean that something
                        // like `Foo = Callable[[T], T]` could not be used like `Foo[int]`, which is
                        // generally how type aliases work.
                        let index = type_var_manager.add(type_var.clone(), None);
                        Some(DbType::TypeVar(TypeVarUsage {
                            type_var,
                            index,
                            in_definition,
                        }))
                    };
                let p = file.points.get(expr.index());
                let mut comp =
                    TypeComputation::new(self, in_definition, Some(&mut type_var_callback));
                comp.errors_already_calculated = p.calculated();
                let t = comp.compute_type(expr);
                let complex = match t {
                    TypeContent::ClassWithoutTypeVar(i) => return TypeNameLookup::Class(i),
                    TypeContent::InvalidVariable(t) => {
                        return TypeNameLookup::InvalidVariable(InvalidVariableType::Variable(
                            NodeRef::new(file, name_def.index()),
                        ))
                    }
                    _ => {
                        let node_ref = NodeRef::new(file, expr.index());
                        let db_type = comp.as_db_type(t, node_ref);
                        debug_assert!(!comp.type_var_manager.has_type_vars());
                        ComplexPoint::TypeAlias(Box::new(TypeAlias {
                            type_vars: type_var_manager.into_type_vars(),
                            location: in_definition,
                            db_type: Rc::new(db_type),
                        }))
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
    ) -> (Inferred<'db>, Type<'db, 'db>) {
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
                        unsaved.save_redirect(f, index);
                    } else {
                        let mut x = type_computation_for_variable_annotation;
                        let mut comp = TypeComputation::new(
                            &mut inference,
                            assignment_node_ref.as_link(),
                            Some(&mut x),
                        );
                        comp.cache_annotation_internal(index, expr);
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
                    unsaved.save_redirect(f, index);
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
                if let Some(tuple) = expr.maybe_tuple() {
                    self.calc_type_comment_tuple(assignment_node_ref, tuple.iter())
                } else {
                    let expr_node_ref = NodeRef::new(self.file, expr.index());
                    let mut x = type_computation_for_variable_annotation;
                    let mut comp =
                        TypeComputation::new(self, assignment_node_ref.as_link(), Some(&mut x));
                    let t = comp.compute_type(expr);
                    let mut db_type = comp.as_db_type(t, expr_node_ref);
                    let type_vars = comp.into_type_vars(|inf, recalculate_type_vars| {
                        db_type = recalculate_type_vars(&db_type);
                    });
                    debug_assert!(type_vars.is_empty());
                    db_type
                }
            })
            .collect();
        DbType::Tuple(TupleContent {
            generics: Some(GenericsList::new_generics(generics)),
            arbitrary_length: false,
        })
    }

    pub fn compute_cast_target(&mut self, node_ref: NodeRef<'db>) -> Inferred<'db> {
        let named_expr = node_ref.as_named_expression();
        let mut x = type_computation_for_variable_annotation;
        let mut comp = TypeComputation::new(self, node_ref.as_link(), Some(&mut x));
        comp.origin = TypeComputationOrigin::CastTarget;

        let t = comp.compute_type(named_expr.expression());
        let mut db_type = comp.as_db_type(t, node_ref);
        let type_vars = comp.into_type_vars(|inf, recalculate_type_vars| {
            db_type = recalculate_type_vars(&db_type);
        });
        debug_assert!(type_vars.is_empty());
        Inferred::execute_db_type(self.i_s, db_type)
    }

    pub fn compute_type_var_constraint(&mut self, expr: Expression) -> Option<DbType> {
        let mut on_type_var = |_: &mut InferenceState, type_var, _, current_callable| todo!();
        let node_ref = NodeRef::new(self.file, expr.index());
        let mut comp = TypeComputation::new(self, node_ref.as_link(), Some(&mut on_type_var));
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
            ComplexPoint::TypeVar(t) => TypeNameLookup::TypeVar(t.clone()),
            _ => unreachable!(),
        }
    } else {
        let point = node_ref.point();
        if point.type_() == PointType::MultiDefinition {
            debug!("TODO check if this is the right place for this kind of stuff.");
            TypeNameLookup::InvalidVariable(InvalidVariableType::Variable(node_ref))
        } else {
            let specific = point.maybe_specific().unwrap();
            if specific == Specific::TypingType {
                TypeNameLookup::SpecialType(SpecialType::Type)
            } else {
                debug_assert_eq!(specific, Specific::TypingCallable);
                TypeNameLookup::SpecialType(SpecialType::Callable)
            }
        }
    }
}

fn check_type_name<'db>(
    i_s: &mut InferenceState<'db, '_>,
    name_node_ref: NodeRef<'db>,
) -> TypeNameLookup<'db, 'db> {
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
            return TypeNameLookup::Class(Inferred::new_saved(
                name_node_ref.file,
                c.index(),
                name_node_ref.file.points.get(c.index()),
            ));
        }
        TypeLike::Assignment(assignment) => {
            if name_node_ref.point().calculated() {
                return load_cached_type(name_node_ref);
            }
            name_node_ref
                .file
                .inference(i_s)
                .compute_type_assignment(assignment)
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
