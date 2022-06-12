use std::rc::Rc;

use parsa_python_ast::*;

use crate::database::{
    CallableContent, ComplexPoint, DbType, GenericsList, Locality, Point, PointType, Specific,
    TupleContent, TypeAlias, TypeVar, TypeVarIndex, TypeVarManager, TypeVarType, TypeVarUsage,
};
use crate::debug;
use crate::diagnostics::IssueType;
use crate::file::{PythonFile, PythonInference};
use crate::file_state::File;
use crate::generics::{Generics, Type};
use crate::getitem::{SliceOrSimple, SliceType, SliceTypeContent, SliceTypeIterator};
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::node_ref::NodeRef;
use crate::value::{Class, ClassLike, Function, Module, Value};

const ANNOTATION_TO_EXPR_DIFFERENCE: u32 = 2;

#[derive(Debug)]
enum SpecialType<'db> {
    Union,
    Optional,
    Any,
    Protocol,
    ProtocolWithGenerics(SliceType<'db>),
    Generic,
    GenericWithGenerics(SliceType<'db>),
    Callable,
    Type,
    Tuple,
}

#[derive(Debug)]
enum TypeContent<'db> {
    Module(&'db PythonFile),
    ClassWithoutTypeVar(Inferred<'db>),
    TypeAlias(&'db TypeAlias),
    DbType(DbType),
    SpecialType(SpecialType<'db>),
    InvalidVariable,
}

enum TypeNameLookup<'db> {
    Module(&'db PythonFile),
    Class(Inferred<'db>),
    TypeVar(Rc<TypeVar>),
    TypeAlias(&'db TypeAlias),
    SpecialType(SpecialType<'db>),
    InvalidFunction(Function<'db, 'db>),
    InvalidVariable,
    Unknown,
}

pub enum BaseClass<'db> {
    DbType(DbType),
    Protocol(Option<SliceType<'db>>),
    Generic(SliceType<'db>),
}

macro_rules! compute_type_application {
    ($self:ident, $method:ident $args:tt) => {{
        let mut type_vars = TypeVarManager::default();
        let mut on_type_var = |_: &mut InferenceState, type_var: Rc<TypeVar>, _| {
            let index = type_vars.add(type_var.clone());
            TypeVarUsage {
                type_var,
                index,
                type_: TypeVarType::Alias,
            }
        };
        let mut tcomp = TypeComputation::new($self, &mut on_type_var);
        match tcomp.$method $args {
            TypeContent::ClassWithoutTypeVar(inf) => inf,
            TypeContent::DbType(db_type) => Inferred::new_unsaved_complex(if tcomp.has_type_vars {
                ComplexPoint::TypeAlias(Box::new(TypeAlias {
                    type_vars: type_vars.into_boxed_slice(),
                    db_type: Rc::new(db_type),
                }))
            } else {
                ComplexPoint::TypeInstance(Box::new(DbType::Type(Box::new(db_type))))
            }),
            _ => todo!(),
        }
    }}
}

impl<'db> TypeContent<'db> {
    fn union(self, i_s: &mut InferenceState<'db, '_>, other: Self) -> Self {
        Self::DbType(match self {
            Self::ClassWithoutTypeVar(inf) => todo!(),
            Self::DbType(t) => t.union(match other {
                Self::ClassWithoutTypeVar(i) => i.as_db_type(i_s),
                Self::DbType(t) => t,
                Self::Module(m) => todo!(),
                Self::TypeAlias(m) => todo!(),
                Self::SpecialType(m) => todo!(),
                Self::InvalidVariable => return Self::InvalidVariable,
            }),
            Self::Module(m) => todo!(),
            Self::TypeAlias(m) => todo!(),
            Self::SpecialType(s) => match s {
                // `Any | something` always is Any
                SpecialType::Any => DbType::Any,
                _ => todo!("{s:?}"),
            },
            Self::InvalidVariable => return Self::InvalidVariable,
        })
    }
}

pub(super) fn type_computation_for_variable_annotation(
    i_s: &mut InferenceState,
    type_var: Rc<TypeVar>,
) -> Option<TypeVarUsage> {
    if let Some(class) = i_s.current_class {
        if let Some(usage) = class
            .type_vars(i_s)
            .find(type_var.clone(), TypeVarType::Class)
        {
            return Some(usage);
        }
    }
    if let Some((func, _)) = i_s.current_execution {
        if let Some(type_vars) = func.type_vars(i_s) {
            let usage = type_vars.find(type_var, TypeVarType::Function);
            if usage.is_some() {
                return usage;
            }
        }
    }
    None
}

pub struct TypeComputation<'db, 'a, 'b, 'c, C> {
    inference: &'c mut PythonInference<'db, 'a, 'b>,
    type_var_callback: &'c mut C,
    errors_already_calculated: bool,
    pub has_type_vars: bool,
    is_base_class_calculation: bool,
}

impl<'db, 'a, 'b, 'c, C> TypeComputation<'db, 'a, 'b, 'c, C>
where
    C: FnMut(&mut InferenceState<'db, 'a>, Rc<TypeVar>, Option<TypeVarIndex>) -> TypeVarUsage,
{
    pub fn new(
        inference: &'c mut PythonInference<'db, 'a, 'b>,
        type_var_callback: &'c mut C,
    ) -> Self {
        Self {
            inference,
            type_var_callback,
            errors_already_calculated: false,
            has_type_vars: false,
            is_base_class_calculation: false,
        }
    }

    pub fn new_base_class_calculation(
        inference: &'c mut PythonInference<'db, 'a, 'b>,
        type_var_callback: &'c mut C,
    ) -> Self {
        Self {
            inference,
            type_var_callback,
            errors_already_calculated: false,
            has_type_vars: false,
            is_base_class_calculation: true,
        }
    }

    fn compute_forward_reference(&mut self, start: CodeIndex, string: String) -> TypeContent<'db> {
        self.cache_code_string(start, string, |comp, expr| comp.compute_type(expr, None))
    }

    fn cache_type_comment(
        &mut self,
        start: CodeIndex,
        string: String,
    ) -> (Inferred<'db>, Type<'db, 'db>) {
        self.cache_code_string(start, string, |comp, expr| {
            // It is kind of a hack to use the ANNOTATION_TO_EXPR_DIFFERENCE here. However this
            // allows us to reuse the code for annotations completely and the nodes before the expr
            // should really never be used by anything productive.
            let index = expr.index() - ANNOTATION_TO_EXPR_DIFFERENCE;
            comp.cache_annotation_internal(index, expr);
            (
                Inferred::new_saved2(comp.inference.file, index),
                comp.inference
                    .use_cached_annotation_type_internal(index, expr),
            )
        })
    }

    // TODO this should not be a string, but probably cow
    fn cache_code_string<T>(
        &mut self,
        start: CodeIndex,
        string: String,
        mut callback: impl FnMut(&mut TypeComputation<'db, 'a, '_, '_, C>, Expression<'db>) -> T,
    ) -> T {
        let f: &'db PythonFile =
            self.inference
                .file
                .new_annotation_file(self.inference.i_s.db, start, string);
        if let Some(expr) = f.tree.maybe_expression() {
            let mut comp = TypeComputation {
                inference: &mut f.inference(self.inference.i_s),
                type_var_callback: self.type_var_callback,
                errors_already_calculated: self.errors_already_calculated,
                has_type_vars: false,
                is_base_class_calculation: self.is_base_class_calculation,
            };
            let type_ = callback(&mut comp, expr);
            self.has_type_vars |= comp.has_type_vars;
            type_
        } else {
            debug!("Found non-expression in annotation: {}", f.tree.code());
            todo!()
        }
    }

    pub fn compute_base_class(&mut self, expr: Expression<'db>) -> BaseClass<'db> {
        let calculated = self.compute_type(expr, None);
        match calculated {
            TypeContent::SpecialType(SpecialType::GenericWithGenerics(s)) => BaseClass::Generic(s),
            TypeContent::SpecialType(SpecialType::Protocol) => BaseClass::Protocol(None),
            TypeContent::SpecialType(SpecialType::ProtocolWithGenerics(s)) => {
                BaseClass::Protocol(Some(s))
            }
            _ => BaseClass::DbType(
                self.as_db_type(calculated, NodeRef::new(self.inference.file, expr.index())),
            ),
        }
    }

    pub fn compute_annotation(&mut self, annotation: Annotation<'db>) {
        self.cache_annotation_internal(annotation.index(), annotation.expression());
    }

    pub fn compute_return_annotation(&mut self, annotation: ReturnAnnotation<'db>) {
        self.cache_annotation_internal(annotation.index(), annotation.expression());
    }

    fn add_module_issue(&self, file: &'db PythonFile, node_ref: NodeRef<'db>) {
        node_ref.add_typing_issue(
            self.inference.i_s.db,
            IssueType::InvalidType(format!(
                "Module {:?} is not valid as a type",
                Module::new(self.inference.i_s.db, file).qualified_name(self.inference.i_s.db),
            )),
        );
    }

    fn add_function_issue(&self, node_ref: NodeRef<'db>, func: Function<'db, 'db>) {
        //let node_ref = NodeRef::new(self.inference.file, name.index());
        node_ref.add_typing_issue(
            self.inference.i_s.db,
            IssueType::InvalidType(format!(
                "Function {:?} is not valid as a type",
                func.qualified_name(self.inference.i_s.db),
            )),
        );
        node_ref.add_typing_issue(
            self.inference.i_s.db,
            IssueType::Note(
                "Perhaps you need \"Callable[...]\" or a callback protocol?".to_owned(),
            ),
        );
    }

    fn cache_annotation_internal(&mut self, annotation_index: NodeIndex, expr: Expression<'db>) {
        let point = self.inference.file.points.get(annotation_index);
        if point.calculated() {
            return;
        }
        debug!(
            "Infer annotation expression class on {:?}: {:?}",
            self.inference.file.byte_to_line_column(expr.start()),
            expr.as_code()
        );

        let type_ = self.compute_type(expr, None);

        let specific = match type_ {
            TypeContent::ClassWithoutTypeVar(i) => {
                debug_assert!(self.inference.file.points.get(expr.index()).calculated());
                Specific::AnnotationClassInstance
            }
            TypeContent::DbType(d) => {
                if self.has_type_vars {
                    Inferred::new_unsaved_complex(ComplexPoint::TypeInstance(Box::new(d)))
                        .save_redirect(self.inference.file, expr.index());
                    Specific::AnnotationWithTypeVars
                } else {
                    Inferred::new_unsaved_complex(ComplexPoint::TypeInstance(Box::new(d)))
                        .save_redirect(self.inference.file, annotation_index);
                    return;
                }
            }
            TypeContent::Module(m) => {
                self.add_module_issue(m, NodeRef::new(self.inference.file, expr.index()));
                Inferred::new_unsaved_complex(ComplexPoint::TypeInstance(Box::new(DbType::Any)))
                    .save_redirect(self.inference.file, annotation_index);
                return;
            }
            TypeContent::TypeAlias(a) => {
                Inferred::new_unsaved_complex(ComplexPoint::TypeInstance(Box::new(a.as_db_type())))
                    .save_redirect(self.inference.file, annotation_index);
                return;
            }
            TypeContent::SpecialType(special) => {
                let db_type = match special {
                    SpecialType::Any => DbType::Any,
                    SpecialType::Type => DbType::Type(Box::new(DbType::Class(
                        self.inference.i_s.db.python_state.object().as_link(),
                    ))),
                    SpecialType::Tuple => DbType::Tuple(TupleContent {
                        generics: None,
                        arbitrary_length: true,
                    }),
                    _ => todo!("{special:?}"),
                };
                Inferred::new_unsaved_complex(ComplexPoint::TypeInstance(Box::new(db_type)))
                    .save_redirect(self.inference.file, annotation_index);
                return;
            }
            TypeContent::InvalidVariable => {
                let node_ref = NodeRef::new(self.inference.file, expr.index());
                node_ref.add_typing_issue(
                    self.inference.i_s.db,
                    IssueType::InvalidType(format!(
                        "Variable {:?} is not valid as a type",
                        "__main__.x".to_owned() //TODO: Use the variable name
                    )),
                );
                node_ref.add_typing_issue(
                    self.inference.i_s.db,
                    IssueType::Note(
                        "See https://mypy.readthedocs.io/en/stable/common_issues.html#variables-vs-type-aliases".to_owned(),
                    ),
                );
                Inferred::new_unsaved_complex(ComplexPoint::TypeInstance(Box::new(DbType::Any)))
                    .save_redirect(self.inference.file, annotation_index);
                return;
            }
        };
        self.inference.file.points.set(
            annotation_index,
            Point::new_simple_specific(specific, Locality::Todo),
        );
    }

    fn as_db_type(&mut self, type_: TypeContent<'db>, node_ref: NodeRef<'db>) -> DbType {
        match type_ {
            TypeContent::ClassWithoutTypeVar(i) => i.as_db_type(self.inference.i_s),
            TypeContent::DbType(d) => d,
            TypeContent::Module(m) => {
                self.add_module_issue(m, node_ref);
                DbType::Any
            }
            TypeContent::TypeAlias(a) => a.as_db_type(),
            TypeContent::SpecialType(m) => match m {
                SpecialType::Callable => DbType::Callable(CallableContent {
                    params: None,
                    return_class: Box::new(DbType::Any),
                }),
                _ => todo!("{m:?}"),
            },
            TypeContent::InvalidVariable => {
                todo!()
            }
        }
    }

    fn compute_slice_type(
        &mut self,
        slice: SliceOrSimple<'db>,
        generic_or_protocol_index: Option<TypeVarIndex>,
    ) -> TypeContent<'db> {
        match slice {
            SliceOrSimple::Simple(s) => {
                self.compute_type(s.named_expr.expression(), generic_or_protocol_index)
            }
            SliceOrSimple::Slice(n) => todo!(),
        }
    }

    fn compute_type(
        &mut self,
        expr: Expression<'db>,
        generic_or_protocol_index: Option<TypeVarIndex>,
    ) -> TypeContent<'db> {
        let type_content = match expr.unpack() {
            ExpressionContent::ExpressionPart(n) => {
                self.compute_type_expression_part(n, generic_or_protocol_index)
            }
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

    fn compute_slice_db_type(&mut self, slice: SliceOrSimple<'db>) -> DbType {
        let t = self.compute_slice_type(slice, None);
        self.as_db_type(t, slice.as_node_ref())
    }

    fn compute_db_type(&mut self, expr: Expression<'db>) -> DbType {
        let t = self.compute_type(expr, None);
        self.as_db_type(t, NodeRef::new(self.inference.file, expr.index()))
    }

    fn compute_type_expression_part(
        &mut self,
        node: ExpressionPart<'db>,
        generic_or_protocol_index: Option<TypeVarIndex>,
    ) -> TypeContent<'db> {
        match node {
            ExpressionPart::Atom(atom) => self.compute_type_atom(atom, generic_or_protocol_index),
            ExpressionPart::Primary(primary) => {
                self.compute_type_primary(primary, generic_or_protocol_index)
            }
            ExpressionPart::BitwiseOr(bitwise_or) => {
                let (a, b) = bitwise_or.unpack();
                // TODO this should only merge in annotation contexts
                let other = self.compute_type_expression_part(b, None);
                self.compute_type_expression_part(a, None)
                    .union(self.inference.i_s, other)
            }
            _ => todo!("Not handled yet {node:?}"),
        }
    }

    fn compute_type_primary(
        &mut self,
        primary: Primary<'db>,
        generic_or_protocol_index: Option<TypeVarIndex>,
    ) -> TypeContent<'db> {
        let base = self.compute_type_primary_or_atom(primary.first(), generic_or_protocol_index);
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
                            self.compute_type_name(name, None)
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
                            TypeContent::DbType(DbType::Any)
                        }
                    }
                    TypeContent::ClassWithoutTypeVar(i) => {
                        let cls = i.maybe_class(self.inference.i_s).unwrap();
                        let node_ref = NodeRef::new(self.inference.file, primary.index());
                        if let Some(index) = cls
                            .class_storage
                            .class_symbol_table
                            .lookup_symbol(name.as_str())
                        {
                            self.inference.file.points.set(
                                name.index(),
                                Point::new_redirect(
                                    cls.reference.file.file_index(),
                                    index,
                                    Locality::Todo,
                                ),
                            );
                            self.compute_type_name(name, None)
                        } else {
                            todo!()
                        }
                    }
                    TypeContent::DbType(t) => match t {
                        DbType::Class(c) => todo!(),
                        DbType::GenericClass(c, g) => todo!(),
                        //DbType::Any => ComputedType::new(TypeContent::DbType(DbType::Any)),
                        _ => todo!("{primary:?} {t:?}"),
                    },
                    TypeContent::TypeAlias(m) => todo!(),
                    TypeContent::SpecialType(m) => todo!(),
                    TypeContent::InvalidVariable => todo!(),
                }
            }
            PrimaryContent::Execution(details) => {
                todo!("{primary:?}")
            }
            PrimaryContent::GetItem(slice_type) => {
                let s = SliceType::new(self.inference.file, primary.index(), slice_type);
                match base {
                    TypeContent::ClassWithoutTypeVar(i) => {
                        let cls = i.maybe_class(self.inference.i_s).unwrap();
                        let t = self.compute_type_get_item_on_class(cls, s);
                        if let TypeContent::ClassWithoutTypeVar(i) = t {
                            TypeContent::ClassWithoutTypeVar(
                                i.save_if_unsaved(self.inference.file, primary.index()),
                            )
                        } else {
                            t
                        }
                    }
                    TypeContent::DbType(d) => todo!(),
                    TypeContent::Module(m) => todo!("{primary:?}"),
                    TypeContent::TypeAlias(m) => self.compute_type_get_item_on_alias(m, s),
                    TypeContent::SpecialType(special) => match special {
                        SpecialType::Union => self.compute_type_get_item_on_union(s),
                        SpecialType::Optional => self.compute_type_get_item_on_optional(s),
                        SpecialType::Type => match s.unpack() {
                            SliceTypeContent::Simple(simple) => TypeContent::DbType(DbType::Type(
                                Box::new(self.compute_db_type(simple.named_expr.expression())),
                            )),
                            _ => todo!(),
                        },
                        SpecialType::Tuple => self.compute_type_get_item_on_tuple(s),
                        SpecialType::Any => todo!(),
                        SpecialType::Protocol => {
                            self.expect_type_var_args(s);
                            TypeContent::SpecialType(SpecialType::ProtocolWithGenerics(s))
                        }
                        SpecialType::ProtocolWithGenerics(_) => todo!(),
                        SpecialType::Generic => {
                            self.expect_type_var_args(s);
                            TypeContent::SpecialType(SpecialType::GenericWithGenerics(s))
                        }
                        SpecialType::GenericWithGenerics(_) => todo!(),
                        SpecialType::Callable => self.compute_type_get_item_on_callable(s),
                    },
                    TypeContent::InvalidVariable => todo!(),
                }
            }
        }
    }

    fn compute_type_get_item_on_class(
        &mut self,
        class: Class<'db, '_>,
        slice_type: SliceType<'db>,
    ) -> TypeContent<'db> {
        if matches!(class.generics(), Generics::None) {
            let expected_count = class.type_vars(self.inference.i_s).len();
            let mut given_count = 1;
            let result = match slice_type.unpack() {
                SliceTypeContent::Simple(s) => {
                    match self.compute_type(s.named_expr.expression(), None) {
                        TypeContent::ClassWithoutTypeVar(_) => TypeContent::ClassWithoutTypeVar(
                            Inferred::new_unsaved_specific(Specific::SimpleGeneric),
                        ),
                        TypeContent::DbType(d) => TypeContent::DbType(DbType::GenericClass(
                            class.reference.as_link(),
                            GenericsList::new_generics(Box::new([d])),
                        )),
                        TypeContent::Module(m) => todo!(),
                        TypeContent::TypeAlias(m) => todo!(),
                        TypeContent::SpecialType(m) => todo!(),
                        TypeContent::InvalidVariable => todo!(),
                    }
                }
                SliceTypeContent::Slice(slice) => todo!(),
                SliceTypeContent::Slices(slices) => {
                    given_count = 0;
                    let mut generics = vec![];
                    for slice_content in slices.iter() {
                        if generics.is_empty() {
                            let t = self.compute_slice_type(slice_content, None);
                            if !matches!(t, TypeContent::ClassWithoutTypeVar(_)) {
                                for slice_content in slices.iter().take(given_count) {
                                    generics.push(self.compute_slice_db_type(slice_content));
                                }
                                generics.push(self.as_db_type(t, slice_content.as_node_ref()));
                            }
                        } else {
                            generics.push(self.compute_slice_db_type(slice_content))
                        }
                        given_count += 1;
                    }
                    if generics.is_empty() {
                        TypeContent::ClassWithoutTypeVar(Inferred::new_unsaved_specific(
                            Specific::SimpleGeneric,
                        ))
                    } else {
                        TypeContent::DbType(DbType::GenericClass(
                            class.reference.as_link(),
                            GenericsList::generics_from_vec(generics),
                        ))
                    }
                }
            };
            if given_count != expected_count {
                // TODO both the type argument issues and are not implemented for other classlikes
                // like tuple/callable/type, which can also have late bound type vars and too
                // many/few given type vars!
                NodeRef::new(self.inference.file, slice_type.primary_index).add_typing_issue(
                    self.inference.i_s.db,
                    IssueType::TypeArgumentIssue(
                        class.name().to_owned(),
                        expected_count,
                        given_count,
                    ),
                );
            }
            result
        } else {
            todo!("{:?}", class)
        }
    }

    fn compute_type_get_item_on_tuple(&mut self, slice_type: SliceType<'db>) -> TypeContent<'db> {
        let content = match slice_type.unpack() {
            SliceTypeContent::Simple(simple) => {
                // TODO if it is a (), it's an empty tuple
                let t = self.compute_db_type(simple.named_expr.expression());
                TupleContent {
                    generics: Some(GenericsList::new_generics(Box::new([t]))),
                    arbitrary_length: false,
                }
            }
            SliceTypeContent::Slice(x) => {
                todo!()
            }
            SliceTypeContent::Slices(slices) => {
                let mut arbitrary_length = false;
                TupleContent {
                    generics: Some(GenericsList::new_generics(
                        slices
                            .iter()
                            .filter_map(|slice_content| {
                                if let SliceOrSimple::Simple(s) = slice_content {
                                    if s.named_expr.is_ellipsis_literal() {
                                        arbitrary_length = true;
                                        return None;
                                    }
                                }
                                Some(self.compute_slice_db_type(slice_content))
                            })
                            .collect(),
                    )),
                    arbitrary_length,
                }
            }
        };
        TypeContent::DbType(DbType::Tuple(content))
    }

    fn compute_type_get_item_on_callable(
        &mut self,
        slice_type: SliceType<'db>,
    ) -> TypeContent<'db> {
        let mut params = Some(vec![]);
        let mut add_param = |params: &mut Option<Vec<DbType>>, element: StarLikeExpression<'db>| {
            if let StarLikeExpression::NamedExpression(n) = element {
                let t = self.compute_type(n.expression(), None);
                params
                    .as_mut()
                    .unwrap()
                    .push(self.as_db_type(t, NodeRef::new(self.inference.file, n.index())))
            } else {
                todo!()
            }
        };

        let content = match slice_type.unpack() {
            SliceTypeContent::Simple(simple) => {
                todo!()
            }
            SliceTypeContent::Slice(x) => {
                todo!()
            }
            SliceTypeContent::Slices(slices) => {
                let mut iterator = slices.iter();
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
                                _ => todo!(),
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
                    params: params.map(GenericsList::generics_from_vec),
                    return_class: Box::new(return_class),
                }
            }
        };
        TypeContent::DbType(DbType::Callable(content))
    }

    fn compute_type_get_item_on_union(&mut self, slice_type: SliceType<'db>) -> TypeContent<'db> {
        let iterator = slice_type.iter();
        if let SliceTypeIterator::SliceOrSimple(s) = iterator {
            self.compute_slice_type(s, None)
        } else {
            TypeContent::DbType(DbType::Union(GenericsList::new_union(
                iterator
                    .map(|slice_or_simple| {
                        let t = self.compute_slice_type(slice_or_simple, None);
                        self.as_db_type(t, slice_or_simple.as_node_ref())
                    })
                    .collect(),
            )))
        }
    }

    fn compute_type_get_item_on_optional(
        &mut self,
        slice_type: SliceType<'db>,
    ) -> TypeContent<'db> {
        match slice_type.unpack() {
            SliceTypeContent::Simple(simple) => TypeContent::DbType(
                self.compute_db_type(simple.named_expr.expression())
                    .union(DbType::None),
            ),
            _ => todo!(),
        }
    }

    fn compute_type_get_item_on_alias(
        &mut self,
        alias: &TypeAlias,
        slice_type: SliceType<'db>,
    ) -> TypeContent<'db> {
        let expected_count = alias.type_vars.len();
        let mut given_count = 1;
        let mut generics = vec![];
        match slice_type.unpack() {
            SliceTypeContent::Simple(s) => {
                generics.push(self.compute_db_type(s.named_expr.expression()))
            }
            SliceTypeContent::Slice(slice) => todo!(),
            SliceTypeContent::Slices(slices) => {
                given_count = 0;
                for slice_or_simple in slices.iter() {
                    given_count += 1;
                    generics.push(self.compute_slice_db_type(slice_or_simple))
                }
            }
        };
        let mismatch = given_count != expected_count;
        if mismatch {
            slice_type.as_node_ref().add_typing_issue(
                self.inference.i_s.db,
                IssueType::TypeAliasArgumentIssue(expected_count, given_count),
            );
        }
        TypeContent::DbType(alias.db_type.remap_type_vars(&mut |usage| {
            if mismatch {
                DbType::Any
            } else {
                generics[usage.index.as_usize()].clone()
            }
        }))
    }

    fn expect_type_var_args(&mut self, slice_type: SliceType<'db>) {
        match slice_type.unpack() {
            SliceTypeContent::Simple(n) => {
                match self.compute_type(n.named_expr.expression(), Some(TypeVarIndex::new(0))) {
                    TypeContent::DbType(DbType::TypeVar(_)) => (),
                    _ => todo!(),
                }
            }
            SliceTypeContent::Slice(slice) => todo!(),
            SliceTypeContent::Slices(slices) => {
                for (i, s) in slices.iter().enumerate() {
                    match self.compute_slice_type(s, Some(TypeVarIndex::new(i))) {
                        TypeContent::DbType(DbType::TypeVar(_)) => (),
                        _ => todo!(),
                    }
                }
            }
        }
    }

    fn compute_type_primary_or_atom(
        &mut self,
        p: PrimaryOrAtom<'db>,
        generic_or_protocol_index: Option<TypeVarIndex>,
    ) -> TypeContent<'db> {
        match p {
            PrimaryOrAtom::Primary(primary) => {
                self.compute_type_primary(primary, generic_or_protocol_index)
            }
            PrimaryOrAtom::Atom(atom) => self.compute_type_atom(atom, generic_or_protocol_index),
        }
    }

    fn compute_type_atom(
        &mut self,
        atom: Atom<'db>,
        generic_or_protocol_index: Option<TypeVarIndex>,
    ) -> TypeContent<'db> {
        match atom.unpack() {
            AtomContent::Name(n) => {
                self.inference.infer_name_reference(n);
                self.compute_type_name(n, generic_or_protocol_index)
            }
            AtomContent::StringsOrBytes(s_o_b) => match s_o_b.as_python_string() {
                Some(PythonString::Ref(start, s)) => {
                    self.compute_forward_reference(start, s.to_owned())
                }
                Some(PythonString::String(start, s)) => todo!(),
                Some(PythonString::FString) => todo!(),
                None => todo!(),
            },
            AtomContent::NoneLiteral => TypeContent::DbType(DbType::None),
            _ => TypeContent::InvalidVariable,
        }
    }

    fn compute_type_name(
        &mut self,
        name: Name<'db>,
        generic_or_protocol_index: Option<TypeVarIndex>,
    ) -> TypeContent<'db> {
        match self.inference.lookup_type_name(name) {
            TypeNameLookup::Module(f) => TypeContent::Module(f),
            TypeNameLookup::Class(i) => TypeContent::ClassWithoutTypeVar(i),
            TypeNameLookup::TypeVar(t) => {
                let usage =
                    (self.type_var_callback)(self.inference.i_s, t, generic_or_protocol_index);
                self.has_type_vars = true;
                TypeContent::DbType(DbType::TypeVar(usage))
            }
            TypeNameLookup::TypeAlias(alias) => {
                if self.is_base_class_calculation {
                    if !matches!(
                        alias.db_type.as_ref(),
                        DbType::Class(_) | DbType::GenericClass(_, _) | DbType::Tuple(_)
                    ) {
                        NodeRef::new(self.inference.file, name.index())
                            .add_typing_issue(self.inference.i_s.db, IssueType::InvalidBaseClass);
                    }
                }
                TypeContent::TypeAlias(alias)
            }
            TypeNameLookup::InvalidFunction(func) => {
                self.add_function_issue(NodeRef::new(self.inference.file, name.index()), func);
                TypeContent::DbType(DbType::Any)
            }
            TypeNameLookup::InvalidVariable => TypeContent::InvalidVariable,
            TypeNameLookup::Unknown => TypeContent::DbType(DbType::Any),
            TypeNameLookup::SpecialType(special) => {
                if self.is_base_class_calculation
                    && !matches!(
                        special,
                        SpecialType::Protocol | SpecialType::Generic | SpecialType::Tuple
                    )
                {
                    debug!("TODO Invalid base class???")
                }
                TypeContent::SpecialType(special)
            }
        }
    }
}

impl<'db, 'a, 'b> PythonInference<'db, 'a, 'b> {
    pub fn compute_type_application_on_class(
        &mut self,
        class: Class<'db, '_>,
        slice_type: SliceType<'db>,
    ) -> Inferred<'db> {
        compute_type_application!(self, compute_type_get_item_on_class(class, slice_type))
    }

    pub fn compute_type_application_on_alias(
        &mut self,
        alias: &TypeAlias,
        slice_type: SliceType<'db>,
    ) -> Inferred<'db> {
        if !matches!(
            alias.db_type.as_ref(),
            DbType::Class(_) | DbType::GenericClass(_, _)
        ) {
            slice_type
                .as_node_ref()
                .add_typing_issue(self.i_s.db, IssueType::OnlyClassTypeApplication);
            return Inferred::new_any();
        }
        compute_type_application!(self, compute_type_get_item_on_alias(alias, slice_type))
    }

    pub fn compute_type_application_on_typing_class(
        &mut self,
        specific: Specific,
        slice_type: SliceType<'db>,
    ) -> Inferred<'db> {
        match specific {
            Specific::TypingGeneric | Specific::TypingProtocol => {
                //Inferred::new_unsaved_specific(Specific::TypingWithGenerics)
                todo!()
            }
            Specific::TypingTuple => {
                compute_type_application!(self, compute_type_get_item_on_tuple(slice_type))
            }
            Specific::TypingCallable => {
                compute_type_application!(self, compute_type_get_item_on_callable(slice_type))
            }
            Specific::TypingUnion => {
                compute_type_application!(self, compute_type_get_item_on_union(slice_type))
            }
            Specific::TypingOptional => {
                compute_type_application!(self, compute_type_get_item_on_optional(slice_type))
            }
            Specific::TypingType => match slice_type.unpack() {
                SliceTypeContent::Simple(simple) => {
                    todo!()
                    // let g = simple.infer_type(i_s);
                    // DbType::Type(Box::new(g))
                }
                _ => todo!(),
            },
            _ => unreachable!("{:?}", specific),
        }
    }

    /* TODO remove
    pub fn maybe_compute_param_annotation(&mut self, name: Name<'db>) -> Option<Inferred<'db>> {
        name.maybe_param_annotation()
            .map(|annotation| match name.simple_param_type() {
                SimpleParamType::Normal => self.compute_annotation(annotation),
                SimpleParamType::MultiArgs => {
                    let p = self.annotation_type(annotation).into_db_type(self.i_s);
                    Inferred::new_unsaved_complex(ComplexPoint::TypeInstance(Box::new(
                        DbType::Tuple(TupleContent {
                            generics: Some(GenericsList::new(Box::new([p]))),
                            arbitrary_length: true,
                        }),
                    )))
                }
                SimpleParamType::MultiKwargs => {
                    let p = self.annotation_type(annotation).into_db_type(self.i_s);
                    Inferred::create_instance(
                        self.i_s.db.python_state.builtins_point_link("dict"),
                        Some(&[
                            DbType::Class(
                                self.i_s.db.python_state.builtins_point_link("str"),
                            ),
                            p,
                        ]),
                    )
                }
            })
    }
    */

    pub(super) fn use_cached_annotation(&mut self, annotation: Annotation<'db>) -> Inferred<'db> {
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

    pub fn use_cached_return_annotation(
        &mut self,
        annotation: ReturnAnnotation<'db>,
    ) -> Inferred<'db> {
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
        annotation: ReturnAnnotation<'db>,
    ) -> Type<'db, 'db> {
        self.use_cached_annotation_type_internal(annotation.index(), annotation.expression())
    }

    pub fn use_cached_annotation_type(&mut self, annotation: Annotation<'db>) -> Type<'db, 'db> {
        self.use_cached_annotation_type_internal(annotation.index(), annotation.expression())
    }

    fn use_cached_annotation_type_internal(
        &mut self,
        annotation_index: NodeIndex,
        expr: Expression<'db>,
    ) -> Type<'db, 'db> {
        let point = self.file.points.get(annotation_index);
        assert!(point.calculated());
        let complex_index = if point.type_() == PointType::Specific {
            if point.specific() == Specific::AnnotationClassInstance {
                return Type::ClassLike(ClassLike::Class(
                    self.infer_expression(expr).maybe_class(self.i_s).unwrap(),
                ));
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
            Type::from_db_type(self.i_s.db, db_type)
        } else {
            unreachable!()
        }
    }

    pub fn use_annotation_expression_or_generic_type(
        &mut self,
        expression: Expression<'db>,
    ) -> Type<'db, 'db> {
        let point = self.file.points.get(expression.index());
        if !point.calculated() {
            todo!("{expression:?}")
        }

        match point.type_() {
            PointType::Redirect => {
                let inferred = self.check_point_cache(expression.index()).unwrap();
                Type::ClassLike(ClassLike::Class(inferred.maybe_class(self.i_s).unwrap()))
            }
            PointType::Complex => {
                if let ComplexPoint::TypeInstance(t) =
                    self.file.complex_points.get(point.complex_index())
                {
                    Type::from_db_type(self.i_s.db, t)
                } else {
                    todo!()
                }
            }
            _ => todo!("{point:?}"),
        }
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

    fn cache_type_assignment(&mut self, assignment: Assignment<'db>) -> TypeNameLookup<'db> {
        self.cache_assignment_nodes(assignment);
        if let Some(name) = assignment.maybe_simple_type_reassignment() {
            // For very simple cases like `Foo = int`. Not sure yet if this going to stay.
            let node_ref = NodeRef::new(self.file, name.index());
            debug_assert!(node_ref.point().calculated());
            return check_type_name(self.i_s, node_ref);
        }
        match assignment.unpack() {
            AssignmentContent::Normal(mut targets, AssignmentRightSide::StarExpressions(right)) => {
                if let StarExpressionContent::Expression(expr) = right.unpack() {
                    let first_target = targets.next().unwrap();
                    if targets.next().is_some() {
                        todo!()
                        // return TypeNameLookup::Invalid;
                    }
                    let name_def = if let Target::Name(name_def) = first_target {
                        name_def
                    } else {
                        unreachable!()
                    };
                    debug_assert!(self.file.points.get(name_def.index()).calculated());
                    let inferred = self.check_point_cache(name_def.index()).unwrap();
                    let complex = if let Some(tv) = inferred.maybe_type_var(self.i_s) {
                        ComplexPoint::TypeVar(Rc::new(tv))
                    } else {
                        let mut type_vars = TypeVarManager::default();
                        let p = self.file.points.get(expr.index());
                        let mut comp = TypeComputation {
                            inference: self,
                            errors_already_calculated: p.calculated(),
                            type_var_callback:
                                &mut |_: &mut InferenceState, type_var: Rc<TypeVar>, _| {
                                    let index = type_vars.add(type_var.clone());
                                    TypeVarUsage {
                                        type_var,
                                        index,
                                        type_: TypeVarType::Alias,
                                    }
                                },
                            has_type_vars: false,
                            is_base_class_calculation: false,
                        };
                        let t = comp.compute_type(expr, None);
                        if let TypeContent::ClassWithoutTypeVar(i) = t {
                            return TypeNameLookup::Class(i);
                        } else if matches!(t, TypeContent::InvalidVariable) {
                            return TypeNameLookup::InvalidVariable;
                        } else {
                            let node_ref = NodeRef::new(comp.inference.file, expr.index());
                            let db_type = Rc::new(comp.as_db_type(t, node_ref));
                            ComplexPoint::TypeAlias(Box::new(TypeAlias {
                                type_vars: type_vars.into_boxed_slice(),
                                db_type,
                            }))
                        }
                    };
                    let node_ref = NodeRef::new(self.file, name_def.name().index());
                    node_ref.insert_complex(complex, Locality::Todo);
                    load_cached_type(node_ref)
                } else {
                    todo!()
                }
            }
            AssignmentContent::WithAnnotation(target, annotation, right_side) => {
                todo!("{target:?}")
            }
            _ => todo!(),
        }
    }

    fn lookup_type_name(&mut self, name: Name<'db>) -> TypeNameLookup<'db> {
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
    ) -> (Inferred<'db>, Type<'db, 'db>) {
        let mut on_type_var = |i_s: &mut InferenceState, type_var, _| {
            type_computation_for_variable_annotation(i_s, type_var).unwrap_or_else(|| todo!())
        };
        let mut comp = TypeComputation::new(self, &mut on_type_var);
        comp.cache_type_comment(start, s.trim_end_matches('\\').to_owned())
    }

    pub fn compute_type_var_bound(&mut self, expr: Expression<'db>) -> Option<DbType> {
        let mut on_type_var = |_: &mut InferenceState, type_var, _| todo!();
        let mut comp = TypeComputation::new(self, &mut on_type_var);
        let db_type = comp.compute_db_type(expr);
        (!comp.has_type_vars).then(|| db_type)
    }
}

#[inline]
fn check_special_type(point: Point) -> Option<SpecialType<'static>> {
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
        let specific = node_ref.point().maybe_specific().unwrap();
        if specific == Specific::TypingType {
            TypeNameLookup::SpecialType(SpecialType::Type)
        } else {
            debug_assert_eq!(specific, Specific::TypingCallable);
            TypeNameLookup::SpecialType(SpecialType::Callable)
        }
    }
}

fn check_type_name<'db>(
    i_s: &mut InferenceState<'db, '_>,
    name_node_ref: NodeRef<'db>,
) -> TypeNameLookup<'db> {
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
            // Name must be a NameDefinition
            let name_index = new_name.index();
            let node_ref = NodeRef::new(name_node_ref.file, name_index);
            if node_ref.point().calculated() {
                load_cached_type(node_ref)
            } else {
                name_node_ref
                    .file
                    .inference(i_s)
                    .cache_type_assignment(assignment)
            }
        }
        TypeLike::Function(f) => TypeNameLookup::InvalidFunction(Function::new(
            NodeRef::new(name_node_ref.file, f.index()),
            None,
        )),
        TypeLike::Import => {
            if point.calculated() {
                // When an import appears, this means that there's no redirect and the import leads
                // nowhere.
                debug_assert_eq!(point.type_(), PointType::Unknown);
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
