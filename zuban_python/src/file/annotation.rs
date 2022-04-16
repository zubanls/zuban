use std::rc::Rc;

use parsa_python_ast::*;

use crate::database::{
    ComplexPoint, DbType, FileIndex, GenericsList, Locality, Point, PointType, Specific,
    TupleContent, TypeAlias, TypeVar, TypeVarManager, TypeVarType, TypeVarUsage,
};
use crate::debug;
use crate::diagnostics::IssueType;
use crate::file::{PythonFile, PythonInference};
use crate::file_state::File;
use crate::generics::{Generics, Type};
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::node_ref::NodeRef;
use crate::value::{Class, ClassLike, Value};

#[derive(Debug)]
enum SpecialType {
    Union,
    Optional,
    Any,
    Protocol,
    ProtocolWithGenerics,
    Generic,
    GenericWithGenerics,
}

#[derive(Debug)]
enum TypeContent<'db> {
    Module(&'db PythonFile),
    ClassWithoutTypeVar(Inferred<'db>),
    TypeAlias(&'db TypeAlias),
    DbType(DbType),
    SpecialType(SpecialType),
}

enum TypeNameLookup<'db> {
    Module(&'db PythonFile),
    Class(Inferred<'db>),
    TypeVar(Rc<TypeVar>),
    TypeAlias(&'db TypeAlias),
    SpecialType(SpecialType),
    Invalid,
}

pub enum BaseClass {
    DbType(DbType),
    Protocol,
    Generic,
}

#[derive(Debug)]
struct ComputedType<'db> {
    type_: TypeContent<'db>,
    has_type_vars: bool,
}

impl<'db> ComputedType<'db> {
    fn new(type_: TypeContent<'db>) -> Self {
        Self {
            type_,
            has_type_vars: false,
        }
    }

    fn union(self, i_s: &mut InferenceState<'db, '_>, other: Self) -> Self {
        Self {
            type_: TypeContent::DbType(match self.type_ {
                TypeContent::ClassWithoutTypeVar(inf) => todo!(),
                TypeContent::DbType(t) => t.union(match other.type_ {
                    TypeContent::ClassWithoutTypeVar(i) => i.as_db_type(i_s),
                    TypeContent::DbType(t) => t,
                    TypeContent::Module(m) => todo!(),
                    TypeContent::TypeAlias(m) => todo!(),
                    TypeContent::SpecialType(m) => todo!(),
                }),
                TypeContent::Module(m) => todo!(),
                TypeContent::TypeAlias(m) => todo!(),
                TypeContent::SpecialType(s) => match s {
                    // `Any | something` always is Any
                    SpecialType::Any => DbType::Any,
                    _ => todo!("{:?}", s),
                },
            }),
            has_type_vars: self.has_type_vars | other.has_type_vars,
        }
    }

    fn into_db_type(self, i_s: &mut InferenceState<'db, '_>) -> DbType {
        match self.type_ {
            TypeContent::ClassWithoutTypeVar(i) => i.as_db_type(i_s),
            TypeContent::DbType(d) => d,
            TypeContent::Module(m) => todo!(),
            TypeContent::TypeAlias(m) => todo!(),
            TypeContent::SpecialType(m) => todo!(),
        }
    }
}

pub struct TypeComputation<'db, 'a, 'b, 'c, C> {
    inference: &'c mut PythonInference<'db, 'a, 'b>,
    type_var_callback: &'c mut C,
}

impl<'db, 'a, 'b, 'c, C: FnMut(Rc<TypeVar>) -> TypeVarUsage> TypeComputation<'db, 'a, 'b, 'c, C> {
    pub fn new(
        inference: &'c mut PythonInference<'db, 'a, 'b>,
        type_var_callback: &'c mut C,
    ) -> Self {
        Self {
            inference,
            type_var_callback,
        }
    }

    // TODO this should not be a string, but probably cow
    fn compute_annotation_string(&mut self, start: CodeIndex, string: String) -> ComputedType<'db> {
        let f: &'db PythonFile =
            self.inference
                .file
                .new_annotation_file(self.inference.i_s.database, start, string);
        if let Some(expr) = f.tree.maybe_expression() {
            TypeComputation::new(&mut f.inference(self.inference.i_s), self.type_var_callback)
                .compute_type(expr)
        } else {
            debug!("Found non-expression in annotation: {}", f.tree.code());
            todo!()
        }
    }

    pub fn compute_base_class(&mut self, expr: Expression<'db>) -> BaseClass {
        let calculated = self.compute_type(expr);
        match calculated.type_ {
            TypeContent::SpecialType(SpecialType::Protocol | SpecialType::ProtocolWithGenerics) => {
                BaseClass::Protocol
            }
            TypeContent::SpecialType(SpecialType::Generic | SpecialType::GenericWithGenerics) => {
                BaseClass::Protocol
            }
            _ => BaseClass::DbType(calculated.into_db_type(self.inference.i_s)),
        }
    }

    pub fn compute_annotation(&mut self, annotation: Annotation<'db>) {
        self.cache_annotation_internal(annotation.index(), annotation.expression());
    }

    pub fn compute_return_annotation(&mut self, annotation: ReturnAnnotation<'db>) {
        self.cache_annotation_internal(annotation.index(), annotation.expression());
    }

    #[inline]
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

        let ComputedType {
            type_,
            has_type_vars,
        } = self.compute_type(expr);

        let specific = match type_ {
            TypeContent::ClassWithoutTypeVar(i) => {
                i.save_redirect(self.inference.file, expr.index());
                Specific::AnnotationClassInstance
            }
            TypeContent::DbType(d) => {
                if has_type_vars {
                    Inferred::new_unsaved_complex(ComplexPoint::TypeInstance(Box::new(
                        DbType::Type(Box::new(d)),
                    )))
                    .save_redirect(self.inference.file, expr.index());
                    Specific::AnnotationWithTypeVars
                } else {
                    Inferred::new_unsaved_complex(ComplexPoint::TypeInstance(Box::new(d)))
                        .save_redirect(self.inference.file, annotation_index);
                    return;
                }
            }
            TypeContent::Module(m) => todo!(),
            TypeContent::TypeAlias(m) => {
                if m.type_vars.is_empty() {
                    Inferred::new_unsaved_complex(ComplexPoint::TypeInstance(Box::new(
                        m.db_type.as_ref().clone(),
                    )))
                    .save_redirect(self.inference.file, annotation_index);
                    return;
                } else {
                    todo!()
                }
            }
            TypeContent::SpecialType(s) => match s {
                SpecialType::Any => {
                    Inferred::new_unsaved_complex(ComplexPoint::TypeInstance(Box::new(
                        DbType::Any,
                    )))
                    .save_redirect(self.inference.file, annotation_index);
                    return;
                }
                _ => todo!("{:?}", s),
            },
        };
        self.inference.file.points.set(
            annotation_index,
            Point::new_simple_specific(specific, Locality::Todo),
        );
    }

    fn compute_type(&mut self, expr: Expression<'db>) -> ComputedType<'db> {
        match expr.unpack() {
            ExpressionContent::ExpressionPart(n) => self.compute_type_expression_part(n),
            ExpressionContent::Lambda(_) => todo!(),
            ExpressionContent::Ternary(t) => todo!(),
        }
    }

    fn compute_type_expression_part(&mut self, node: ExpressionPart<'db>) -> ComputedType<'db> {
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
            _ => todo!("Not handled yet {:?}", node),
        }
        /*
        let node_ref = NodeRef::new(self.file, expr.index());
        if let Some(func) = inferred.maybe_simple(inference.i_s, |v| v.as_function().cloned()) {
            node_ref.add_typing_issue(
                i_s.database,
                IssueType::ValidType(format!(
                    "Function {:?} is not valid as a type",
                    func.qualified_name(i_s.database),
                )),
            );
            node_ref.add_typing_issue(
                i_s.database,
                IssueType::Note(
                    "Perhaps you need \"Callable[...]\" or a callback protocol?".to_owned(),
                ),
            )
        } else if let Some(module) =
            inferred.maybe_simple(inference.i_s, |v| v.as_module().cloned())
        {
            node_ref.add_typing_issue(
                i_s.database,
                IssueType::ValidType(format!(
                    "Module {:?} is not valid as a type",
                    module.qualified_name(i_s.database),
                )),
            );
        } else {
            debug!("Unknown annotation expression {}", expr.short_debug());
        }
        Point::new_unknown(self.file.file_index(), Locality::Todo)
        */
    }

    fn compute_type_primary(&mut self, primary: Primary<'db>) -> ComputedType<'db> {
        let base = self.compute_type_primary_or_atom(primary.first());
        match primary.second() {
            PrimaryContent::Attribute(name) => {
                match base.type_ {
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
                            node_ref.add_typing_issue(
                                self.inference.i_s.database,
                                IssueType::TypeNotFound,
                            );
                            self.inference.file.points.set(
                                name.index(),
                                Point::new_unknown(f.file_index(), Locality::Todo),
                            );
                            ComputedType::new(TypeContent::DbType(DbType::Unknown))
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
                            self.compute_type_name(name)
                        } else {
                            todo!()
                        }
                    }
                    TypeContent::DbType(t) => todo!(),
                    TypeContent::TypeAlias(m) => todo!(),
                    TypeContent::SpecialType(m) => todo!(),
                }
            }
            PrimaryContent::Execution(details) => {
                todo!("{:?}", primary)
            }
            PrimaryContent::GetItem(slice_type) => match base.type_ {
                TypeContent::ClassWithoutTypeVar(i) => {
                    let cls = i.maybe_class(self.inference.i_s).unwrap();
                    self.compute_type_get_item_on_class(cls, primary.index(), slice_type)
                }
                TypeContent::DbType(d) => todo!(),
                TypeContent::Module(m) => todo!(),
                TypeContent::TypeAlias(m) => {
                    self.compute_type_get_item_on_alias(m, primary.index(), slice_type)
                }
                TypeContent::SpecialType(special) => match special {
                    SpecialType::Union => todo!(),
                    SpecialType::Optional => todo!(),
                    SpecialType::Any => todo!(),
                    SpecialType::Protocol => {
                        self.expect_type_var_args(slice_type);
                        ComputedType::new(TypeContent::SpecialType(
                            SpecialType::ProtocolWithGenerics,
                        ))
                    }
                    SpecialType::ProtocolWithGenerics => todo!(),
                    SpecialType::Generic => {
                        self.expect_type_var_args(slice_type);
                        ComputedType::new(TypeContent::SpecialType(
                            SpecialType::GenericWithGenerics,
                        ))
                    }
                    SpecialType::GenericWithGenerics => todo!(),
                },
            },
        }
    }

    fn compute_type_get_item_on_class(
        &mut self,
        class: Class<'db, '_>,
        primary_index: NodeIndex,
        slice_type: SliceType<'db>,
    ) -> ComputedType<'db> {
        if matches!(class.generics, Generics::None) {
            let expected_count = class.type_vars(self.inference.i_s).len();
            let mut given_count = 1;
            let result = match slice_type {
                SliceType::NamedExpression(named_expr) => {
                    let ComputedType {
                        type_,
                        has_type_vars,
                    } = self.compute_type(named_expr.expression());
                    match type_ {
                        TypeContent::ClassWithoutTypeVar(inf) => {
                            let point =
                                Point::new_simple_specific(Specific::SimpleGeneric, Locality::Todo);
                            self.inference.file.points.set(primary_index, point);
                            ComputedType::new(TypeContent::ClassWithoutTypeVar(
                                Inferred::new_and_save(self.inference.file, primary_index, point),
                            ))
                        }
                        TypeContent::DbType(d) => ComputedType {
                            type_: TypeContent::DbType(DbType::GenericClass(
                                class.reference.as_link(),
                                GenericsList::new(Box::new([d])),
                            )),
                            has_type_vars,
                        },
                        TypeContent::Module(m) => todo!(),
                        TypeContent::TypeAlias(m) => todo!(),
                        TypeContent::SpecialType(m) => todo!(),
                    }
                }
                SliceType::Slice(slice) => todo!(),
                SliceType::Slices(slices) => {
                    given_count = 0;
                    let mut generics = vec![];
                    let mut has_any_type_vars = false;
                    for slice_content in slices.iter() {
                        if generics.is_empty() {
                            match slice_content {
                                SliceContent::NamedExpression(n) => {
                                    let ComputedType {
                                        type_,
                                        has_type_vars,
                                    } = self.compute_type(n.expression());
                                    has_any_type_vars |= has_type_vars;
                                    match type_ {
                                        TypeContent::DbType(d) => {
                                            if given_count > 0 {
                                                todo!("restart")
                                            } else {
                                                generics.push(d);
                                            }
                                        }
                                        TypeContent::ClassWithoutTypeVar(inf) => (),
                                        _ => todo!(),
                                    }
                                }
                                SliceContent::Slice(n) => todo!(),
                            }
                        } else {
                            match slice_content {
                                SliceContent::NamedExpression(n) => {
                                    let t = self.compute_type(n.expression());
                                    has_any_type_vars |= t.has_type_vars;
                                    generics.push(t.into_db_type(self.inference.i_s))
                                }
                                SliceContent::Slice(n) => todo!(),
                            }
                        }
                        given_count += 1;
                    }
                    if generics.is_empty() {
                        todo!()
                    } else {
                        ComputedType {
                            type_: TypeContent::DbType(DbType::GenericClass(
                                class.reference.as_link(),
                                GenericsList::from_vec(generics),
                            )),
                            has_type_vars: has_any_type_vars,
                        }
                    }
                }
            };
            if given_count != expected_count {
                // TODO both the type argument issues and are not implemented for other classlikes
                // like tuple/callable/type, which can also have late bound type vars and too
                // many/few given type vars!
                NodeRef::new(self.inference.file, primary_index).add_typing_issue(
                    self.inference.i_s.database,
                    IssueType::TypeArgumentIssue(
                        class.name().to_owned(),
                        expected_count,
                        given_count,
                    ),
                );
            }
            result
        } else {
            todo!()
        }
    }

    fn compute_type_get_item_on_alias(
        &mut self,
        alias: &'db TypeAlias,
        primary_index: NodeIndex,
        slice_type: SliceType<'db>,
    ) -> ComputedType<'db> {
        let expected_count = alias.type_vars.len();
        let mut given_count = 1;
        let result = match slice_type {
            SliceType::NamedExpression(named_expr) => {
                let ComputedType {
                    type_,
                    has_type_vars,
                } = self.compute_type(named_expr.expression());
                match type_ {
                    TypeContent::ClassWithoutTypeVar(inf) => {
                        todo!()
                    }
                    TypeContent::DbType(d) => ComputedType {
                        type_: TypeContent::DbType(alias.db_type.remap_type_vars(&mut |usage| {
                            todo!()
                            /*
                            if usage.index > 0 {
                                todo!()
                            } else {
                                d
                            }
                            */
                        })),
                        has_type_vars,
                    },
                    TypeContent::Module(m) => todo!(),
                    TypeContent::TypeAlias(m) => todo!(),
                    TypeContent::SpecialType(m) => todo!(),
                }
            }
            SliceType::Slice(slice) => todo!(),
            SliceType::Slices(slices) => {
                given_count = 0;
                for slice_content in slices.iter() {
                    given_count += 1;
                }
                todo!()
            }
        };
        if given_count != expected_count {
            todo!()
            /*
            // Should be "Bad number of arguments for type alias, expected: 1, given: 2"
            NodeRef::new(self.inference.file, primary_index).add_typing_issue(
                self.inference.i_s.database,
                IssueType::TypeArgumentIssue(
                    class.name().to_owned(),
                    expected_count,
                    given_count,
                ),
            );
            */
        }
        result
    }

    fn expect_type_var_args(&mut self, slice_type: SliceType<'db>) {
        match slice_type {
            SliceType::NamedExpression(named_expr) => {
                match self.compute_type(named_expr.expression()).type_ {
                    TypeContent::DbType(DbType::TypeVar(_)) => (),
                    _ => todo!(),
                }
            }
            SliceType::Slice(slice) => todo!(),
            SliceType::Slices(slices) => {
                for slice_content in slices.iter() {
                    match slice_content {
                        SliceContent::NamedExpression(n) => {
                            match self.compute_type(n.expression()).type_ {
                                TypeContent::DbType(DbType::TypeVar(_)) => (),
                                _ => todo!(),
                            }
                        }
                        SliceContent::Slice(n) => todo!(),
                    }
                }
            }
        }
    }

    fn compute_type_primary_or_atom(&mut self, p: PrimaryOrAtom<'db>) -> ComputedType<'db> {
        match p {
            PrimaryOrAtom::Primary(primary) => self.compute_type_primary(primary),
            PrimaryOrAtom::Atom(atom) => self.compute_type_atom(atom),
        }
    }

    fn compute_type_atom(&mut self, atom: Atom<'db>) -> ComputedType<'db> {
        match atom.unpack() {
            AtomContent::Name(n) => self.compute_type_name(n),
            AtomContent::StringsOrBytes(s_o_b) => match s_o_b.as_python_string() {
                Some(PythonString::Ref(start, s)) => {
                    self.compute_annotation_string(start, s.to_owned())
                }
                Some(PythonString::String(start, s)) => todo!(),
                Some(PythonString::FString) => todo!(),
                None => todo!(),
            },
            AtomContent::NoneLiteral => ComputedType::new(TypeContent::DbType(DbType::None)),
            _ => todo!(),
        }
    }

    fn compute_type_name(&mut self, name: Name<'db>) -> ComputedType<'db> {
        match self.inference.lookup_type_name(name) {
            TypeNameLookup::Module(f) => ComputedType::new(TypeContent::Module(f)),
            TypeNameLookup::Class(i) => ComputedType::new(TypeContent::ClassWithoutTypeVar(i)),
            TypeNameLookup::TypeVar(t) => {
                ComputedType::new(TypeContent::DbType(DbType::TypeVar((self
                    .type_var_callback)(
                    t
                ))))
            }
            TypeNameLookup::TypeAlias(alias) => ComputedType::new(TypeContent::TypeAlias(alias)),
            TypeNameLookup::Invalid => ComputedType::new(TypeContent::DbType(DbType::Any)),
            TypeNameLookup::SpecialType(special) => {
                ComputedType::new(TypeContent::SpecialType(special))
            }
        }
    }
}

impl<'db, 'a, 'b> PythonInference<'db, 'a, 'b> {
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
                        self.i_s.database.python_state.builtins_point_link("dict"),
                        Some(&[
                            DbType::Class(
                                self.i_s.database.python_state.builtins_point_link("str"),
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
            if point.specific() == Specific::AnnotationClassInstance {
                Inferred::new_saved(self.file, annotation.index(), point)
            } else {
                debug_assert_eq!(point.specific(), Specific::AnnotationWithTypeVars);
                Inferred::new_saved(self.file, annotation.expression().index(), point)
            }
        } else {
            debug_assert_eq!(point.type_(), PointType::Complex, "{:?}", annotation);
            debug_assert!(matches!(
                self.file.complex_points.get(point.complex_index()),
                ComplexPoint::TypeInstance(_)
            ));
            Inferred::new_saved(self.file, annotation.index(), point)
        }
    }

    pub fn use_cached_return_annotation(
        &mut self,
        annotation: ReturnAnnotation<'db>,
    ) -> Inferred<'db> {
        let point = self.file.points.get(annotation.index());
        assert!(point.calculated());
        if point.type_() == PointType::Specific {
            if point.specific() == Specific::AnnotationClassInstance {
                Inferred::new_saved(self.file, annotation.index(), point)
            } else {
                debug_assert_eq!(point.specific(), Specific::AnnotationWithTypeVars);
                todo!()
            }
        } else {
            debug_assert_eq!(point.type_(), PointType::Complex, "{:?}", annotation);
            debug_assert!(matches!(
                self.file.complex_points.get(point.complex_index()),
                ComplexPoint::TypeInstance(_)
            ));
            Inferred::new_saved(self.file, annotation.index(), point)
        }
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
            debug_assert_eq!(point.type_(), PointType::Complex, "{:?}", expr);
            debug_assert!(matches!(
                self.file.complex_points.get(point.complex_index()),
                ComplexPoint::TypeInstance(_)
            ));
            point.complex_index()
        };
        if let ComplexPoint::TypeInstance(db_type) = self.file.complex_points.get(complex_index) {
            Type::from_db_type(self.i_s.database, db_type)
        } else {
            unreachable!()
        }
    }

    fn cache_type_assignment(&mut self, assignment: Assignment<'db>) -> TypeNameLookup<'db> {
        self.cache_assignment_nodes(assignment);
        match assignment.unpack() {
            AssignmentContent::Normal(mut targets, AssignmentRightSide::StarExpressions(right)) => {
                if let StarExpressionContent::Expression(expr) = right.unpack() {
                    let first_target = targets.next().unwrap();
                    if targets.next().is_some() {
                        return TypeNameLookup::Invalid;
                    }
                    let name = if let Target::Name(n) = first_target {
                        n
                    } else {
                        unreachable!()
                    };
                    debug_assert!(self.file.points.get(name.index()).calculated());
                    let inferred = self.check_point_cache(name.index()).unwrap();
                    let complex = if let Some(tv) = inferred.maybe_type_var(self.i_s) {
                        ComplexPoint::TypeVar(Rc::new(tv))
                    } else {
                        let mut type_vars = TypeVarManager::default();
                        let t = TypeComputation::new(self, &mut |type_var| {
                            let index = type_vars.add(type_var.clone());
                            TypeVarUsage {
                                type_var,
                                index,
                                type_: TypeVarType::Alias,
                            }
                        })
                        .compute_type(expr)
                        .into_db_type(self.i_s);
                        ComplexPoint::TypeAlias(Box::new(TypeAlias {
                            type_vars: type_vars.into_boxed_slice(),
                            db_type: Rc::new(t),
                        }))
                    };
                    let name_def_index = name.name_definition().unwrap().index();
                    let node_ref = NodeRef::new(self.file, name_def_index);
                    node_ref.insert_complex(complex, Locality::Todo);
                    load_cached_type(node_ref)
                } else {
                    todo!()
                }
            }
            AssignmentContent::WithAnnotation(target, annotation, right_side) => {
                todo!("{:?}", target)
            }
            _ => todo!(),
        }
    }

    fn lookup_type_name(&mut self, name: Name<'db>) -> TypeNameLookup<'db> {
        let point = self.file.points.get(name.index());
        if point.calculated() {
            match point.type_() {
                PointType::Specific => todo!(),
                PointType::Redirect => {
                    check_type_name(
                        self.i_s,
                        point.as_redirected_node_ref(self.i_s.database),
                        || {
                            let node_ref = NodeRef::new(self.file, name.index());
                            node_ref.add_typing_issue(
                                self.i_s.database,
                                IssueType::ValidType(format!(
                                    "Function {:?} is not valid as a type",
                                    "m.A".to_owned() //TODO: func.qualified_name(self.i_s.database),
                                )),
                            );
                            node_ref.add_typing_issue(
                                self.i_s.database,
                                IssueType::Note(
                                    "Perhaps you need \"Callable[...]\" or a callback protocol?"
                                        .to_owned(),
                                ),
                            );
                        },
                    )
                }
                PointType::FileReference => {
                    let file = self.i_s.database.loaded_python_file(point.file_index());
                    TypeNameLookup::Module(file)
                }
                PointType::Unknown => TypeNameLookup::Invalid,
                _ => todo!("{:?}", point),
            }
        } else {
            // Make sure the name is cached.
            self.infer_name_reference(name);
            debug_assert!(self.file.points.get(name.index()).calculated());
            self.lookup_type_name(name)
        }
    }

    pub(super) fn compute_type_comment(&mut self, start: CodeIndex, string: String) -> DbType {
        TypeComputation::new(self, &mut |_| todo!())
            .compute_annotation_string(start, string)
            .into_db_type(self.i_s)
    }

    pub fn compute_type_var_bound(&mut self, expr: Expression<'db>) -> Option<DbType> {
        let mut had_type_vars = false;
        let db_type = TypeComputation::new(self, &mut |_| {
            had_type_vars = true;
            todo!()
        })
        .compute_type(expr)
        .into_db_type(self.i_s);
        (!had_type_vars).then(|| db_type)
    }
}

#[inline]
fn check_special_type(point: Point) -> Option<SpecialType> {
    if point.calculated() && point.type_() == PointType::Specific {
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
    match node_ref.complex().unwrap() {
        ComplexPoint::TypeAlias(t) => TypeNameLookup::TypeAlias(t),
        ComplexPoint::TypeVar(t) => TypeNameLookup::TypeVar(t.clone()),
        _ => unreachable!(),
    }
}

fn check_type_name<'db>(
    i_s: &mut InferenceState<'db, '_>,
    name_node_ref: NodeRef<'db>,
    mut on_invalid_function: impl FnMut(),
) -> TypeNameLookup<'db> {
    let point = name_node_ref.point();
    // First check redirects. These are probably one of the following cases:
    //
    // 1. imports
    // 2. Typeshed Aliases (special cases, see python_state.rs)
    // 3. Maybe simple assignments like `Foo = str`, though I'm not sure.
    //
    // It's important to check that it's a name. Otherwise it redirects to some random place.
    if point.type_() == PointType::Redirect {
        let new = point.as_redirected_node_ref(i_s.database);
        if new.maybe_name().is_some() {
            return check_type_name(i_s, new, on_invalid_function);
        }
    }

    if let Some(special) = check_special_type(point) {
        return TypeNameLookup::SpecialType(special);
    }

    let new_name = name_node_ref.as_name();
    match new_name.expect_type() {
        TypeLike::ClassDef(c) => {
            return TypeNameLookup::Class(Inferred::new_saved(
                name_node_ref.file,
                c.index(),
                name_node_ref.file.points.get(c.index()),
            ))
        }
        TypeLike::Assignment(assignment) => {
            // Name must be a NameDefinition
            let name_def_index = new_name.name_definition().unwrap().index();
            let node_ref = NodeRef::new(name_node_ref.file, name_def_index);
            if node_ref.point().calculated() {
                load_cached_type(node_ref)
            } else {
                name_node_ref
                    .file
                    .inference(i_s)
                    .cache_type_assignment(assignment)
            }
        }
        TypeLike::Function => {
            on_invalid_function();
            TypeNameLookup::Invalid
        }
        TypeLike::Import => {
            let mut inference = name_node_ref.file.inference(i_s);
            // Cache
            inference.infer_name(new_name);
            inference.lookup_type_name(new_name)
        }
        TypeLike::Other => {
            todo!()
        }
    }
}
