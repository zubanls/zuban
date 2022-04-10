use std::rc::Rc;

use parsa_python_ast::*;

use crate::database::{
    ComplexPoint, DbType, GenericsList, Locality, Point, PointType, Specific, TupleContent,
    TypeAlias, TypeVar, TypeVarUsage,
};
use crate::debug;
use crate::diagnostics::IssueType;
use crate::file::{PythonFile, PythonInference};
use crate::file_state::File;
use crate::generics::{Generics, Type};
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::node_ref::NodeRef;
use crate::value::{Class, ClassLike};

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

enum AnnotationType {
    SimpleClass,
    DbTypeWithTypeVars,
    DbTypeWithoutTypeVars,
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
                TypeContent::SpecialType(m) => todo!(),
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

    pub fn compute_type_as_db_type(&mut self, expr: Expression<'db>) -> DbType {
        self.compute_type(expr).into_db_type(self.inference.i_s)
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
                            todo!()
                        }
                    }
                    TypeContent::ClassWithoutTypeVar(_) => todo!(),
                    TypeContent::DbType(t) => todo!(),
                    TypeContent::TypeAlias(m) => todo!(),
                    TypeContent::SpecialType(m) => todo!(),
                }
            }
            PrimaryContent::Execution(details) => {
                todo!()
            }
            PrimaryContent::GetItem(slice_type) => match base.type_ {
                TypeContent::ClassWithoutTypeVar(i) => {
                    let cls = i.maybe_class(self.inference.i_s).unwrap();
                    self.compute_type_get_item_on_class(cls, primary.index(), slice_type)
                }
                TypeContent::DbType(d) => todo!(),
                TypeContent::Module(m) => todo!(),
                TypeContent::TypeAlias(m) => todo!(),
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
                    SpecialType::Generic => todo!(),
                    SpecialType::GenericWithGenerics => todo!(),
                },
            },
        }
    }

    fn compute_type_get_item_on_class(
        &mut self,
        class: Class,
        primary_index: NodeIndex,
        slice_type: SliceType<'db>,
    ) -> ComputedType<'db> {
        if matches!(class.generics, Generics::None) {
            match slice_type {
                SliceType::NamedExpression(named_expr) => {
                    let ComputedType {
                        type_,
                        has_type_vars,
                    } = self.compute_type(named_expr.expression());
                    match type_ {
                        TypeContent::ClassWithoutTypeVar(_) => {
                            debug_assert!(!self
                                .inference
                                .file
                                .points
                                .get(primary_index)
                                .calculated());
                            ComputedType::new(TypeContent::ClassWithoutTypeVar(
                                Inferred::new_and_save(
                                    self.inference.file,
                                    primary_index,
                                    Point::new_simple_specific(
                                        Specific::SimpleGeneric,
                                        Locality::Todo,
                                    ),
                                ),
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
                    slices.iter();
                    todo!()
                }
            }
        } else {
            todo!()
        }
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
                slices.iter();
                todo!()
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

    pub(super) fn use_cached_param_annotation(
        &mut self,
        annotation: Annotation<'db>,
    ) -> Inferred<'db> {
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

    pub fn use_return_annotation(&mut self, annotation: ReturnAnnotation<'db>) -> Inferred<'db> {
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

    pub fn use_return_annotation_type(
        &mut self,
        annotation: ReturnAnnotation<'db>,
    ) -> Type<'db, 'db> {
        self.use_annotation_type_internal(annotation.index(), annotation.expression())
    }

    pub fn use_annotation_type(&mut self, annotation: Annotation<'db>) -> Type<'db, 'db> {
        self.use_annotation_type_internal(annotation.index(), annotation.expression())
    }

    fn use_annotation_type_internal(
        &mut self,
        annotation_index: NodeIndex,
        expr: Expression<'db>,
    ) -> Type<'db, 'db> {
        let point = self.file.points.get(annotation_index);
        assert!(point.calculated());
        if point.type_() == PointType::Specific {
            if point.specific() == Specific::AnnotationClassInstance {
                return Type::ClassLike(ClassLike::Class(
                    self.infer_expression(expr).maybe_class(self.i_s).unwrap(),
                ));
            } else {
                debug_assert_eq!(point.specific(), Specific::AnnotationWithTypeVars);
            }
        } else {
            debug_assert_eq!(point.type_(), PointType::Complex, "{:?}", expr);
            debug_assert!(matches!(
                self.file.complex_points.get(point.complex_index()),
                ComplexPoint::TypeInstance(_)
            ));
        }
        if let ComplexPoint::TypeInstance(db_type) = self
            .file
            .complex_points
            .get_by_node_index(&self.file.points, expr.index())
        {
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
                    let inferred = self.check_point_cache(expr.index()).unwrap();
                    let complex = if let Some(tv) = inferred.maybe_type_var(self.i_s) {
                        ComplexPoint::TypeVar(Rc::new(tv))
                    } else {
                        let type_vars = vec![];
                        let t = TypeComputation::new(self, &mut |x| todo!()).compute_type(expr);
                        ComplexPoint::TypeAlias(Box::new(TypeAlias {
                            type_vars: type_vars.into_boxed_slice(),
                            db_type: Rc::new(t.into_db_type(self.i_s)),
                        }))
                    };
                    if let Target::Name(n) = first_target {
                        let name_def_index = n.name_definition().unwrap().index();
                        let node_ref = NodeRef::new(self.file, name_def_index);
                        node_ref.insert_complex(complex, Locality::Todo);
                        Self::load_cached_type(node_ref)
                    } else {
                        unreachable!()
                    }
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

    fn load_cached_type(node_ref: NodeRef<'db>) -> TypeNameLookup<'db> {
        match node_ref.complex().unwrap() {
            ComplexPoint::TypeAlias(t) => TypeNameLookup::TypeAlias(t),
            ComplexPoint::TypeVar(t) => TypeNameLookup::TypeVar(t.clone()),
            _ => unreachable!(),
        }
    }

    fn lookup_type_name(&mut self, name: Name<'db>) -> TypeNameLookup<'db> {
        let point = self.file.points.get(name.index());
        if point.calculated() {
            match point.type_() {
                PointType::Specific => todo!(),
                PointType::Redirect => {
                    let file = match point.file_index() == self.file.file_index() {
                        true => self.file,
                        false => self.i_s.database.loaded_python_file(point.file_index()),
                    };
                    let new_name_ref = NodeRef::new(file, point.node_index());

                    if let Some(special) = check_special_type(new_name_ref.point()) {
                        return TypeNameLookup::SpecialType(special);
                    }

                    let new_name = new_name_ref.as_name();
                    match new_name.expect_type() {
                        TypeLike::ClassDef(c) => {
                            return TypeNameLookup::Class(Inferred::new_saved(
                                file,
                                c.index(),
                                file.points.get(c.index()),
                            ))
                        }
                        TypeLike::Assignment(assignment) => {
                            // Name must be a NameDefinition
                            let name_def_index = new_name.name_definition().unwrap().index();
                            let node_ref = NodeRef::new(self.file, name_def_index);
                            if node_ref.point().calculated() {
                                Self::load_cached_type(node_ref)
                            } else {
                                self.cache_type_assignment(assignment)
                            }
                        }
                        TypeLike::Function => {
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
                            TypeNameLookup::Invalid
                        }
                        TypeLike::Import => {
                            if point.type_() == PointType::Redirect {
                                let mut inference = file.inference(self.i_s);
                                // Cache
                                inference.infer_name(new_name);
                                inference.lookup_type_name(new_name)
                            } else {
                                todo!()
                            }
                        }
                        TypeLike::Other => {
                            todo!()
                        }
                    }
                }
                PointType::FileReference => {
                    let file = self.i_s.database.loaded_python_file(point.file_index());
                    TypeNameLookup::Module(file)
                }
                _ => todo!(),
            }
        } else {
            // Make sure the name is cached.
            self.infer_name_reference(name);
            debug_assert!(self.file.points.get(name.index()).calculated());
            self.lookup_type_name(name)
        }
    }

    pub fn compute_annotation(&mut self, annotation: Annotation<'db>) -> Inferred<'db> {
        self.compute_annotation_internal(annotation.index(), annotation.expression())
    }

    pub fn compute_return_annotation(&mut self, annotation: ReturnAnnotation<'db>) {
        self.compute_annotation_internal(annotation.index(), annotation.expression());
    }

    pub fn compute_annotation_internal(
        &mut self,
        annotation_index: NodeIndex,
        expr: Expression<'db>,
    ) -> Inferred<'db> {
        let t = self.cache_annotation_internal(annotation_index, expr);

        if matches!(t, AnnotationType::DbTypeWithTypeVars) {
            // TODO this is always a TypeInstance, just use that.
            let inferred = self.check_point_cache(expr.index()).unwrap();
            let type_ = inferred.class_as_type(self.i_s);
            todo!();
            type_.execute_and_resolve_type_vars(self.i_s, self.i_s.current_class, None)
        } else {
            self.check_point_cache(annotation_index).unwrap()
        }
    }

    pub(super) fn compute_type_comment(&mut self, start: CodeIndex, string: String) -> DbType {
        TypeComputation::new(self, &mut |_| todo!())
            .compute_annotation_string(start, string)
            .into_db_type(self.i_s)
    }

    #[inline]
    fn cache_annotation_internal(
        &mut self,
        annotation_index: NodeIndex,
        expr: Expression<'db>,
    ) -> AnnotationType {
        let point = self.file.points.get(annotation_index);
        if point.calculated() {
            return if point.type_() == PointType::Specific {
                if point.specific() == Specific::AnnotationClassInstance {
                    AnnotationType::SimpleClass
                } else {
                    debug_assert_eq!(point.specific(), Specific::AnnotationWithTypeVars);
                    AnnotationType::DbTypeWithTypeVars
                }
            } else {
                debug_assert_eq!(point.type_(), PointType::Complex);
                AnnotationType::DbTypeWithoutTypeVars
            };
        }
        debug!(
            "Infer annotation expression class on {:?}: {:?}",
            self.file.byte_to_line_column(expr.start()),
            expr.as_code()
        );

        let ComputedType {
            type_,
            has_type_vars,
        } = TypeComputation::new(self, &mut |_| todo!()).compute_type(expr);

        let (specific, ret) = match type_ {
            TypeContent::ClassWithoutTypeVar(i) => {
                i.save_redirect(self.file, expr.index());
                (
                    Specific::AnnotationClassInstance,
                    AnnotationType::SimpleClass,
                )
            }
            TypeContent::DbType(d) => {
                if has_type_vars {
                    Inferred::new_unsaved_complex(ComplexPoint::TypeInstance(Box::new(
                        DbType::Type(Box::new(d)),
                    )))
                    .save_redirect(self.file, expr.index());
                    (
                        Specific::AnnotationWithTypeVars,
                        AnnotationType::DbTypeWithTypeVars,
                    )
                } else {
                    Inferred::new_unsaved_complex(ComplexPoint::TypeInstance(Box::new(d)))
                        .save_redirect(self.file, annotation_index);
                    return AnnotationType::DbTypeWithoutTypeVars;
                }
            }
            TypeContent::Module(m) => todo!(),
            TypeContent::TypeAlias(m) => todo!(),
            TypeContent::SpecialType(_) => todo!(),
        };
        self.file.points.set(
            annotation_index,
            Point::new_simple_specific(specific, Locality::Todo),
        );
        ret
    }

    pub fn compute_type_var_bound(&mut self, expr: Expression<'db>) -> Option<DbType> {
        let mut had_type_vars = false;
        let db_type = TypeComputation::new(self, &mut |_| {
            had_type_vars = true;
            todo!()
        })
        .compute_type_as_db_type(expr);
        (!had_type_vars).then(|| db_type)
    }
}

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
