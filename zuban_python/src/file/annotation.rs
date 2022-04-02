use parsa_python_ast::*;

use crate::database::{
    ComplexPoint, DbType, FormatStyle, GenericsList, Locality, Point, PointType, Specific,
    TupleContent,
};
use crate::debug;
use crate::diagnostics::IssueType;
use crate::file::{PythonFile, PythonInference};
use crate::file_state::File;
use crate::generics::{Generics, Type};
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::node_ref::NodeRef;
use crate::value::{Class, ClassLike, Module, Value};

enum AnnotationType {
    SimpleClass,
    DbTypeWithTypeVars,
    DbTypeWithoutTypeVars,
}

#[derive(Debug)]
enum TypeContent<'db> {
    Module(&'db PythonFile),
    ClassWithoutTypeVar(Inferred<'db>),
    DbType(DbType),
}

#[derive(Debug)]
struct ComputedType<'db> {
    pub type_: TypeContent<'db>,
    has_type_vars: bool,
}

impl<'db> ComputedType<'db> {
    pub fn new(type_: TypeContent<'db>) -> Self {
        Self {
            type_,
            has_type_vars: false,
        }
    }

    pub fn union(self, i_s: &mut InferenceState<'db, '_>, other: Self) -> Self {
        Self {
            type_: TypeContent::DbType(match self.type_ {
                TypeContent::ClassWithoutTypeVar(inf) => todo!(),
                TypeContent::DbType(t) => t.union(match other.type_ {
                    TypeContent::ClassWithoutTypeVar(i) => i.as_db_type(i_s),
                    TypeContent::DbType(t) => t,
                    TypeContent::Module(m) => todo!(),
                }),
                TypeContent::Module(m) => todo!(),
            }),
            has_type_vars: self.has_type_vars | other.has_type_vars,
        }
    }

    fn into_db_type(self, i_s: &mut InferenceState<'db, '_>) -> DbType {
        match self.type_ {
            TypeContent::ClassWithoutTypeVar(i) => i.as_db_type(i_s),
            TypeContent::DbType(d) => d,
            TypeContent::Module(m) => todo!(),
        }
    }
}

impl<'db, 'a, 'b> PythonInference<'db, 'a, 'b> {
    pub fn maybe_compute_param_annotation(&mut self, name: Name<'db>) -> Option<Inferred<'db>> {
        name.maybe_param_annotation().map(|annotation| {
            let mut inference = self.file.inference(self.i_s);
            match name.simple_param_type() {
                SimpleParamType::Normal => inference.compute_annotation(annotation),
                SimpleParamType::MultiArgs => {
                    let p = inference.annotation_type(annotation).into_db_type(self.i_s);
                    Inferred::new_unsaved_complex(ComplexPoint::TypeInstance(Box::new(
                        DbType::Tuple(TupleContent {
                            generics: Some(GenericsList::new(Box::new([p]))),
                            arbitrary_length: true,
                        }),
                    )))
                }
                SimpleParamType::MultiKwargs => {
                    let p = inference.annotation_type(annotation).into_db_type(self.i_s);
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
            }
        })
    }

    pub fn return_annotation_type(&mut self, annotation: ReturnAnnotation<'db>) -> Type<'db, 'db> {
        self.annotation_type_internal(annotation.index(), annotation.expression())
    }

    pub fn annotation_type(&mut self, annotation: Annotation<'db>) -> Type<'db, 'db> {
        self.annotation_type_internal(annotation.index(), annotation.expression())
    }

    fn annotation_type_internal(
        &mut self,
        annotation_index: NodeIndex,
        expr: Expression<'db>,
    ) -> Type<'db, 'db> {
        match self.cache_annotation_internal(annotation_index, expr) {
            AnnotationType::SimpleClass => Type::ClassLike(ClassLike::Class(
                self.infer_expression(expr).maybe_class(self.i_s).unwrap(),
            )),
            AnnotationType::DbTypeWithTypeVars | AnnotationType::DbTypeWithoutTypeVars => {
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
        }
    }

    pub fn compute_return_annotation(
        &mut self,
        annotation: ReturnAnnotation<'db>,
    ) -> Inferred<'db> {
        self.compute_annotation_internal(annotation.index(), annotation.expression())
    }

    pub fn compute_annotation(&mut self, annotation: Annotation<'db>) -> Inferred<'db> {
        self.compute_annotation_internal(annotation.index(), annotation.expression())
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
            type_.execute_and_resolve_type_vars(self.i_s, self.i_s.current_class, None)
        } else {
            self.check_point_cache(annotation_index).unwrap()
        }
    }

    pub(super) fn compute_type_comment(&mut self, start: CodeIndex, string: String) -> DbType {
        self.compute_annotation_string(start, string)
            .into_db_type(self.i_s)
    }

    // TODO this should not be a string, but probably cow
    fn compute_annotation_string(&mut self, start: CodeIndex, string: String) -> ComputedType<'db> {
        let f = self
            .file
            .new_annotation_file(self.i_s.database, start, string);
        if let Some(expr) = f.tree.maybe_expression() {
            f.inference(self.i_s).compute_type(expr)
        } else {
            debug!("Found non-expression in annotation: {}", f.tree.code());
            todo!()
        }
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
        } = self.compute_type(expr);

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
        };
        self.file.points.set(
            annotation_index,
            Point::new_simple_specific(specific, Locality::Todo),
        );
        ret
    }

    pub fn compute_type_as_db_type(&mut self, expr: Expression<'db>) -> DbType {
        self.compute_type(expr).into_db_type(self.i_s)
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
                self.compute_type_expression_part(a).union(self.i_s, other)
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
                            self.file.points.set(
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
                }
            }
            PrimaryContent::Execution(details) => {
                todo!()
            }
            PrimaryContent::GetItem(slice_type) => match base.type_ {
                TypeContent::ClassWithoutTypeVar(i) => {
                    let cls = i.maybe_class(self.i_s).unwrap();
                    self.compute_type_get_item_on_class(cls, primary.index(), slice_type)
                }
                TypeContent::DbType(d) => todo!(),
                TypeContent::Module(m) => todo!(),
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
                    match self.compute_type(named_expr.expression()).type_ {
                        TypeContent::ClassWithoutTypeVar(_) => {
                            debug_assert!(!self.file.points.get(primary_index).calculated());
                            ComputedType::new(TypeContent::ClassWithoutTypeVar(
                                Inferred::new_and_save(
                                    self.file,
                                    primary_index,
                                    Point::new_simple_specific(
                                        Specific::SimpleGeneric,
                                        Locality::Todo,
                                    ),
                                ),
                            ))
                        }
                        TypeContent::DbType(d) => todo!(),
                        TypeContent::Module(m) => todo!(),
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
                    todo!()
                    //self.compute_annotation_string(start, s.to_owned())
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
        let point = self.file.points.get(name.index());
        if point.calculated() {
            match point.type_() {
                PointType::Specific => todo!(),
                PointType::Redirect => {
                    let file = match point.file_index() == self.file.file_index() {
                        true => self.file,
                        false => self.i_s.database.loaded_python_file(point.file_index()),
                    };
                    let new_name = Name::maybe_by_index(&file.tree, point.node_index()).unwrap();
                    match new_name.expect_type() {
                        TypeLike::ClassDef(c) => {
                            return ComputedType::new(TypeContent::ClassWithoutTypeVar(
                                Inferred::new_saved(file, c.index(), file.points.get(c.index())),
                            ))
                        }
                        TypeLike::SimpleAssignment(expr) => {
                            todo!()
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
                            ComputedType::new(TypeContent::DbType(DbType::Any))
                        }
                        TypeLike::Import => {
                            if point.type_() == PointType::Redirect {
                                let mut inference = file.inference(self.i_s);
                                // Cache
                                inference.infer_name(new_name);
                                inference.compute_type_name(new_name)
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
                    ComputedType::new(TypeContent::Module(file))
                }
                _ => todo!(),
            }
        } else {
            // Make sure the name is cached.
            self.infer_name_reference(name);
            debug_assert!(self.file.points.get(name.index()).calculated());
            self.compute_type_name(name)
        }
    }
}
