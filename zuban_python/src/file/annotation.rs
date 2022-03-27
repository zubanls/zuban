use parsa_python_ast::*;

use crate::database::{
    ComplexPoint, DbType, FormatStyle, GenericsList, Locality, Point, PointType, Specific,
    TupleContent,
};
use crate::debug;
use crate::diagnostics::IssueType;
use crate::file::PythonInference;
use crate::file_state::File;
use crate::generics::Type;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::node_ref::NodeRef;
use crate::value::{ClassLike, Value};

pub enum TypeContent<'db> {
    ClassWithoutTypeVar(Inferred<'db>),
    DbType(DbType),
}

pub struct InferredType<'db> {
    pub type_: TypeContent<'db>,
    has_type_vars: bool,
}

impl<'db> InferredType<'db> {
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
                }),
            }),
            has_type_vars: self.has_type_vars | other.has_type_vars,
        }
    }
}

impl<'db, 'a, 'b> PythonInference<'db, 'a, 'b> {
    pub fn maybe_infer_param_annotation(&mut self, name: Name<'db>) -> Option<Inferred<'db>> {
        name.maybe_param_annotation().map(|annotation| {
            let mut inference = self.file.inference(self.i_s);
            match name.simple_param_type() {
                SimpleParamType::Normal => inference.infer_annotation(annotation),
                SimpleParamType::MultiArgs => {
                    let p = inference
                        .infer_annotation_expression_class(annotation.expression())
                        .as_db_type(self.i_s);
                    Inferred::new_unsaved_complex(ComplexPoint::TypeInstance(Box::new(
                        DbType::Tuple(TupleContent {
                            generics: Some(GenericsList::new(Box::new([p]))),
                            arbitrary_length: true,
                        }),
                    )))
                }
                SimpleParamType::MultiKwargs => {
                    let p = inference
                        .infer_annotation_expression_class(annotation.expression())
                        .as_db_type(self.i_s);
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
        let specific = self.cache_annotation_internal(annotation_index, expr);
        match specific {
            Specific::AnnotationClassInstance => Type::ClassLike(ClassLike::Class(
                self.infer_expression(expr).maybe_class(self.i_s).unwrap(),
            )),
            Specific::AnnotationWithoutTypeVars | Specific::AnnotationWithTypeVars => {
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
            _ => unreachable!(),
        }
    }

    pub fn infer_annotation_expression_class(&mut self, expr: Expression<'db>) -> Inferred<'db> {
        debug!(
            "Infer annotation expression class on {:?}: {:?}",
            self.file.byte_to_line_column(expr.start()),
            expr.as_code()
        );

        let expr_part_index = expr.index() + 1;
        let mut i_s = self.i_s.with_annotation_instance();
        let mut inference = self.file.inference(&mut i_s);
        if let Some(inferred) = self.check_point_cache(expr_part_index) {
            return inferred;
        }
        // Since the expression is reserved for instantiating the expression, just do not
        // save the result.
        match expr.unpack() {
            ExpressionContent::ExpressionPart(n) => {
                let mut inferred = inference.infer_type(expr);
                let mut inferred = inferred.type_;

                /*
                if let Some(python_string) = inferred.maybe_str() {
                    if let Some(string) = python_string.to_owned() {
                        inferred = match self.infer_annotation_string(string) {
                            DbType::Class(link) => {
                                let node_reference = NodeRef::from_link(i_s.database, link);
                                Inferred::new_saved(
                                    node_reference.file,
                                    node_reference.node_index,
                                    node_reference.point(),
                                )
                            }
                            DbType::GenericClass(l, g) => todo!(),
                            DbType::Union(multiple) => todo!(),
                            DbType::Tuple(content) => todo!(),
                            DbType::Callable(content) => todo!(),
                            DbType::Type(c) => todo!(),
                            DbType::None => return Inferred::new_none(),
                            DbType::Any => todo!(),
                            DbType::TypeVar(index, link) => todo!(),
                            DbType::Unknown => Inferred::new_unknown(),
                        };
                    } else {
                        inferred = Inferred::new_unknown()
                    }
                    todo!();
                    // Always overwrite the inferred string literal
                    //return inferred.save_redirect(self.file, expr_part_index);
                }

                if self.file.points.get(expr_part_index).calculated() {
                    inferred
                } else {
                    inferred.save_redirect(self.file, expr_part_index)
                }
                */
                todo!()
            }
            ExpressionContent::Lambda(_) | ExpressionContent::Ternary(_) => Inferred::new_unknown(),
        }
    }

    pub fn infer_return_annotation(&mut self, annotation: ReturnAnnotation<'db>) -> Inferred<'db> {
        self.infer_annotation_internal(annotation.index(), annotation.expression())
    }

    pub fn infer_annotation(&mut self, annotation: Annotation<'db>) -> Inferred<'db> {
        self.infer_annotation_internal(annotation.index(), annotation.expression())
    }

    fn infer_annotation_internal(
        &mut self,
        annotation_index: NodeIndex,
        expr: Expression<'db>,
    ) -> Inferred<'db> {
        let specific = self.cache_annotation_internal(annotation_index, expr);

        if specific == Specific::AnnotationWithTypeVars {
            // TODO this is always a TypeInstance, just use that.
            let inferred = self.check_point_cache(expr.index()).unwrap();
            let type_ = inferred.class_as_type(self.i_s);
            type_.execute_and_resolve_type_vars(self.i_s, self.i_s.current_class, None)
        } else {
            self.check_point_cache(expr.index()).unwrap()
        }
    }

    fn infer_annotation_string(&mut self, string: String) -> InferredType<'db> {
        let file = self
            .i_s
            .database
            .load_annotation_file(self.file.file_index(), string);
        if let Some(expr) = file.tree.maybe_expression() {
            file.inference(self.i_s).infer_type(expr)
        } else {
            debug!("Found non-expression in annotation: {}", file.tree.code());
            todo!()
        }
    }

    #[inline]
    fn cache_annotation_internal(
        &mut self,
        annotation_index: NodeIndex,
        expr: Expression<'db>,
    ) -> Specific {
        let point = self.file.points.get(annotation_index);
        if point.calculated() {
            return point.specific();
        }

        let InferredType {
            type_,
            has_type_vars,
        } = self.infer_type(expr);

        let specific = match type_ {
            TypeContent::ClassWithoutTypeVar(i) => {
                i.save_redirect(self.file, expr.index());
                Specific::AnnotationClassInstance
            }
            TypeContent::DbType(d) => {
                Inferred::new_unsaved_complex(ComplexPoint::TypeInstance(Box::new(d)))
                    .save_redirect(self.file, expr.index());
                if has_type_vars {
                    Specific::AnnotationWithTypeVars
                } else {
                    Specific::AnnotationWithoutTypeVars
                }
            }
        };
        self.file.points.set(
            annotation_index,
            Point::new_simple_specific(specific, Locality::Todo),
        );
        specific
    }

    pub fn infer_type(&mut self, expr: Expression<'db>) -> InferredType<'db> {
        match expr.unpack() {
            ExpressionContent::ExpressionPart(n) => self.infer_type_expression_part(n),
            ExpressionContent::Lambda(_) => todo!(),
            ExpressionContent::Ternary(t) => todo!(),
        }
    }
    fn infer_type_expression_part(&mut self, node: ExpressionPart<'db>) -> InferredType<'db> {
        match node {
            ExpressionPart::Atom(atom) => self.infer_type_atom(atom),
            ExpressionPart::Primary(primary) => self.infer_type_primary(primary),
            ExpressionPart::BitwiseOr(bitwise_or) => {
                let (a, b) = bitwise_or.unpack();
                // TODO this should only merge in annotation contexts
                let other = self.infer_type_expression_part(b);
                self.infer_type_expression_part(a).union(self.i_s, other)
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

    fn infer_type_primary(&mut self, primary: Primary<'db>) -> InferredType<'db> {
        let base = self.infer_primary_or_atom(primary.first());
        match primary.second() {
            PrimaryContent::Attribute(name) => todo!()/*base.run_on_value(self.i_s, &mut |i_s, value| {
                debug!("Type lookup {}.{}", value.name(), name.as_str());
                /*
                InferredType {
                    type_: value.lookup(i_s, name.as_str(), NodeRef::new(self.file, primary_index)),
                    has_type_vars: false,
                }
                */
            })*/,
            PrimaryContent::Execution(details) => {
                todo!()
            }
            PrimaryContent::GetItem(slice_type) => {
                todo!()
                /*
                let f = self.file;
                base.run_on_value(self.i_s, &mut |i_s, value| {
                    debug!("Get Item on {}", value.name());
                    let x = i_s.current_execution.and_then(|x| x.1.as_execution(x.0));
                    value.get_item(i_s, &SliceType::new(f, primary_index, slice_type))
                })
                */
            }
        }
    }

    fn infer_type_primary_or_atom(&mut self, p: PrimaryOrAtom<'db>) -> InferredType<'db> {
        match p {
            PrimaryOrAtom::Primary(primary) => self.infer_type_primary(primary),
            PrimaryOrAtom::Atom(atom) => self.infer_type_atom(atom),
        }
    }

    fn infer_type_atom(&mut self, atom: Atom<'db>) -> InferredType<'db> {
        match atom.unpack() {
            AtomContent::Name(n) => return self.infer_type_name(n),
            AtomContent::StringsOrBytes(s_o_b) => {
                if let Some(s) = s_o_b.as_python_string() {
                    if let Some(s) = s.to_owned() {
                        self.infer_annotation_string(s)
                    } else {
                        todo!()
                    }
                } else {
                    todo!()
                }
            }
            AtomContent::NoneLiteral => InferredType::new(TypeContent::DbType(DbType::None)),
            _ => todo!(),
        }
    }

    fn infer_type_name(&mut self, name: Name<'db>) -> InferredType<'db> {
        let point = self.file.points.get(name.index());
        if point.calculated() {
            if point.type_() == PointType::Specific {
                todo!()
            } else {
                let file = match point.file_index() == self.file.file_index() {
                    true => self.file,
                    false => self.i_s.database.loaded_python_file(point.file_index()),
                };
                let name = Name::maybe_by_index(&file.tree, point.node_index()).unwrap();
                match name.expect_type() {
                    TypeLike::ClassDef(c) => {
                        return InferredType {
                            type_: TypeContent::ClassWithoutTypeVar(Inferred::new_saved(
                                file,
                                c.index(),
                                file.points.get(c.index()),
                            )),
                            has_type_vars: false,
                        }
                    }
                    TypeLike::SimpleAssignment(expr) => {
                        todo!()
                    }
                    TypeLike::Function => {
                        todo!()
                    }
                    TypeLike::Other => {
                        todo!()
                    }
                }
            }
        }

        // class alias import ?
        let point = if let Some(link) = self
            .i_s
            .database
            .python_state
            .builtins()
            .lookup_global(name.as_str())
        {
            debug_assert!(link.file != self.file_index || link.node_index != name.index());
            dbg!(&link.file, link.node_index);
            link.into_point_redirect()
        } else {
            todo!()
        };
        self.file.points.set_on_name(&name, point);
        debug_assert!(self.file.points.get(name.index()).calculated());
        todo!()
    }
}
