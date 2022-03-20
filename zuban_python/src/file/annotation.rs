use parsa_python_ast::*;

use crate::database::{DbType, FormatStyle, Locality, Point, Specific};
use crate::debug;
use crate::diagnostics::IssueType;
use crate::file::PythonInference;
use crate::file_state::File;
use crate::generics::{search_type_vars_within_possible_class, Type};
use crate::inferred::Inferred;
use crate::node_ref::NodeRef;
use crate::value::{ClassLike, Value};


struct InferredType<'db> {
    type_: Inferred<'db>,
    has_type_vars: bool,
}

impl InferredType<'_> {
    pub fn union(self, other: Self) -> Self {
        Self {
            type_: self.type_.union(other.type_),
            has_type_vars: self.has_type_vars | other.has_type_vars,
        }
    }
}

impl<'db, 'a, 'b> PythonInference<'db, 'a, 'b> {
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
                    // Always overwrite the inferred string literal
                    return inferred.save_redirect(self.file, expr_part_index);
                }

                if self.file.points.get(expr_part_index).calculated() {
                    inferred
                } else {
                    inferred.save_redirect(self.file, expr_part_index)
                }
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
        if let Some(inferred) = self.check_point_cache(annotation_index) {
            return inferred;
        }

        // Make sure that we're not working "inside" of a function/closure. Annotations are always
        // considered global and should not use params or local state.
        let mut i_s = self.i_s.with_annotation_instance();
        let mut inference = self.file.inference(&mut i_s);
        let inferred = inference.infer_annotation_expression_class(expr);
        // TODO locality is wrong!!!!!1
        let type_ = inferred.as_type(self.i_s);
        let point = if matches!(type_, Type::Unknown) {
            return Inferred::new_unknown()
        } else if type_.has_type_vars(self.i_s) {
            // Cannot save this, because different type vars change the output.
            return type_.execute_and_resolve_type_vars(self.i_s, self.i_s.current_class, None);
        } else if matches!(type_, Type::ClassLike(ClassLike::Class(_))) {
            Point::new_simple_specific(Specific::AnnotationInstance, Locality::Todo)
        } else {
            return type_
                .maybe_execute(self.i_s)
                .save_redirect(self.file, annotation_index);
        };
        Inferred::new_and_save(self.file, annotation_index, point)
    }

    pub fn infer_annotation_string(&mut self, string: String) -> DbType {
        let file = self
            .i_s
            .database
            .load_annotation_file(self.file.file_index(), string);
        if let Some(expr) = file.tree.maybe_expression() {
            let mut found_type_vars = vec![];
            search_type_vars_within_possible_class(
                self.i_s,
                file,
                &expr,
                &mut found_type_vars,
                self.i_s.current_class,
                true,
                Specific::LateBoundTypeVar,
            );
            let db_type = file
                .inference(self.i_s)
                .infer_annotation_expression_class(expr)
                .as_db_type(self.i_s);
            debug!(
                "Inferred annotation string as {}",
                db_type.as_type_string(self.i_s.database, None, FormatStyle::Short)
            );
            return db_type;
        }
        debug!("Found non-expression in annotation: {}", file.tree.code());
        DbType::Unknown
    }

    fn infer_type(&mut self, expr: Expression<'db>) -> InferredType<'db> {
        let InferredType {type_, has_type_vars} = match expr.unpack() {
            ExpressionContent::ExpressionPart(n) => self.infer_type_expression_part(n),
            ExpressionContent::Lambda(_) => todo!(),
            ExpressionContent::Ternary(t) => todo!(),
        };
        InferredType {
            type_: type_.save_redirect(self.file, expr.index()),
            has_type_vars,
        }
    }
    fn infer_type_expression_part(&mut self, node: ExpressionPart<'db>) -> InferredType<'db> {
        match node {
            ExpressionPart::Atom(atom) => self.infer_type_atom(atom),
            ExpressionPart::Primary(primary) => self.infer_type_primary(primary),
            ExpressionPart::BitwiseOr(bitwise_or) => {
                let (a, b) = bitwise_or.unpack();
                // TODO this should only merge in annotation contexts
                self.infer_type_expression_part(a)
                    .union(self.infer_type_expression_part(b))
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
        use AtomContent::*;
        let specific = match atom.unpack() {
            Name(n) => return self.infer_type_name(n),
            StringsOrBytes(s_o_b) => {
                let mut iterator = s_o_b.iter();
                match iterator.next().unwrap() {
                    StringOrByte::String(s) => {
                        if iterator.next().is_none() {
                            return self.infer_annotation_string(s)
                        } else {
                            todo!("multiple strings")
                        }
                    },
                    StringOrByte::Bytes(_) => todo!(),
                    StringOrByte::FString(f) => todo!(),
                };
                for string_or_byte in iterator {
                    if let StringOrByte::FString(f) = string_or_byte {
                        self.calc_fstring_diagnostics(f)
                    }
                }
            }
            NoneLiteral => return None
            _ => todo!(),
        };
        let point = Point::new_simple_specific(specific, Locality::Todo);
        InferredType {
            type_: Inferred::new_and_save(self.file, atom.index(), point),
            has_type_vars: false,
        }
    }

    fn infer_type_name(&mut self, name: Name<'db>) -> InferredType<'db> {
        let point = self.file.points.get(name.index());
        if point.calculated() {
            let file = match point.file_index() == self.file.file_index() {
                true => self.file,
                false => self.i_s.database.loaded_python_file(point.file_index()),
            };
            let name = Name::maybe_by_index(&file.tree, point.node_index()).unwrap();
            match name.expect_type() {
                TypeLike::ClassDef(c) => {
                    return InferredType {
                        type_: Inferred::new_saved(file, c.index(), file.points.get(c.index())),
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
