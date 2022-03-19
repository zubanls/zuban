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
                let mut inferred = inference.infer_expression_part(n);

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
}
