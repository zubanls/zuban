use parsa_python_cst::Expression;

use crate::{
    arguments::Args,
    database::PointLink,
    diagnostics::IssueKind,
    node_ref::NodeRef,
    type_::{NewType, Type},
};

use super::{TypeComputation, TypeContent};

impl<'db, 'file> TypeComputation<'db, 'file, '_, '_> {
    pub(super) fn compute_new_type_assignment(&mut self, args: &dyn Args<'db>) -> Option<NewType> {
        let Some((first, second)) = args.maybe_two_positional_args(self.i_s) else {
            args.add_issue(
                self.i_s,
                IssueKind::ArgumentIssue(Box::from(
                    "NewType(...) expects exactly two positional arguments",
                )),
            );
            return None;
        };
        let result = first
            .expect_named_expression()
            .maybe_single_string_literal()
            .map(|py_string| (first, py_string));
        let (name_node, py_string) = match result {
            Some(result) => result,
            None => {
                first.add_issue(
                    self.i_s,
                    IssueKind::ArgumentIssue(Box::from(
                        "Argument 1 to NewType(...) must be a string literal",
                    )),
                );
                return None;
            }
        };
        let Some(name_def) = py_string.in_simple_assignment() else {
            first.add_issue(
                self.i_s,
                IssueKind::InvalidAssignmentForm {
                    class_name: "NewType",
                },
            );
            return None;
        };
        if name_def.as_code() != py_string.content() {
            name_node.add_issue(
                self.i_s,
                IssueKind::VarNameMismatch {
                    class_name: "NewType".into(),
                    string_name: Box::from(py_string.content()),
                    variable_name: Box::from(name_def.as_code()),
                },
            );
        }
        let type_ =
            self.compute_new_type_constraint(second.expect_named_expression().expression())?;
        Some(NewType::new(
            PointLink {
                file: name_node.file_index(),
                node_index: name_def.name_index(),
            },
            PointLink {
                file: name_node.file_index(),
                node_index: py_string.index(),
            },
            type_,
        ))
    }

    fn compute_new_type_constraint(&mut self, expr: Expression) -> Option<Type> {
        let node_ref = NodeRef::new(self.file, expr.index());
        match self.compute_type(expr) {
            TypeContent::InvalidVariable(_) => {
                node_ref.add_issue(self.i_s, IssueKind::NewTypeInvalidType);
                None
            }
            t => {
                let t = self.as_type(t, node_ref);
                if !t.is_subclassable(self.i_s.db) {
                    node_ref.add_issue(
                        self.i_s,
                        IssueKind::NewTypeMustBeSubclassable {
                            got: t.format_short(self.i_s.db),
                        },
                    );
                }
                if t.maybe_class(self.i_s.db)
                    .is_some_and(|cls| cls.is_protocol(self.i_s.db))
                {
                    node_ref.add_issue(self.i_s, IssueKind::NewTypeCannotUseProtocols);
                }
                Some(t)
            }
        }
    }
}
