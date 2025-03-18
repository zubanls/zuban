use std::rc::Rc;

use crate::{
    arguments::Args,
    database::{ComplexPoint, PointLink},
    diagnostics::IssueKind,
    file::name_resolution::NameResolution,
    inference_state::InferenceState,
    inferred::Inferred,
    node_ref::NodeRef,
    type_::NewType,
};

impl<'db, 'file> NameResolution<'db, 'file, '_> {
    pub(crate) fn compute_new_type_assignment(&self, args: &dyn Args<'db>) -> Inferred {
        if let Some(n) = maybe_new_type(self.i_s, args) {
            Inferred::new_unsaved_complex(ComplexPoint::NewTypeDefinition(Rc::new(n)))
        } else {
            Inferred::new_invalid_type_definition()
        }
    }
}

fn maybe_new_type<'db>(i_s: &InferenceState<'db, '_>, args: &dyn Args<'db>) -> Option<NewType> {
    let Some((first, second)) = args.maybe_two_positional_args(i_s) else {
        args.add_issue(
            i_s,
            IssueKind::ArgumentIssue(Box::from(
                "NewType(...) expects exactly two positional arguments",
            )),
        );
        return None;
    };
    let result = first
        .as_named_expression()
        .maybe_single_string_literal()
        .map(|py_string| (first, py_string));
    let (name_node, py_string) = match result {
        Some(result) => result,
        None => {
            first.add_issue(
                i_s,
                IssueKind::ArgumentIssue(Box::from(
                    "Argument 1 to NewType(...) must be a string literal",
                )),
            );
            return None;
        }
    };
    if let Some(name) = py_string.in_simple_assignment() {
        if name.as_code() != py_string.content() {
            name_node.add_issue(
                i_s,
                IssueKind::VarNameMismatch {
                    class_name: "NewType".into(),
                    string_name: Box::from(py_string.content()),
                    variable_name: Box::from(name.as_code()),
                },
            );
        }
    } else {
        first.add_issue(
            i_s,
            IssueKind::InvalidAssignmentForm {
                class_name: "NewType",
            },
        );
        return None;
    }
    let type_node_ref = NodeRef::new(
        second.file,
        second.as_named_expression().expression().index(),
    );
    Some(NewType::new(
        PointLink {
            file: name_node.file_index(),
            node_index: py_string.index(),
        },
        type_node_ref.as_link(),
    ))
}
