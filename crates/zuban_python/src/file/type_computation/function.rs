use parsa_python_cst::{
    Decorated, FunctionDef, FunctionParent, NodeIndex, ReturnAnnotation, ReturnOrYield,
};

use crate::{
    database::Database,
    diagnostics::{Issue, IssueKind},
    file::{PythonFile, FUNC_TO_RETURN_OR_YIELD_DIFF, FUNC_TO_TYPE_VAR_DIFF},
    inference_state::InferenceState,
    node_ref::NodeRef,
    type_::{StringSlice, TypeVarLikes},
};

#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) struct FuncNodeRef<'file>(NodeRef<'file>);

impl<'a> std::ops::Deref for FuncNodeRef<'a> {
    type Target = NodeRef<'a>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl std::cmp::PartialEq<NodeRef<'_>> for FuncNodeRef<'_> {
    fn eq(&self, other: &NodeRef) -> bool {
        self.0 == *other
    }
}

impl<'a> From<FuncNodeRef<'a>> for NodeRef<'a> {
    fn from(value: FuncNodeRef<'a>) -> Self {
        value.0
    }
}

impl<'db: 'file, 'file> FuncNodeRef<'file> {
    #[inline]
    pub fn from_node_ref(node_ref: NodeRef<'file>) -> Self {
        debug_assert!(node_ref.maybe_function().is_some(), "{node_ref:?}");
        Self(node_ref)
    }

    pub fn node(&self) -> FunctionDef<'file> {
        FunctionDef::by_index(&self.file.tree, self.node_index)
    }

    pub fn return_annotation(&self) -> Option<ReturnAnnotation> {
        self.node().return_annotation()
    }

    pub fn expect_return_annotation_node_ref(&self) -> NodeRef {
        NodeRef::new(
            self.file,
            self.return_annotation().unwrap().expression().index(),
        )
    }

    pub fn is_typed(&self) -> bool {
        self.node().is_typed()
    }

    pub fn iter_return_or_yield(&self) -> ReturnOrYieldIterator<'file> {
        let def_point = self
            .file
            .points
            .get(self.node_index + FUNC_TO_RETURN_OR_YIELD_DIFF);
        let first_return_or_yield = def_point.node_index();
        ReturnOrYieldIterator {
            file: self.file,
            next_node_index: first_return_or_yield,
        }
    }

    pub fn is_generator(&self) -> bool {
        for return_or_yield in self.iter_return_or_yield() {
            if let ReturnOrYield::Yield(_) = return_or_yield {
                return true;
            }
        }
        false
    }

    pub fn is_async(&self) -> bool {
        matches!(
            self.node().parent(),
            FunctionParent::Async | FunctionParent::DecoratedAsync(_)
        )
    }

    pub fn type_vars(&self, db: &'db Database) -> &'file TypeVarLikes {
        let type_var_reference = self.type_var_reference();
        if type_var_reference.point().calculated() {
            TypeVarLikes::load_saved_type_vars(db, type_var_reference)
        } else {
            unreachable!()
        }
    }

    pub fn type_var_reference(&self) -> NodeRef<'file> {
        self.add_to_node_index(FUNC_TO_TYPE_VAR_DIFF)
    }

    pub(crate) fn expect_decorated_node(&self) -> Decorated {
        self.node().maybe_decorated().unwrap()
    }

    pub(crate) fn add_issue_for_declaration(&self, i_s: &InferenceState, kind: IssueKind) {
        let node = self.node();
        self.file.add_issue(
            i_s,
            Issue {
                kind,
                start_position: node.start(),
                end_position: node.end_position_of_colon(),
            },
        )
    }

    pub(crate) fn add_issue_onto_start_including_decorator(
        &self,
        i_s: &InferenceState,
        kind: IssueKind,
    ) {
        let node = self.node();
        if let Some(decorated) = node.maybe_decorated() {
            NodeRef::new(self.file, decorated.index()).add_issue(i_s, kind)
        } else {
            self.add_issue_for_declaration(i_s, kind)
        }
    }

    pub fn name_string_slice(&self) -> StringSlice {
        let name = self.node().name();
        StringSlice::new(self.file_index(), name.start(), name.end())
    }

    pub fn name(&self) -> &'file str {
        let func = FunctionDef::by_index(&self.file.tree, self.node_index);
        func.name().as_str()
    }
}

pub struct ReturnOrYieldIterator<'a> {
    file: &'a PythonFile,
    next_node_index: NodeIndex,
}

impl<'a> Iterator for ReturnOrYieldIterator<'a> {
    type Item = ReturnOrYield<'a>;
    fn next(&mut self) -> Option<Self::Item> {
        if self.next_node_index == 0 {
            None
        } else {
            let point = self.file.points.get(self.next_node_index);
            let index = self.next_node_index;
            self.next_node_index = point.node_index();
            // - 1 because the index points to the next yield/return literal. The parent of those
            // literals are then `return_stmt` and `yield_expr` terminals.
            Some(ReturnOrYield::by_index(&self.file.tree, index - 1))
        }
    }
}
