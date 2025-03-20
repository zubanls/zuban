use crate::node_ref::NodeRef;

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
}
