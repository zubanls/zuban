use parsa_python::{
    NodeIndex, NonterminalType::*, PyNode, PyNodeType::Nonterminal, PyTree, SiblingIterator,
    TerminalType, PYTHON_GRAMMAR,
};

macro_rules! create_nonterminal_structs {
    ($($name:ident: $nonterminal:ident)+) => {
        $(
            pub struct $name<'db>(PyNode<'db>);
            impl<'db> $name<'db> {
                #[inline]
                pub fn new(node: PyNode<'db>) -> Self {
                    debug_assert_eq!(node.get_type(), Nonterminal($nonterminal));
                    Self(node)
                }

                #[inline]
                pub fn by_index(tree: &'db PyTree, index: NodeIndex) -> Self {
                    Self::new(tree.get_node_by_index(index))
                }
            }
        )+
    }
}

create_nonterminal_structs!(
    Stmt: stmt
    StarExpressions: star_expressions
    StarExpressionsTuple: star_expressions
    StarExpression: star_expression
);

impl<'db> Stmt<'db> {}

impl<'db> StarExpressions<'db> {
    pub fn unpack(&self) -> StarExpressionContent<'db> {
        let mut iter = self.0.iter_children();
        let expr = iter.next().unwrap();
        if iter.next().is_none() {
            if expr.is_type(Nonterminal(expression)) {
                StarExpressionContent::Expression(expr)
            } else {
                StarExpressionContent::StarExpression(StarExpression(expr))
            }
        } else {
            StarExpressionContent::Tuple(StarExpressionsTuple(self.0))
        }
    }
}

pub enum StarExpressionContent<'db> {
    Expression(PyNode<'db>),
    StarExpression(StarExpression<'db>),
    Tuple(StarExpressionsTuple<'db>),
}
