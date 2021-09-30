use parsa_python::{
    NonterminalType::*, PyNode, PyNodeType::Nonterminal, PyTree, SiblingIterator, TerminalType,
    PYTHON_GRAMMAR,
};

macro_rules! create_structs {
    ($($name:ident),+) => {
        $(
            pub struct $name<'db>(PyNode<'db>);
        )+
    }
}

create_structs!(Stmt, StarExpressions, StarExpressionsTuple, StarExpression);

impl<'db> Stmt<'db> {}

impl<'db> StarExpressions<'db> {
    pub fn new(node: PyNode<'db>) -> Self {
        Self(node)
    }

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
