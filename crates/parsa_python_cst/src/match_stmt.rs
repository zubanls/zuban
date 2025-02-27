use crate::{
    Block, CaseBlock, Expression, Guard, MatchStmt, NamedExpression, OpenSequencePattern, Pattern,
    StarLikeExpressionIterator, SubjectExpr,
};
use parsa_python::{NonterminalType::*, PyNodeType::Nonterminal};

impl<'db> MatchStmt<'db> {
    pub fn unpack(&self) -> (SubjectExpr<'db>, impl Iterator<Item = CaseBlock<'db>>) {
        let mut iterator = self.node.iter_children().skip(1);
        let subject = SubjectExpr::new(iterator.next().unwrap());
        (
            subject,
            iterator.skip(3).filter_map(|n| {
                n.is_type(Nonterminal(case_block))
                    .then(|| CaseBlock::new(n))
            }),
        )
    }
}

impl<'db> SubjectExpr<'db> {
    pub fn unpack(&self) -> SubjectExprContent {
        let child = self.node.nth_child(0);
        if child.is_type(Nonterminal(named_expression)) {
            SubjectExprContent::NamedExpression(NamedExpression::new(child))
        } else {
            debug_assert_eq!(child.type_(), Nonterminal(star_named_expressions));
            SubjectExprContent::Tuple(StarLikeExpressionIterator::Elements(
                child.iter_children().step_by(2),
            ))
        }
    }
}

pub enum SubjectExprContent<'db> {
    NamedExpression(NamedExpression<'db>),
    Tuple(StarLikeExpressionIterator<'db>),
}

impl<'db> CaseBlock<'db> {
    pub fn unpack(&self) -> (CasePattern<'db>, Option<Guard<'db>>, Block<'db>) {
        let mut iterator = self.node.iter_children().skip(1);
        let second = iterator.next().unwrap();
        let case_pattern = if second.is_type(Nonterminal(pattern)) {
            CasePattern::Pattern(Pattern::new(second))
        } else {
            CasePattern::OpenSequencePattern(OpenSequencePattern::new(second))
        };
        let maybe_guard = iterator.next().unwrap();
        let guard_ = if maybe_guard.is_type(Nonterminal(guard)) {
            iterator.next();
            Some(Guard::new(maybe_guard))
        } else {
            None
        };
        (case_pattern, guard_, Block::new(iterator.next().unwrap()))
    }
}

pub enum CasePattern<'db> {
    Pattern(Pattern<'db>),
    OpenSequencePattern(OpenSequencePattern<'db>),
}

impl<'db> Pattern<'db> {
    pub fn unpack(&self) -> () {
        todo!()
    }
}

impl<'db> Guard<'db> {
    pub fn named_expr(&self) -> NamedExpression<'db> {
        NamedExpression::new(self.node.nth_child(1))
    }
}
