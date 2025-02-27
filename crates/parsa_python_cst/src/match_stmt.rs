use crate::{
    Block, CaseBlock, ClassPattern, DottedName, GroupPattern, Guard, KeywordPattern,
    LiteralPattern, MappingPattern, MatchStmt, NameDef, NamedExpression, OpenSequencePattern,
    OrPattern, Pattern, SequencePattern, StarLikeExpressionIterator, SubjectExpr, WildcardPattern,
};
use parsa_python::{NonterminalType::*, PyNodeType::Nonterminal, SiblingIterator};

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

pub enum PatternKind<'db> {
    NameDef(NameDef<'db>),
    WildcardPattern(WildcardPattern<'db>),
    DottedName(DottedName<'db>),
    ClassPattern(ClassPattern<'db>),
    LiteralPattern(LiteralPattern<'db>),
    GroupPattern(GroupPattern<'db>),
    OrPattern(OrPattern<'db>),
    SequencePattern(SequencePattern<'db>),
    MappingPattern(MappingPattern<'db>),
}

impl<'db> Pattern<'db> {
    pub fn unpack(&self) -> (PatternKind<'db>, Option<NameDef<'db>>) {
        let mut iterator = self.node.iter_children();
        let first = iterator.next().unwrap();
        let pat = if first.is_type(Nonterminal(name_def)) {
            PatternKind::NameDef(NameDef::new(first))
        } else if first.is_type(Nonterminal(wildcard_pattern)) {
            PatternKind::WildcardPattern(WildcardPattern::new(first))
        } else if first.is_type(Nonterminal(dotted_name)) {
            PatternKind::DottedName(DottedName::new(first))
        } else if first.is_type(Nonterminal(class_pattern)) {
            PatternKind::ClassPattern(ClassPattern::new(first))
        } else if first.is_type(Nonterminal(literal_pattern)) {
            PatternKind::LiteralPattern(LiteralPattern::new(first))
        } else if first.is_type(Nonterminal(group_pattern)) {
            PatternKind::GroupPattern(GroupPattern::new(first))
        } else if first.is_type(Nonterminal(sequence_pattern)) {
            PatternKind::SequencePattern(SequencePattern::new(first))
        } else if first.is_type(Nonterminal(or_pattern)) {
            PatternKind::OrPattern(OrPattern::new(first))
        } else {
            debug_assert_eq!(first.type_(), Nonterminal(mapping_pattern), "{first:?}");
            PatternKind::MappingPattern(MappingPattern::new(first))
        };
        (pat, iterator.skip(1).next().map(NameDef::new))
    }
}

impl<'db> ClassPattern<'db> {
    pub fn unpack(&self) -> (DottedName<'db>, impl Iterator<Item = ParamPattern<'db>>) {
        let mut iterator = self.node.iter_children();
        let dotted = DottedName::new(iterator.next().unwrap());
        iterator.next();
        let param_pattern_node = iterator.next().unwrap();
        let param_siblings = if param_pattern_node.is_type(Nonterminal(param_patterns)) {
            param_pattern_node.iter_children()
        } else {
            debug_assert!(param_pattern_node.is_leaf());
            SiblingIterator::new_empty(&self.node)
        };
        let param_iterator = param_siblings.step_by(2).map(|n| {
            if n.is_type(Nonterminal(pattern)) {
                ParamPattern::Positional(Pattern::new(n))
            } else {
                ParamPattern::Keyword(KeywordPattern::new(n))
            }
        });
        (dotted, param_iterator)
    }
}

pub enum ParamPattern<'db> {
    Positional(Pattern<'db>),
    Keyword(KeywordPattern<'db>),
}

impl<'db> Guard<'db> {
    pub fn named_expr(&self) -> NamedExpression<'db> {
        NamedExpression::new(self.node.nth_child(1))
    }
}
