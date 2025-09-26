use crate::{
    Block, Bytes, CaseBlock, ClassPattern, ComplexNumber, DottedPatternName, DoubleStarPattern,
    GroupPattern, Guard, KeyValuePattern, KeywordPattern, LiteralPattern, MappingPattern,
    MatchStmt, Name, NameDef, NamedExpression, OpenSequencePattern, OrPattern, Pattern,
    SequencePattern, SignedNumber, StarLikeExpressionIterator, StarPattern, Strings, SubjectExpr,
    UnpackedNumber, WildcardPattern,
};
use parsa_python::{NonterminalType::*, PyNode, PyNodeType::Nonterminal, SiblingIterator};

impl<'db> MatchStmt<'db> {
    pub fn unpack(&self) -> (SubjectExpr<'db>, impl Iterator<Item = CaseBlock<'db>>) {
        let mut iterator = self.node.iter_children().skip(1);
        let subject = SubjectExpr::new(iterator.next().unwrap());
        (
            subject,
            iterator
                .skip(3)
                .filter(|&n| n.is_type(Nonterminal(case_block)))
                .map(CaseBlock::new),
        )
    }
}

impl<'db> SubjectExpr<'db> {
    pub fn unpack(&self) -> SubjectExprContent<'_> {
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
    DottedName(DottedPatternName<'db>),
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
        (
            pattern_node_to_kind(first),
            iterator.nth(1).map(NameDef::new),
        )
    }
}

fn pattern_node_to_kind(node: PyNode) -> PatternKind {
    if node.is_type(Nonterminal(name_def)) {
        PatternKind::NameDef(NameDef::new(node))
    } else if node.is_type(Nonterminal(wildcard_pattern)) {
        PatternKind::WildcardPattern(WildcardPattern::new(node))
    } else if node.is_type(Nonterminal(dotted_pattern_name)) {
        PatternKind::DottedName(DottedPatternName::new(node))
    } else if node.is_type(Nonterminal(class_pattern)) {
        PatternKind::ClassPattern(ClassPattern::new(node))
    } else if node.is_type(Nonterminal(literal_pattern)) {
        PatternKind::LiteralPattern(LiteralPattern::new(node))
    } else if node.is_type(Nonterminal(group_pattern)) {
        PatternKind::GroupPattern(GroupPattern::new(node))
    } else if node.is_type(Nonterminal(sequence_pattern)) {
        PatternKind::SequencePattern(SequencePattern::new(node))
    } else if node.is_type(Nonterminal(or_pattern)) {
        PatternKind::OrPattern(OrPattern::new(node))
    } else {
        debug_assert_eq!(node.type_(), Nonterminal(mapping_pattern), "{node:?}");
        PatternKind::MappingPattern(MappingPattern::new(node))
    }
}

impl<'db> ClassPattern<'db> {
    pub fn unpack(
        &self,
    ) -> (
        DottedPatternName<'db>,
        impl Iterator<Item = ParamPattern<'db>>,
    ) {
        let mut iterator = self.node.iter_children();
        let dotted = DottedPatternName::new(iterator.next().unwrap());
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

impl<'db> KeywordPattern<'db> {
    pub fn unpack(&self) -> (Name<'db>, Pattern<'db>) {
        let mut iterator = self.node.iter_children();
        let name = Name::new(iterator.next().unwrap());
        iterator.next();
        let pat = Pattern::new(iterator.next().unwrap());
        (name, pat)
    }
}

impl<'db> SequencePattern<'db> {
    pub fn iter(&self) -> impl Iterator<Item = SequencePatternItem<'db>> {
        let node = self.node.nth_child(1);
        node.is_type(Nonterminal(open_sequence_pattern))
            .then(|| OpenSequencePattern::new(node).iter())
            .into_iter()
            .flatten()
    }
}

impl<'db> OpenSequencePattern<'db> {
    pub fn iter(&self) -> impl Iterator<Item = SequencePatternItem<'db>> + use<'db> {
        self.node.iter_children().step_by(2).map(|n| {
            if n.is_type(Nonterminal(pattern)) {
                SequencePatternItem::Entry(Pattern::new(n))
            } else {
                SequencePatternItem::Rest(StarPattern::new(n))
            }
        })
    }
}

pub enum SequencePatternItem<'db> {
    Entry(Pattern<'db>),
    Rest(StarPattern<'db>),
}

pub enum StarPatternContent<'db> {
    NameDef(NameDef<'db>),
    WildcardPattern(WildcardPattern<'db>),
}

impl<'db> StarPattern<'db> {
    pub fn unpack(&self) -> StarPatternContent<'db> {
        let n = self.node.nth_child(1);
        if n.is_type(Nonterminal(wildcard_pattern)) {
            StarPatternContent::WildcardPattern(WildcardPattern::new(n))
        } else {
            StarPatternContent::NameDef(NameDef::new(n))
        }
    }
}

impl<'db> MappingPattern<'db> {
    pub fn iter(&self) -> impl Iterator<Item = MappingPatternItem<'db>> {
        self.node
            .iter_children()
            .skip(1)
            .step_by(2)
            .filter_map(|n| {
                if n.is_type(Nonterminal(key_value_pattern)) {
                    Some(MappingPatternItem::Entry(KeyValuePattern::new(n)))
                } else if n.is_type(Nonterminal(double_star_pattern)) {
                    Some(MappingPatternItem::Rest(DoubleStarPattern::new(n)))
                } else {
                    debug_assert!(n.is_leaf(), "{n:?}");
                    None
                }
            })
    }
}

pub enum MappingPatternItem<'db> {
    Entry(KeyValuePattern<'db>),
    Rest(DoubleStarPattern<'db>),
}

impl<'db> KeyValuePattern<'db> {
    pub fn unpack(&self) -> (KeyEntryInPattern<'db>, Pattern<'db>) {
        let mut iterator = self.node.iter_children();
        let first = iterator.next().unwrap();
        let key = if first.is_type(Nonterminal(literal_pattern)) {
            KeyEntryInPattern::LiteralPattern(LiteralPattern::new(first))
        } else {
            KeyEntryInPattern::DottedName(DottedPatternName::new(first))
        };
        iterator.next();
        let value = Pattern::new(iterator.next().unwrap());
        (key, value)
    }
}

pub enum KeyEntryInPattern<'db> {
    LiteralPattern(LiteralPattern<'db>),
    DottedName(DottedPatternName<'db>),
}

impl<'db> DoubleStarPattern<'db> {
    pub fn name_def(&self) -> NameDef<'db> {
        NameDef::new(self.node.nth_child(1))
    }
}

impl<'db> GroupPattern<'db> {
    pub fn inner(&self) -> Pattern<'db> {
        Pattern::new(self.node.nth_child(1))
    }
}

impl<'db> OrPattern<'db> {
    pub fn iter(&self) -> impl Iterator<Item = PatternKind<'db>> {
        self.node
            .iter_children()
            .step_by(2)
            .map(pattern_node_to_kind)
    }
}

impl<'db> Guard<'db> {
    pub fn named_expr(&self) -> NamedExpression<'db> {
        NamedExpression::new(self.node.nth_child(1))
    }
}

pub enum LiteralPatternContent<'db> {
    Strings(Strings<'db>),
    Bytes(Bytes<'db>),
    SignedNumber(SignedNumber<'db>),
    ComplexNumber(ComplexNumber<'db>),
    None,
    Bool(bool),
}

impl<'db> LiteralPattern<'db> {
    pub fn unpack(&self) -> LiteralPatternContent<'db> {
        let node = self.node.nth_child(0);
        if node.is_type(Nonterminal(strings)) {
            LiteralPatternContent::Strings(Strings::new(node))
        } else if node.is_type(Nonterminal(bytes)) {
            LiteralPatternContent::Bytes(Bytes::new(node))
        } else if node.is_type(Nonterminal(signed_number)) {
            LiteralPatternContent::SignedNumber(SignedNumber::new(node))
        } else if node.is_type(Nonterminal(complex_number)) {
            LiteralPatternContent::ComplexNumber(ComplexNumber::new(node))
        } else if node.as_code() == "True" {
            LiteralPatternContent::Bool(true)
        } else if node.as_code() == "False" {
            LiteralPatternContent::Bool(false)
        } else {
            debug_assert_eq!(node.as_code(), "None");
            LiteralPatternContent::None
        }
    }
}

impl<'db> SignedNumber<'db> {
    pub fn number_and_is_negated(&self) -> (UnpackedNumber<'db>, bool) {
        let mut iter = self.node.iter_children();
        let mut number = iter.next().unwrap();
        let negated = number.as_code() == "-";
        if negated {
            number = iter.next().unwrap();
        }
        (UnpackedNumber::from_node(number), negated)
    }
}
