use parsa_python::{CodeIndex, NonterminalType::*, PyNode, PyNodeType, TerminalType};

use crate::Tree;

#[derive(Clone, Copy, PartialEq)]
pub struct Range {
    pub start: CodeIndex,
    pub end: CodeIndex,
}

impl Tree {
    fn initial_node_for_selection_ranges(&self, position: CodeIndex) -> PyNode<'_> {
        let mut node = self.0.leaf_by_position(position);
        fn is_pos_in_node(node: PyNode, position: CodeIndex) -> bool {
            node.start() <= position && node.end() >= position
        }
        if !is_pos_in_node(node, position) {
            fn node_includes_in_position(initial: PyNode, position: CodeIndex) -> PyNode {
                let parent = initial.parent().unwrap();
                if is_pos_in_node(parent, position) {
                    parent
                } else {
                    node_includes_in_position(parent, position)
                }
            }

            node = node_includes_in_position(node, position);
        }
        node
    }

    pub fn selection_ranges(&self, position: CodeIndex) -> impl Iterator<Item = Range> {
        let initial = self.initial_node_for_selection_ranges(position);
        SelectionRanges {
            node: Some(initial),
            previous: None,
        }
    }
}

struct SelectionRanges<'tree> {
    node: Option<PyNode<'tree>>,
    previous: Option<Range>,
}

impl Iterator for SelectionRanges<'_> {
    type Item = Range;

    fn next(&mut self) -> Option<Self::Item> {
        let node = self.node?;
        self.node = node.parent();
        let range = Range {
            start: node.start(),
            end: node.end(),
        };
        if let Some(previous) = self.previous {
            // We never want to repeat the same range.
            if previous == range {
                return self.next();
            }
        }
        match node.type_() {
            PyNodeType::Terminal(
                TerminalType::Operator
                | TerminalType::Endmarker
                | TerminalType::Indent
                | TerminalType::Dedent
                | TerminalType::ErrorDedent,
            )
            | PyNodeType::Keyword
            | PyNodeType::Nonterminal(kwargs | block | simple_stmt | stmt) => self.next(),
            _ => {
                self.previous = Some(range);
                Some(range)
            }
        }
    }
}
