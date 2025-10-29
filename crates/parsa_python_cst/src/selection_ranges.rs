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
        if node.start() == position
            && (node.type_() == PyNodeType::Keyword || node.as_code().ends_with("\n"))
            && let Some(previous) = node.previous_leaf()
            && previous.end() == position
        {
            node = previous
        }
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
            code: self.code(),
            node: Some(initial),
            previous: None,
        }
    }
}

struct SelectionRanges<'tree> {
    code: &'tree str,
    node: Option<PyNode<'tree>>,
    previous: Option<Range>,
}

impl Iterator for SelectionRanges<'_> {
    type Item = Range;

    fn next(&mut self) -> Option<Self::Item> {
        let node = self.node?;
        self.node = node.parent();
        let mut range = Range {
            start: node.start(),
            end: node.end(),
        };
        let type_ = node.type_();
        if let Some(previous) = self.previous {
            // We never want to repeat the same range.
            if previous == range {
                return self.next();
            }
        }
        if let PyNodeType::Nonterminal(stmt) = type_ {
            let before_node_code = &self.code[..node.start() as usize];
            if let Some(prefix_n) = before_node_code.rfind('\n') {
                // Set the start to after the newline, this is also how Pylance does it and seems
                // reasonable.
                range.start -= before_node_code.len() as CodeIndex - prefix_n as CodeIndex - 1;
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
            | PyNodeType::Nonterminal(kwargs | block | simple_stmts) => self.next(),
            _ => {
                self.previous = Some(range);
                Some(range)
            }
        }
    }
}
