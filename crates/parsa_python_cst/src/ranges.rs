use parsa_python::{
    CodeIndex,
    NonterminalType::*,
    PyNode,
    PyNodeType::{self, Nonterminal},
    TerminalType,
};

use crate::{StarExpressions, Tree};

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

    pub fn initial_imports_end_code_index(&self) -> CodeIndex {
        for (i, n) in self.0.root_node().iter_children().enumerate() {
            let is_import = || {
                if !n.is_type(Nonterminal(stmt)) {
                    return false;
                }
                let first = n.nth_child(0);
                if !first.is_type(Nonterminal(simple_stmts)) {
                    return false;
                }
                for simp in first.iter_children().step_by(2) {
                    if simp.is_type(Nonterminal(simple_stmt)) {
                        let maybe_imp = simp.nth_child(0);
                        if maybe_imp.is_type(Nonterminal(star_expressions))
                            && i == 0
                            && StarExpressions::new(maybe_imp)
                                .maybe_simple_expression()
                                .and_then(|expr| expr.maybe_string())
                                .is_some()
                        {
                            return true;
                        }
                        if !maybe_imp.is_type(Nonterminal(import_from))
                            && !maybe_imp.is_type(Nonterminal(import_name))
                        {
                            return false;
                        }
                    }
                }
                true
            };
            if !is_import() {
                let prefix = n.prefix_to_previous_leaf();
                let mut last_newline = 0;
                if n.previous_sibling().is_none() {
                    // We want to preserve comments at the start of the file and will therefore
                    // only remove whitespace.
                    for (i, byte) in prefix.bytes().rev().enumerate() {
                        if byte == b'\n' {
                            last_newline = i;
                        } else if !byte.is_ascii_whitespace() {
                            return n.start() - last_newline as CodeIndex;
                        }
                    }
                }
                return n.start() - prefix.len() as CodeIndex;
            }
        }
        self.root().end()
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
        if let Nonterminal(stmt) = type_ {
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
            | Nonterminal(kwargs | block | simple_stmts) => self.next(),
            _ => {
                self.previous = Some(range);
                Some(range)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_initial_imports_with_carriage_return() {
        let code = "\r\n# x\r\nx\r\n";
        let parsed = Tree::parse(code.into());
        debug_assert_eq!(parsed.initial_imports_end_code_index(), 7);
        let parsed = Tree::parse(code.replace('\r', "").into());
        debug_assert_eq!(parsed.initial_imports_end_code_index(), 5);
    }
}
