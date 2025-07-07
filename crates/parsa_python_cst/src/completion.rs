use parsa_python::{CodeIndex, NonterminalType::*, PyNode, PyNodeType::Nonterminal};

use crate::{Atom, Primary, PrimaryOrAtom, Tree};

impl Tree {
    pub fn completion_node(&self, position: CodeIndex) -> CompletionNode {
        let mut leaf = self.0.leaf_by_position(position);
        if leaf.start() == position {
            if let Some(n) = leaf.previous_leaf() {
                if n.end() == position {
                    leaf = n;
                }
            }
        }
        let rest = RestNode::new(leaf, position);
        if position < leaf.start() {
            if leaf.prefix().contains("#") {
                return CompletionNode::Global { rest: None };
            }
        }
        if let Some(previous) = leaf.previous_leaf() {
            if previous.as_code() == "." {
                if let Some(before_dot) = previous.previous_sibling() {
                    let mut base = None;
                    if before_dot.is_type(Nonterminal(atom)) {
                        base = Some(PrimaryOrAtom::Atom(Atom::new(before_dot)))
                    } else if before_dot.is_type(Nonterminal(primary)) {
                        base = Some(PrimaryOrAtom::Primary(Primary::new(before_dot)))
                    }
                    if let Some(base) = base {
                        return CompletionNode::Attribute { base, rest };
                    }
                }
            }
        }
        CompletionNode::Global { rest: Some(rest) }
    }
}

#[derive(Debug)]
pub enum CompletionNode<'db> {
    Attribute {
        base: PrimaryOrAtom<'db>,
        rest: RestNode<'db>,
    },
    Global {
        rest: Option<RestNode<'db>>,
    },
}

/// Holds all kinds of nodes including invalid ones that might be valid starts for completion.
#[derive(Debug)]
pub struct RestNode<'db> {
    node: PyNode<'db>,
    position: CodeIndex,
}

impl<'db> RestNode<'db> {
    fn new(node: PyNode<'db>, position: CodeIndex) -> Self {
        Self { node, position }
    }

    pub fn is_string(&self) -> bool {
        let code = self.node.as_code();
        for c in code.chars().take(3) {
            if matches!(c, '"' | '\'') {
                return true;
            }
        }
        false
    }

    pub fn as_code(&self) -> &'db str {
        &self.node.as_code()[..(self.position - self.node.start()) as usize]
    }
}
