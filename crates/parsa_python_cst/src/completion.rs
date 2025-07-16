use parsa_python::{
    CodeIndex, NodeIndex,
    NonterminalType::*,
    PyNode,
    PyNodeType::{ErrorNonterminal, Nonterminal},
};

use crate::{Atom, DottedImportName, Lambda, NameDef, Primary, PrimaryOrAtom, Tree};

impl Tree {
    pub fn completion_node(&self, position: CodeIndex) -> (Scope, CompletionNode, RestNode) {
        let mut leaf = self.0.leaf_by_position(position);
        let scope = scope_for_node(leaf);
        if leaf.start() == position {
            if let Some(n) = leaf.previous_leaf() {
                if n.end() == position && n.as_code() != "." {
                    leaf = n;
                }
            }
        }
        if leaf.end() == position && leaf.as_code() == "." {
            leaf = leaf.next_leaf().unwrap();
        }
        let rest = RestNode::new(self, leaf, position);
        if position < leaf.start() {
            if leaf.prefix().contains("#") {
                return (scope, CompletionNode::Global, rest);
            }
        }
        if let Some(previous) = leaf.previous_leaf() {
            match previous.as_code() {
                "." => {
                    if let Some(before_dot) = previous.previous_sibling() {
                        let mut base = None;
                        if before_dot.is_type(Nonterminal(atom)) {
                            base = Some(PrimaryOrAtom::Atom(Atom::new(before_dot)))
                        } else if before_dot.is_type(Nonterminal(primary)) {
                            base = Some(PrimaryOrAtom::Primary(Primary::new(before_dot)))
                        } else if before_dot.is_type(Nonterminal(dotted_import_name)) {
                            return (
                                scope,
                                CompletionNode::DottedImportName {
                                    base: DottedImportName::new(before_dot),
                                },
                                rest,
                            );
                        } else if before_dot.is_type(Nonterminal(name_def))
                            && before_dot
                                .parent()
                                .unwrap()
                                .is_type(ErrorNonterminal(dotted_as_name))
                        {
                            return (
                                scope,
                                CompletionNode::ImportName {
                                    path: Some((NameDef::new(before_dot), None)),
                                },
                                rest,
                            );
                        }
                        if let Some(base) = base {
                            return (scope, CompletionNode::Attribute { base }, rest);
                        }
                    }
                }
                "import" => {
                    if let Some(before_imp) = previous.previous_sibling() {
                        if before_imp.is_type(Nonterminal(dotted_import_name)) {
                            return (
                                scope,
                                import_from_target_node(before_imp.parent().unwrap()),
                                rest,
                            );
                        }
                    } else {
                        return (scope, CompletionNode::ImportName { path: None }, rest);
                    }
                }
                "as" => {
                    return (scope, CompletionNode::AsNewName, rest);
                }
                "def" => {
                    return (scope, CompletionNode::AfterDefKeyword, rest);
                }
                "class" => {
                    return (scope, CompletionNode::AfterClassKeyword, rest);
                }
                _ => {
                    if let Some(parent) = previous.parent() {
                        if parent.is_type(Nonterminal(dotted_import_name)) {
                            if let Some(before) = parent.previous_sibling() {
                                if before.as_code() == "from" {
                                    return (
                                        scope,
                                        CompletionNode::NecessaryKeyword("import"),
                                        rest,
                                    );
                                }
                            }
                        } else if parent.is_type(ErrorNonterminal(import_from_targets)) {
                            return (
                                scope,
                                import_from_target_node(parent.parent().unwrap()),
                                rest,
                            );
                        }
                    }
                }
            }
        }
        (scope, CompletionNode::Global, rest)
    }
}

fn import_from_target_node(node: PyNode) -> CompletionNode {
    debug_assert!(
        matches!(
            node.type_(),
            Nonterminal(import_from) | ErrorNonterminal(import_from),
        ),
        "{:?}",
        node.type_()
    );
    let mut dots = 0;
    for child in node.iter_children().skip(1) {
        if child.is_type(Nonterminal(dotted_import_name)) {
            return CompletionNode::ImportFromTarget {
                base: Some(DottedImportName::new(child)),
                dots,
            };
        } else {
            match child.as_code() {
                "import" => break,
                "." => dots += 1,
                "..." => dots += 3,
                _ => unreachable!(),
            }
        }
    }
    debug_assert_ne!(dots, 0);
    CompletionNode::ImportFromTarget { base: None, dots }
}

pub(crate) fn scope_for_node<'db>(node: PyNode<'db>) -> Scope<'db> {
    let scope_node = node
        .parent_until(&[
            Nonterminal(file),
            Nonterminal(class_def),
            Nonterminal(function_def),
            Nonterminal(lambda),
        ])
        .expect("There should always be a file");
    if scope_node.is_type(Nonterminal(file)) {
        Scope::Module
    } else if scope_node.is_type(Nonterminal(function_def)) {
        Scope::Function(scope_node.index)
    } else if scope_node.is_type(Nonterminal(class_def)) {
        Scope::Class(scope_node.index)
    } else {
        debug_assert_eq!(scope_node.type_(), Nonterminal(lambda));
        Scope::Lambda(Lambda::new(scope_node))
    }
}

#[derive(Copy, Clone)]
pub enum Scope<'db> {
    Module,
    Class(NodeIndex),
    Function(NodeIndex),
    Lambda(Lambda<'db>),
}

#[derive(Debug)]
pub enum CompletionNode<'db> {
    Attribute {
        base: PrimaryOrAtom<'db>,
    },
    DottedImportName {
        base: DottedImportName<'db>,
    },
    ImportName {
        path: Option<(NameDef<'db>, Option<DottedImportName<'db>>)>,
    },
    ImportFromTarget {
        dots: usize,
        base: Option<DottedImportName<'db>>,
    },
    AsNewName,
    NecessaryKeyword(&'static str),
    AfterDefKeyword,
    AfterClassKeyword,
    Global,
}

/// Holds all kinds of nodes including invalid ones that might be valid starts for completion.
pub struct RestNode<'db> {
    tree: &'db Tree,
    node: PyNode<'db>,
    position: CodeIndex,
}

impl<'db> RestNode<'db> {
    fn new(tree: &'db Tree, node: PyNode<'db>, position: CodeIndex) -> Self {
        Self {
            tree,
            node,
            position,
        }
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
        // TODO it feels weird that we don't involve the prefix especially for comments
        if self.position < self.node.start() {
            return "";
        }
        &self.tree.code()[self.node.start() as usize..self.position as usize]
    }
}

impl std::fmt::Debug for RestNode<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct(stringify!(RestNode))
            .field("node", &self.node)
            .field("position", &self.position)
            .finish()
    }
}
