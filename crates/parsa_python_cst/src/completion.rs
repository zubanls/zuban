use parsa_python::{
    CodeIndex,
    NonterminalType::*,
    PyNode,
    PyNodeType::{ErrorNonterminal, Nonterminal},
};

use crate::{
    Atom, ClassDef, DottedImportName, FunctionDef, Lambda, NameDef, Primary, PrimaryOrAtom, Tree,
};

impl Tree {
    pub fn completion_node(&self, position: CodeIndex) -> (Scope, CompletionNode, RestNode) {
        let mut leaf = self.0.leaf_by_position(position);
        let scope = scope_for_node(leaf);
        if leaf.start() == position {
            if let Some(n) = leaf.previous_leaf() {
                // Only use the previous leaf if we are not on a control character.
                if n.end() == position && {
                    let next_char = n.as_code().chars().next().unwrap();
                    next_char.is_alphanumeric() || next_char == '_'
                } {
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
                            let before_import_names = before_dot.previous_leaf().unwrap();
                            if before_import_names.as_code() == "." {
                                let maybe_name_def =
                                    before_import_names.previous_sibling().unwrap();
                                if maybe_name_def.is_type(Nonterminal(name_def)) {
                                    // This is the case where we are in import_name
                                    let name_def_ = NameDef::new(maybe_name_def);
                                    return (
                                        scope,
                                        CompletionNode::ImportName {
                                            path: Some((
                                                name_def_,
                                                Some(DottedImportName::new(before_dot)),
                                            )),
                                        },
                                        rest,
                                    );
                                }
                            }
                            return (
                                scope,
                                CompletionNode::ImportFromFirstPart {
                                    base: Some(DottedImportName::new(before_dot)),
                                    dots: from_import_dots_before_node(
                                        before_dot.previous_leaf().unwrap(),
                                    ),
                                },
                                rest,
                            );
                        } else if before_dot.is_type(Nonterminal(name_def))
                            && matches!(
                                before_dot.parent().unwrap().type_(),
                                Nonterminal(dotted_as_name) | ErrorNonterminal(dotted_as_name)
                            )
                        {
                            return (
                                scope,
                                CompletionNode::ImportName {
                                    path: Some((NameDef::new(before_dot), None)),
                                },
                                rest,
                            );
                        } else if matches!(
                            previous.parent().unwrap().type_(),
                            Nonterminal(import_from) | ErrorNonterminal(import_from)
                        ) {
                            return (
                                scope,
                                CompletionNode::ImportFromFirstPart {
                                    base: None,
                                    dots: from_import_dots_before_node(
                                        before_dot.previous_leaf().unwrap(),
                                    ),
                                },
                                rest,
                            );
                        }
                        if let Some(base) = base {
                            return (scope, CompletionNode::Attribute { base }, rest);
                        }
                    }
                }
                "from" | "..." => {
                    if matches!(
                        previous.parent().unwrap().type_(),
                        Nonterminal(import_from) | ErrorNonterminal(import_from)
                    ) {
                        return (
                            scope,
                            CompletionNode::ImportFromFirstPart {
                                base: None,
                                dots: from_import_dots_before_node(previous),
                            },
                            rest,
                        );
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
                _ => (),
            }
            let parent = previous.parent().unwrap();
            match parent.type_() {
                Nonterminal(dotted_import_name) => {
                    if let Some(before) = parent.previous_sibling() {
                        if before.as_code() == "from" {
                            return (scope, CompletionNode::NecessaryKeyword("import"), rest);
                        }
                    }
                }
                Nonterminal(import_from_targets) | ErrorNonterminal(import_from_targets) => {
                    return (
                        scope,
                        import_from_target_node(parent.parent().unwrap()),
                        rest,
                    );
                }
                _ => (),
            }
            if let Some(leaf_parent) = leaf.parent() {
                if leaf_parent.is_type(ErrorNonterminal(import_from_targets)) {
                    return (
                        scope,
                        import_from_target_node(leaf_parent.parent().unwrap()),
                        rest,
                    );
                }
            }
        }
        (scope, CompletionNode::Global, rest)
    }
}

fn from_import_dots_before_node(leaf: PyNode) -> usize {
    debug_assert!(leaf.is_leaf());
    let count = match leaf.as_code() {
        "." => 1,
        "..." => 3,
        _ => return 0,
    };
    count + from_import_dots_before_node(leaf.previous_leaf().unwrap())
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
        Scope::Function(FunctionDef::new(scope_node))
    } else if scope_node.is_type(Nonterminal(class_def)) {
        Scope::Class(ClassDef::new(scope_node))
    } else {
        debug_assert_eq!(scope_node.type_(), Nonterminal(lambda));
        Scope::Lambda(Lambda::new(scope_node))
    }
}

#[derive(Copy, Clone)]
pub enum Scope<'db> {
    Module,
    Class(ClassDef<'db>),
    Function(FunctionDef<'db>),
    Lambda(Lambda<'db>),
}

#[derive(Debug)]
pub enum CompletionNode<'db> {
    Attribute {
        base: PrimaryOrAtom<'db>,
    },
    ImportName {
        path: Option<(NameDef<'db>, Option<DottedImportName<'db>>)>,
    },
    ImportFromFirstPart {
        dots: usize,
        base: Option<DottedImportName<'db>>,
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
