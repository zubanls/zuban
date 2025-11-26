use parsa_python::{
    CodeIndex,
    NonterminalType::*,
    PyNode,
    PyNodeType::{ErrorNonterminal, Nonterminal},
};

use crate::{
    Atom, ClassDef, DottedImportName, FunctionDef, Lambda, NameDef, Primary, PrimaryContent,
    PrimaryOrAtom, PrimaryTarget, PrimaryTargetOrAtom, Tree,
};

impl Tree {
    pub fn completion_node(
        &self,
        position: CodeIndex,
    ) -> (Scope<'_>, CompletionNode<'_>, RestNode<'_>) {
        let mut leaf = self.0.leaf_by_position(position);
        let is_control = |n: PyNode| {
            let next_char = n.as_code().chars().next().unwrap();
            !next_char.is_alphanumeric() && next_char != '_'
        };
        if leaf.start() == position
            && let Some(n) = leaf.previous_leaf()
        {
            // Only use the previous leaf if we are not on a control character.
            if n.end() == position && !is_control(n) {
                leaf = n;
            }
        }
        if leaf.end() == position && leaf.as_code() == "." {
            leaf = leaf.next_leaf().unwrap();
        }
        let scope = scope_for_node(leaf);
        let rest = RestNode::new(
            self,
            if leaf.end() == position
                && is_control(leaf)
                && let Some(n) = leaf.next_leaf()
            {
                n
            } else {
                leaf
            },
            position,
        );
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
                    if let Some(before) = parent.previous_sibling()
                        && before.as_code() == "from"
                    {
                        return (scope, CompletionNode::NecessaryKeyword("import"), rest);
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
                } else if leaf_parent.is_type(Nonterminal(name_def)) {
                    let parent = leaf_parent.parent().unwrap();
                    if parent.is_type(Nonterminal(t_primary)) {
                        let prim = PrimaryTarget::new(parent);
                        return (
                            scope,
                            CompletionNode::PrimaryTarget { base: prim.first() },
                            rest,
                        );
                    }
                } else if leaf_parent.is_type(Nonterminal(t_primary)) {
                    let prim = PrimaryTarget::new(leaf_parent);
                    return (
                        scope,
                        CompletionNode::PrimaryTarget { base: prim.first() },
                        rest,
                    );
                }
            }
        }
        (
            scope,
            CompletionNode::Global {
                context: context(leaf),
            },
            rest,
        )
    }
}

fn context(node: PyNode) -> Option<CompletionContext> {
    let parent = node.parent_until(&[
        Nonterminal(primary),
        Nonterminal(t_primary),
        Nonterminal(stmt),
    ])?;
    if parent.is_type(Nonterminal(primary)) {
        Primary::new(parent).first();
        let prim = Primary::new(parent);
        if matches!(prim.second(), PrimaryContent::Execution(_)) {
            Some(CompletionContext::PrimaryCall(prim.first()))
        } else {
            context(parent)
        }
    } else if parent.is_type(Nonterminal(t_primary)) {
        None
        //PrimaryTarget::new(parent).second()
    } else {
        None
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

#[derive(Copy, Clone, Debug)]
pub enum Scope<'db> {
    Module,
    Class(ClassDef<'db>),
    Function(FunctionDef<'db>),
    Lambda(Lambda<'db>),
}

impl Scope<'_> {
    pub fn short_debug_info(&self) -> String {
        match self {
            Scope::Module => "Module".into(),
            Scope::Class(c) => format!("class {}", c.name().as_code()),
            Scope::Function(f) => format!("def {}", f.name().as_code()),
            Scope::Lambda(_) => "Lambda".into(),
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub enum CompletionNode<'db> {
    Attribute {
        base: PrimaryOrAtom<'db>,
    },
    PrimaryTarget {
        base: PrimaryTargetOrAtom<'db>,
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
    Global {
        context: Option<CompletionContext<'db>>,
    },
}

#[derive(Debug, Copy, Clone)]
pub enum CompletionContext<'db> {
    PrimaryCall(PrimaryOrAtom<'db>),
    PrimaryTargetCall(PrimaryTargetOrAtom<'db>),
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

    pub fn start(&self) -> CodeIndex {
        self.node.start().min(self.position)
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

    pub fn ensure_no_rest(&mut self) {
        self.position = 0;
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
