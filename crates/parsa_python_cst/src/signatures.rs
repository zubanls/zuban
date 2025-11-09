use parsa_python::{
    CodeIndex, NodeIndex,
    NonterminalType::*,
    PyNode,
    PyNodeType::{ErrorNonterminal, Nonterminal, Terminal},
    SiblingIterator, TerminalType,
};

use crate::{
    AtomContent, Expression, ExpressionPart, Name, PrimaryTargetOrAtom, Scope, Tree,
    completion::scope_for_node,
};

impl Tree {
    pub fn signature_node(
        &self,
        position: CodeIndex,
    ) -> Option<(Scope<'_>, ExpressionPart<'_>, SignatureArgsIterator<'_>)> {
        let mut leaf = self.0.leaf_by_position(position);
        if leaf.start() == position {
            leaf = leaf.previous_leaf()?;
        }
        let mut next_stmt = None;
        let scope = scope_for_node(leaf);
        let mut check_node = leaf;
        loop {
            check_node = check_node.parent_until(&[
                Nonterminal(stmt),
                ErrorNonterminal(stmt),
                Nonterminal(primary),
                ErrorNonterminal(primary),
                Nonterminal(t_primary),
                ErrorNonterminal(t_primary),
            ])?;
            if check_node.is_type(Nonterminal(stmt)) {
                return None;
            } else if check_node.is_type(ErrorNonterminal(stmt)) {
                next_stmt = Some(check_node);
                check_node = check_node.previous_leaf()?;
                continue;
            }
            let mut iterator = check_node.iter_children();
            let Some(first) = iterator.next() else {
                continue;
            };
            let Some(maybe_paren) = iterator.next() else {
                continue;
            };
            if maybe_paren.as_code() != "(" || maybe_paren.end() > position {
                continue;
            }
            let base = ExpressionPart::new(first);
            let Some(maybe_args) = iterator.next() else {
                return Some((
                    scope,
                    base,
                    if next_stmt.is_some() {
                        SignatureArgsIterator::Args {
                            args: SiblingIterator::new_empty(&first),
                            next_stmt: next_stmt
                                .map(|node| ErrorStmtSignaturePart::new(node, leaf.index)),
                            until_position: position,
                        }
                    } else {
                        SignatureArgsIterator::None
                    },
                ));
            };
            if iterator.next().is_some_and(|node| node.start() < position) {
                continue;
            }
            if maybe_args.is_type(Nonterminal(arguments))
                || maybe_args.is_type(ErrorNonterminal(arguments))
            {
                return Some((
                    scope,
                    base,
                    SignatureArgsIterator::Args {
                        args: maybe_args.iter_children(),
                        next_stmt: next_stmt
                            .map(|node| ErrorStmtSignaturePart::new(node, leaf.index)),
                        until_position: position,
                    },
                ));
            } else if maybe_args.as_code() == ")" {
                if maybe_args.start() < position {
                    continue;
                }
                return Some((scope, base, SignatureArgsIterator::None));
            } else {
                debug_assert!(
                    maybe_args.is_type(Nonterminal(comprehension))
                        || maybe_args.is_type(ErrorNonterminal(comprehension))
                );
                return Some((scope, base, SignatureArgsIterator::Comprehension));
            }
        }
    }
}

#[derive(Debug, Clone)]
pub enum SignatureArgsIterator<'db> {
    Args {
        args: SiblingIterator<'db>,
        next_stmt: Option<ErrorStmtSignaturePart<'db>>,
        until_position: CodeIndex,
    },
    Comprehension,
    None,
}

#[derive(Debug)]
pub enum SignatureArg<'db> {
    PositionalOrEmptyAfterComma,
    PositionalOrKeywordName(&'db str),
    Keyword(Name<'db>),
    StarArgs,
    StarStarKwargs,
}

impl<'db> Iterator for SignatureArgsIterator<'db> {
    type Item = SignatureArg<'db>;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Args {
                args,
                next_stmt,
                until_position,
            } => {
                let Some(mut arg) = args.next() else {
                    return next_stmt.as_mut().and_then(|next_stmt| next_stmt.next());
                };
                if arg.as_code() == "," {
                    if arg.end() > *until_position {
                        return None;
                    }
                    if let Some(next) = args.next() {
                        arg = next;
                    } else {
                        return Some(SignatureArg::PositionalOrEmptyAfterComma);
                    }
                }
                if arg.is_type(Nonterminal(named_expression)) {
                    let expr = arg.nth_child(0);
                    if expr.is_type(Nonterminal(expression))
                        && let Some(AtomContent::Name(n)) =
                            Expression::new(expr).maybe_unpacked_atom()
                    {
                        return Some(SignatureArg::PositionalOrKeywordName(n.as_code()));
                    }
                }
                if arg.is_type(Nonterminal(kwargs)) || arg.is_type(ErrorNonterminal(kwargs)) {
                    *args = arg.iter_children();
                    self.next()
                } else if arg.is_type(Nonterminal(kwarg)) {
                    Some(SignatureArg::Keyword(Name::new(arg.nth_child(0))))
                } else if arg.is_type(ErrorNonterminal(kwarg)) {
                    let name = arg.nth_child(0);
                    debug_assert!(matches!(name.type_(), Terminal(TerminalType::Name)));
                    if name.next_leaf().is_some_and(|leaf| leaf.as_code() == "=") {
                        Some(SignatureArg::Keyword(Name::new(name)))
                    } else {
                        Some(SignatureArg::PositionalOrKeywordName(name.as_code()))
                    }
                } else if arg.is_type(Nonterminal(starred_expression))
                    || arg.is_type(ErrorNonterminal(starred_expression))
                {
                    Some(SignatureArg::StarArgs)
                } else if arg.is_type(Nonterminal(double_starred_expression))
                    || arg.is_type(ErrorNonterminal(double_starred_expression))
                {
                    Some(SignatureArg::StarStarKwargs)
                } else {
                    Some(SignatureArg::PositionalOrEmptyAfterComma)
                }
            }
            Self::Comprehension => {
                *self = Self::None;
                Some(SignatureArg::PositionalOrEmptyAfterComma)
            }
            Self::None => None,
        }
    }
}

pub enum SignatureBase<'db> {
    ExpressionPart(ExpressionPart<'db>),
    PrimaryTargetOrAtom(PrimaryTargetOrAtom<'db>),
}

#[derive(Debug, Clone)]
pub struct ErrorStmtSignaturePart<'db> {
    stmt_: PyNode<'db>,
    inner_stmt_iterator: ErrorInnerStmtSignaturePart<'db>,
}

impl<'db> ErrorStmtSignaturePart<'db> {
    fn new(stmt_: PyNode<'db>, last_node: NodeIndex) -> Self {
        let first_child = stmt_.nth_child(0);
        let inner_stmt_iterator = if first_child.is_type(ErrorNonterminal(simple_stmts)) {
            first_child.nth_child(0).nth_child(0).iter_children()
        } else {
            stmt_.iter_children()
        };

        Self {
            stmt_,
            inner_stmt_iterator: ErrorInnerStmtSignaturePart {
                inner_stmt_iterator,
                last_node,
            },
        }
    }
}

impl<'db> Iterator for ErrorStmtSignaturePart<'db> {
    type Item = SignatureArg<'db>;

    fn next(&mut self) -> Option<Self::Item> {
        for inner in &mut self.inner_stmt_iterator {
            if inner.is_type(Nonterminal(star_targets)) {
                self.inner_stmt_iterator.inner_stmt_iterator = inner.iter_children();
                return self.next();
            }
            if inner.as_code() == "," {
                if let Some(name) = inner.next_leaf()
                    && name.is_type(Terminal(TerminalType::Name))
                {
                    if let Some(next) = name.next_leaf()
                        && next.as_code() == "="
                    {
                        if let Some(after_eq) = next.next_sibling() {
                            self.inner_stmt_iterator.inner_stmt_iterator = after_eq.iter_children();
                        }
                        return Some(SignatureArg::Keyword(Name::new(name)));
                    } else {
                        return Some(SignatureArg::PositionalOrKeywordName(name.as_code()));
                    }
                }
                return Some(SignatureArg::PositionalOrEmptyAfterComma);
            }
        }
        let new = self.stmt_.next_sibling()?;
        if new.index > self.inner_stmt_iterator.last_node {
            return None;
        }
        *self = Self::new(new, self.inner_stmt_iterator.last_node);
        self.next()
    }
}

#[derive(Debug, Clone)]
pub struct ErrorInnerStmtSignaturePart<'db> {
    inner_stmt_iterator: SiblingIterator<'db>,
    last_node: NodeIndex,
}

impl<'db> Iterator for ErrorInnerStmtSignaturePart<'db> {
    type Item = PyNode<'db>;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner_stmt_iterator
            .next()
            .filter(|node| node.index <= self.last_node)
    }
}
