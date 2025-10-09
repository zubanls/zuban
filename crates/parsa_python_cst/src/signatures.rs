use parsa_python::{
    CodeIndex,
    NonterminalType::*,
    PyNodeType::{ErrorNonterminal, Nonterminal},
    SiblingIterator,
};

use crate::{ExpressionPart, Name, PrimaryTargetOrAtom, Scope, Tree, completion::scope_for_node};

impl Tree {
    pub fn signature_node(
        &self,
        position: CodeIndex,
    ) -> Option<(Scope<'_>, ExpressionPart<'_>, SignatureArgsIterator<'_>)> {
        let mut leaf = self.0.leaf_by_position(position);
        if leaf.start() == position {
            leaf = leaf.previous_leaf()?;
        }
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
            if check_node.is_type(Nonterminal(stmt)) || check_node.is_type(ErrorNonterminal(stmt)) {
                return None;
            }
            let mut iterator = check_node.iter_children();
            let Some(first) = iterator.next() else {
                continue;
            };
            let Some(maybe_paren) = iterator.next() else {
                continue;
            };
            if maybe_paren.as_code() != "(" {
                continue;
            }
            let base = ExpressionPart::new(first);
            if first.is_type(Nonterminal(primary)) || first.is_type(Nonterminal(t_primary)) {
                first
            } else {
                first
            };
            let Some(maybe_args) = iterator.next() else {
                return Some((scope, base, SignatureArgsIterator::None));
            };
            if maybe_args.is_type(Nonterminal(arguments))
                || maybe_args.is_type(ErrorNonterminal(arguments))
            {
                return Some((
                    scope,
                    base,
                    SignatureArgsIterator::Args(maybe_args.iter_children()),
                ));
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
    Args(SiblingIterator<'db>),
    Comprehension,
    None,
}

pub enum SignatureArg<'db> {
    PositionalOrEmptyAfterComma,
    Keyword(Name<'db>),
    StarArgs,
    StarStarKwargs,
}

impl<'db> Iterator for SignatureArgsIterator<'db> {
    type Item = SignatureArg<'db>;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Args(args) => {
                let mut arg = args.next()?;
                if arg.as_code() == "," {
                    if let Some(next) = args.next() {
                        arg = next;
                    } else {
                        return Some(SignatureArg::PositionalOrEmptyAfterComma);
                    }
                }
                if arg.is_type(Nonterminal(kwargs)) || arg.is_type(ErrorNonterminal(kwargs)) {
                    *self = Self::Args(arg.iter_children());
                    self.next()
                } else if arg.is_type(Nonterminal(kwarg)) || arg.is_type(ErrorNonterminal(kwarg)) {
                    Some(SignatureArg::Keyword(Name::new(arg.nth_child(0))))
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
