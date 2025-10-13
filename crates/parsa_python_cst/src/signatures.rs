use parsa_python::{
    CodeIndex,
    NonterminalType::*,
    PyNodeType::{ErrorNonterminal, Nonterminal},
    SiblingIterator,
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
        let mut additional_param_count = 0;
        while leaf.is_error_recovery_node() {
            if leaf.as_code() == "," {
                additional_param_count += 1;
            }
            leaf = leaf.previous_leaf()?;
        }
        let scope = scope_for_node(leaf);
        let mut check_node = leaf;
        loop {
            check_node = dbg!(check_node.parent_until(&[
                Nonterminal(stmt),
                ErrorNonterminal(stmt),
                Nonterminal(primary),
                ErrorNonterminal(primary),
                Nonterminal(t_primary),
                ErrorNonterminal(t_primary),
            ]))?;
            if check_node.is_type(Nonterminal(stmt)) {
                return None;
            } else if check_node.is_type(ErrorNonterminal(stmt)) {
                check_node = check_node.previous_leaf()?;
                if check_node.as_code() == "," {
                    additional_param_count += 1;
                }
                continue;
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
                    SignatureArgsIterator::Args {
                        args: maybe_args.iter_children(),
                        additional_param_count,
                    },
                ));
            } else {
                debug_assert!(
                    maybe_args.is_type(Nonterminal(comprehension))
                        || maybe_args.is_type(ErrorNonterminal(comprehension))
                );
                return Some((
                    scope,
                    base,
                    SignatureArgsIterator::Comprehension {
                        param_count: additional_param_count + 1,
                    },
                ));
            }
        }
    }
}

#[derive(Debug, Clone)]
pub enum SignatureArgsIterator<'db> {
    Args {
        args: SiblingIterator<'db>,
        additional_param_count: usize,
    },
    Comprehension {
        param_count: usize,
    },
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
                additional_param_count,
            } => {
                let Some(mut arg) = args.next() else {
                    if *additional_param_count > 0 {
                        *additional_param_count -= 1;
                        return Some(SignatureArg::PositionalOrEmptyAfterComma);
                    }
                    return None;
                };
                if arg.as_code() == "," {
                    if let Some(next) = args.next() {
                        arg = next;
                    } else {
                        return Some(SignatureArg::PositionalOrEmptyAfterComma);
                    }
                }
                if arg.is_type(Nonterminal(named_expression)) {
                    let expr = arg.nth_child(0);
                    if expr.is_type(Nonterminal(expression)) {
                        if let Some(AtomContent::Name(n)) =
                            Expression::new(expr).maybe_unpacked_atom()
                        {
                            return Some(SignatureArg::PositionalOrKeywordName(n.as_code()));
                        }
                    }
                }
                if arg.is_type(Nonterminal(kwargs)) || arg.is_type(ErrorNonterminal(kwargs)) {
                    *self = Self::Args {
                        args: arg.iter_children(),
                        additional_param_count: *additional_param_count,
                    };
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
            Self::Comprehension { param_count } => {
                if *param_count > 0 {
                    *param_count -= 1;
                    return Some(SignatureArg::PositionalOrEmptyAfterComma);
                }
                None
            }
            Self::None => None,
        }
    }
}

pub enum SignatureBase<'db> {
    ExpressionPart(ExpressionPart<'db>),
    PrimaryTargetOrAtom(PrimaryTargetOrAtom<'db>),
}
