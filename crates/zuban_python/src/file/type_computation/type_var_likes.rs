use std::sync::Arc;

use parsa_python_cst::NodeIndex;

use crate::{
    arguments::{ArgKind, Args, KeywordArg},
    database::{ComplexPoint, PointLink},
    debug,
    diagnostics::IssueKind,
    file::name_resolution::NameResolution,
    inference_state::InferenceState,
    inferred::Inferred,
    type_::{
        ParamSpec, TypeLikeInTypeVar, TypeVar, TypeVarKindInfos, TypeVarLike, TypeVarLikeName,
        TypeVarTuple, TypeVarVariance, Variance,
    },
};

impl<'db, 'file> NameResolution<'db, 'file, '_> {
    pub(crate) fn compute_type_var_assignment(&self, args: &dyn Args) -> Inferred {
        if let Some(t) = maybe_type_var(self.i_s, args) {
            Inferred::new_unsaved_complex(ComplexPoint::TypeVarLike(t))
        } else {
            Inferred::new_invalid_type_definition()
        }
    }

    pub(crate) fn compute_type_var_tuple_assignment(&self, args: &dyn Args) -> Inferred {
        if let Some(t) = maybe_type_var_tuple(self.i_s, args) {
            Inferred::new_unsaved_complex(ComplexPoint::TypeVarLike(t))
        } else {
            Inferred::new_invalid_type_definition()
        }
    }

    pub(crate) fn compute_param_spec_assignment(&self, args: &dyn Args) -> Inferred {
        if let Some(t) = maybe_param_spec(self.i_s, args) {
            Inferred::new_unsaved_complex(ComplexPoint::TypeVarLike(t))
        } else {
            Inferred::new_invalid_type_definition()
        }
    }
}

fn maybe_type_var(i_s: &InferenceState, args: &dyn Args) -> Option<TypeVarLike> {
    let mut iterator = args.iter(i_s.mode);
    if let Some(first_arg) = iterator.next() {
        let result = if let ArgKind::Positional(pos) = &first_arg.kind {
            pos.node_ref
                .expect_named_expression()
                .maybe_single_string_literal()
                .map(|py_string| (pos.node_ref, py_string))
        } else {
            debug!("TODO this should probably add an error");
            None
        };
        let (name_node, py_string) = match result {
            Some(result) => result,
            None => {
                first_arg.add_issue(
                    i_s,
                    IssueKind::TypeVarLikeFirstArgMustBeString {
                        class_name: "TypeVar",
                    },
                );
                return None;
            }
        };
        let Some(name_def) = py_string.in_simple_assignment() else {
            first_arg.add_issue(
                i_s,
                IssueKind::InvalidAssignmentForm {
                    class_name: "TypeVar",
                },
            );
            return None;
        };
        if name_def.as_code() != py_string.content() {
            name_node.add_issue(
                i_s,
                IssueKind::VarNameMismatch {
                    class_name: "TypeVar".into(),
                    string_name: Box::from(py_string.content()),
                    variable_name: Box::from(name_def.as_code()),
                },
            );
        }

        let mut constraints = vec![];
        let mut bound = None;
        let mut keys = CommonKeywordHandler::new("TypeVar");
        for arg in iterator {
            match arg.kind {
                ArgKind::Positional(pos) => {
                    let expr_index = pos.node_ref.expect_named_expression().expression().index();
                    constraints.push(TypeLikeInTypeVar::new_lazy(expr_index));
                }
                ArgKind::Keyword(KeywordArg {
                    key,
                    node_ref,
                    expression,
                    ..
                }) if key == "bound" => {
                    if !constraints.is_empty() {
                        node_ref.add_issue(i_s, IssueKind::TypeVarValuesAndUpperBound);
                        return None;
                    }
                    bound = Some(expression.index());
                }
                ArgKind::Keyword(kw_arg) => keys.handle_key(i_s, kw_arg)?,
                ArgKind::Comprehension { .. } => {
                    arg.add_issue(i_s, IssueKind::UnexpectedComprehension);
                    return None;
                }
                _ => {
                    arg.add_issue(i_s, IssueKind::UnexpectedArgumentTo { name: "TypeVar" });
                }
            }
        }
        if constraints.len() == 1 {
            args.add_issue(i_s, IssueKind::TypeVarValuesNeedsAtLeastTwo);
            return None;
        }
        let kind = if let Some(bound) = bound {
            debug_assert!(constraints.is_empty());
            TypeVarKindInfos::Bound(TypeLikeInTypeVar::new_lazy(bound))
        } else if !constraints.is_empty() {
            TypeVarKindInfos::Constraints(constraints.into())
        } else {
            TypeVarKindInfos::Unrestricted
        };
        Some(TypeVarLike::TypeVar(Arc::new(TypeVar::new(
            TypeVarLikeName::InString {
                name_node: PointLink {
                    file: name_node.file_index(),
                    node_index: name_def.name_index(),
                },
                string_node: PointLink {
                    file: name_node.file_index(),
                    node_index: py_string.index(),
                },
            },
            i_s.as_parent_scope(),
            kind,
            keys.default,
            keys.variance(i_s, args)?,
        ))))
    } else {
        args.add_issue(
            i_s,
            IssueKind::TypeVarLikeTooFewArguments {
                class_name: "TypeVar",
            },
        );
        None
    }
}

struct CommonKeywordHandler {
    kind: &'static str,
    covariant: bool,
    contravariant: bool,
    infer_variance: bool,
    default: Option<NodeIndex>,
}

impl CommonKeywordHandler {
    fn new(kind: &'static str) -> Self {
        Self {
            kind,
            covariant: false,
            contravariant: false,
            infer_variance: false,
            default: None,
        }
    }

    fn handle_key(&mut self, i_s: &InferenceState, kw_arg: KeywordArg) -> Option<()> {
        let as_bool = |for_argument| {
            let code = kw_arg.expression.as_code();
            match code {
                "True" => Some(true),
                "False" => Some(false),
                _ => {
                    kw_arg.node_ref.add_issue(
                        i_s,
                        IssueKind::TypeVarLikeVarianceMustBeBool {
                            kind: self.kind,
                            argument: for_argument,
                        },
                    );
                    None
                }
            }
        };

        let key = kw_arg.key;
        match key {
            "covariant" => self.covariant = as_bool("covariant")?,
            "contravariant" => self.contravariant = as_bool("contravariant")?,
            "infer_variance" => self.infer_variance = as_bool("infer_variance")?,
            "default" => self.default = Some(kw_arg.expression.index()),
            _ => match self.kind {
                "TypeVar" => {
                    kw_arg.node_ref.add_issue(
                        i_s,
                        IssueKind::UnexpectedArgument {
                            class_name: "TypeVar",
                            argument_name: Box::from(key),
                        },
                    );
                    return None;
                }
                "TypeVarTuple" => {
                    kw_arg.node_ref.add_issue(
                        i_s,
                        IssueKind::ArgumentIssue(
                            format!(r#"Unexpected keyword argument "{key}" for "TypeVarTuple""#)
                                .into(),
                        ),
                    );
                }
                "ParamSpec" => {
                    kw_arg
                        .node_ref
                        .add_issue(i_s, IssueKind::UnexpectedArgumentTo { name: "ParamSpec" });
                }
                _ => unreachable!(),
            },
        }
        Some(())
    }

    fn variance(&self, i_s: &InferenceState, args: &dyn Args) -> Option<TypeVarVariance> {
        Some(if self.infer_variance {
            if self.covariant {
                args.add_issue(
                    i_s,
                    IssueKind::TypeVarInferVarianceCannotSpecifyVariance {
                        specified: "covariant",
                    },
                );
            }
            if self.contravariant {
                args.add_issue(
                    i_s,
                    IssueKind::TypeVarInferVarianceCannotSpecifyVariance {
                        specified: "contravariant",
                    },
                );
            }
            TypeVarVariance::Inferred
        } else {
            TypeVarVariance::Known(match (self.covariant, self.contravariant) {
                (false, false) => Variance::Invariant,
                (true, false) => Variance::Covariant,
                (false, true) => Variance::Contravariant,
                (true, true) => {
                    args.add_issue(
                        i_s,
                        IssueKind::TypeVarLikeCoAndContravariant { kind: self.kind },
                    );
                    return None;
                }
            })
        })
    }
}

fn maybe_type_var_tuple(i_s: &InferenceState, args: &dyn Args) -> Option<TypeVarLike> {
    let mut iterator = args.iter(i_s.mode);
    if let Some(first_arg) = iterator.next() {
        let result = if let ArgKind::Positional(pos) = &first_arg.kind {
            pos.node_ref
                .expect_named_expression()
                .maybe_single_string_literal()
                .map(|py_string| (pos.node_ref, py_string))
        } else {
            debug!("TODO type var tuple why does this not need an error?");
            None
        };
        let (name_node, py_string) = match result {
            Some(result) => result,
            None => {
                first_arg.add_issue(
                    i_s,
                    IssueKind::TypeVarLikeFirstArgMustBeString {
                        class_name: "TypeVarTuple",
                    },
                );
                return None;
            }
        };
        let Some(name_def) = py_string.in_simple_assignment() else {
            first_arg.add_issue(
                i_s,
                IssueKind::InvalidAssignmentForm {
                    class_name: "TypeVarTuple",
                },
            );
            return None;
        };
        if name_def.as_code() != py_string.content() {
            name_node.add_issue(
                i_s,
                IssueKind::VarNameMismatch {
                    class_name: "TypeVarTuple".into(),
                    string_name: Box::from(py_string.content()),
                    variable_name: Box::from(name_def.as_code()),
                },
            );
        }

        let mut keys = CommonKeywordHandler::new("TypeVarTuple");
        for arg in iterator {
            match arg.kind {
                ArgKind::Positional(_) => {
                    arg.add_issue(
                        i_s,
                        IssueKind::ArgumentIssue(
                            "Too many positional arguments for \"TypeVarTuple\"".into(),
                        ),
                    );
                    break;
                }
                ArgKind::Keyword(kw_arg) => keys.handle_key(i_s, kw_arg)?,
                ArgKind::Comprehension { .. } => {
                    arg.add_issue(i_s, IssueKind::UnexpectedComprehension);
                    return None;
                }
                _ => {
                    arg.add_issue(
                        i_s,
                        IssueKind::UnexpectedArgumentTo {
                            name: "TypeVarTuple",
                        },
                    );
                }
            }
        }
        Some(TypeVarLike::TypeVarTuple(Arc::new(TypeVarTuple::new(
            TypeVarLikeName::InString {
                name_node: PointLink {
                    file: name_node.file_index(),
                    node_index: name_def.name_index(),
                },
                string_node: PointLink {
                    file: name_node.file_index(),
                    node_index: py_string.index(),
                },
            },
            i_s.as_parent_scope(),
            keys.default,
            keys.variance(i_s, args)?,
        ))))
    } else {
        args.add_issue(
            i_s,
            IssueKind::TypeVarLikeTooFewArguments {
                class_name: "TypeVarTuple",
            },
        );
        None
    }
}

fn maybe_param_spec(i_s: &InferenceState, args: &dyn Args) -> Option<TypeVarLike> {
    let mut iterator = args.iter(i_s.mode);
    if let Some(first_arg) = iterator.next() {
        let result = if let ArgKind::Positional(pos) = &first_arg.kind {
            pos.node_ref
                .expect_named_expression()
                .maybe_single_string_literal()
                .map(|py_string| (pos.node_ref, py_string))
        } else {
            debug!("TODO param spec why does this not need an error?");
            None
        };
        let (name_node, py_string) = match result {
            Some(result) => result,
            None => {
                first_arg.add_issue(
                    i_s,
                    IssueKind::TypeVarLikeFirstArgMustBeString {
                        class_name: "ParamSpec",
                    },
                );
                return None;
            }
        };
        let Some(name_def) = py_string.in_simple_assignment() else {
            first_arg.add_issue(
                i_s,
                IssueKind::InvalidAssignmentForm {
                    class_name: "ParamSpec",
                },
            );
            return None;
        };
        if name_def.as_code() != py_string.content() {
            name_node.add_issue(
                i_s,
                IssueKind::VarNameMismatch {
                    class_name: "ParamSpec".into(),
                    string_name: Box::from(py_string.content()),
                    variable_name: Box::from(name_def.as_code()),
                },
            );
        }

        let mut keys = CommonKeywordHandler::new("ParamSpec");
        for arg in iterator {
            match arg.kind {
                ArgKind::Positional { .. } => {
                    arg.add_issue(
                        i_s,
                        IssueKind::ArgumentIssue(
                            "Too many positional arguments for \"ParamSpec\"".into(),
                        ),
                    );
                    break;
                }
                ArgKind::Keyword(KeywordArg { key: "bound", .. }) => {
                    arg.add_issue(
                        i_s,
                        IssueKind::ParamSpecKeywordArgumentWithoutDefinedSemantics,
                    );
                }
                ArgKind::Keyword(kw_arg) => keys.handle_key(i_s, kw_arg)?,
                _ => {
                    arg.add_issue(i_s, IssueKind::UnexpectedArgumentTo { name: "ParamSpec" });
                }
            }
        }
        let mut variance = keys.variance(i_s, args)?;
        if let TypeVarVariance::Known(variance) = &mut variance {
            // Variance is used in an inverted way for ParamSpec, because Zuban treats param
            // signatures in a covariant way and only inverts variance once param types are
            // matched. This could be changed, but it shouldn't matter too much so we keep this
            // historical artifact.
            *variance = variance.invert();
        }
        Some(TypeVarLike::ParamSpec(Arc::new(ParamSpec::new(
            TypeVarLikeName::InString {
                name_node: PointLink {
                    file: name_node.file_index(),
                    node_index: name_def.name_index(),
                },
                string_node: PointLink {
                    file: name_node.file_index(),
                    node_index: py_string.index(),
                },
            },
            i_s.as_parent_scope(),
            keys.default,
            variance,
        ))))
    } else {
        args.add_issue(
            i_s,
            IssueKind::TypeVarLikeTooFewArguments {
                class_name: "ParamSpec",
            },
        );
        None
    }
}
