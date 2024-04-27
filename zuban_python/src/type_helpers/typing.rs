use std::{borrow::Cow, rc::Rc};

use crate::{
    arguments::{ArgKind, Args, InferredArg, KeywordArg},
    database::{ComplexPoint, PointLink},
    debug,
    diagnostics::IssueKind,
    inference_state::InferenceState,
    inferred::Inferred,
    matching::{CouldBeALiteral, FormatData, OnTypeError, ResultContext},
    node_ref::NodeRef,
    type_::{
        ClassGenerics, FormatStyle, NewType, ParamSpec, Type, TypeVar, TypeVarKind, TypeVarLike,
        TypeVarName, TypeVarTuple, TypedDictGenerics, Variance,
    },
    utils::join_with_commas,
};

pub(crate) fn execute_type<'db>(
    i_s: &InferenceState<'db, '_>,
    args: &dyn Args<'db>,
    on_type_error: OnTypeError,
) -> Inferred {
    let mut iterator = args.iter();
    let first = iterator.next();
    if let Some(x) = iterator.next() {
        todo!()
    } else if let Some(first) = first {
        let InferredArg::Inferred(inf) = first.infer(i_s, &mut ResultContext::Unknown) else {
            todo!()
        };
        Inferred::from_type(Type::Type(Rc::new(inf.as_type(i_s))))
    } else {
        todo!()
    }
}

#[derive(Debug)]
pub struct TypingCast();

impl<'db> TypingCast {
    pub(crate) fn execute(
        &self,
        i_s: &InferenceState<'db, '_>,
        args: &dyn Args<'db>,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError,
    ) -> Inferred {
        let mut result = None;
        let mut actual = None;
        let mut count = 0;
        let mut had_non_positional = false;
        for arg in args.iter() {
            // TODO something like *Iterable[str] looped forever and then we put in this hack
            if arg.in_args_or_kwargs_and_arbitrary_len() {
                count = 2;
                had_non_positional = true;
                break;
            }
            match arg.kind {
                ArgKind::Positional(positional) => {
                    if positional.position == 1 {
                        result = positional
                            .node_ref
                            .file
                            .inference(i_s)
                            .compute_cast_target(positional.node_ref)
                            .ok()
                    } else {
                        actual = Some(positional.infer(i_s, &mut ResultContext::ExpectUnused));
                    }
                }
                _ => {
                    arg.infer(i_s, &mut ResultContext::ExpectUnused);
                    had_non_positional = true;
                }
            }
            count += 1;
        }
        if count != 2 {
            args.add_issue(
                i_s,
                IssueKind::ArgumentIssue(Box::from("\"cast\" expects 2 arguments")),
            );
            return Inferred::new_any_from_error();
        } else if had_non_positional {
            args.add_issue(
                i_s,
                IssueKind::ArgumentIssue(Box::from(
                    "\"cast\" must be called with 2 positional arguments",
                )),
            );
        }
        let result = result.unwrap_or_else(Inferred::new_any_from_error);
        if i_s.db.project.flags.warn_redundant_casts {
            if let Some(actual) = actual {
                let t_in = actual.as_cow_type(i_s);
                let t_out = result.as_type(i_s);
                if t_in.is_simple_same_type(i_s, &t_out).non_any_match() && !(t_in.is_any()) {
                    args.add_issue(
                        i_s,
                        IssueKind::RedundantCast {
                            to: result.format_short(i_s),
                        },
                    );
                }
            }
        }
        result
    }
}

#[derive(Debug)]
pub struct RevealTypeFunction();

impl RevealTypeFunction {
    pub(crate) fn execute<'db>(
        &self,
        i_s: &InferenceState<'db, '_>,
        args: &dyn Args<'db>,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError,
    ) -> Inferred {
        let mut iterator = args.iter();
        let arg = iterator.next().unwrap_or_else(|| todo!());
        let ArgKind::Positional(pos) = arg.kind else {
            todo!()
        };

        let inferred = if matches!(result_context, ResultContext::ExpectUnused) {
            // For some reason mypy wants to generate a literal here if possible.
            pos.infer(i_s, &mut ResultContext::RevealType)
        } else {
            pos.infer(i_s, result_context)
        };
        let t = inferred.as_cow_type(i_s);
        let s = reveal_type_info(
            i_s,
            match result_context.could_be_a_literal(i_s) {
                CouldBeALiteral::Yes { implicit: false } => match t.as_ref() {
                    Type::Literal(l) => {
                        let mut l = l.clone();
                        l.implicit = false;
                        Cow::Owned(Type::Literal(l))
                    }
                    _ => t,
                },
                _ => t,
            }
            .as_ref(),
        );
        pos.add_issue(
            i_s,
            IssueKind::Note(format!("Revealed type is \"{s}\"").into()),
        );
        if iterator.next().is_some() {
            todo!()
        }
        inferred
    }
}

fn reveal_type_info(i_s: &InferenceState, t: &Type) -> Box<str> {
    let format_data = FormatData::with_style(i_s.db, FormatStyle::MypyRevealType);
    if let Type::Type(type_) = t {
        match type_.as_ref() {
            Type::Class(c) if c.generics != ClassGenerics::NotDefinedYet => (),
            Type::TypedDict(td) => {
                let tvs = match &td.generics {
                    TypedDictGenerics::NotDefinedYet(tvs) => Some(tvs.format(&format_data)),
                    _ => None,
                };
                return format!(
                    "def {}(*, {}) -> {}",
                    tvs.as_deref().unwrap_or(""),
                    join_with_commas(td.members(i_s.db).iter().map(|member| {
                        let mut s = format!(
                            "{}: {}",
                            member.name.as_str(i_s.db),
                            member.type_.format(&format_data)
                        );
                        if !member.required {
                            s += " = ...";
                        }
                        s
                    })),
                    type_.format(&format_data)
                )
                .into();
            }
            _ => {
                if let Some(callable) = t.maybe_callable(i_s) {
                    return callable.format(&format_data).into();
                }
            }
        }
    }
    t.format(&format_data)
}

pub(crate) fn execute_assert_type<'db>(
    i_s: &InferenceState<'db, '_>,
    args: &dyn Args<'db>,
    result_context: &mut ResultContext,
    on_type_error: OnTypeError,
) -> Inferred {
    if args.iter().count() != 2 {
        args.add_issue(
            i_s,
            IssueKind::ArgumentIssue(Box::from("\"assert_type\" expects 2 arguments")),
        );
        return Inferred::new_any_from_error();
    };

    let mut iterator = args.iter();
    let first = iterator.next().unwrap();
    let second = iterator.next().unwrap();

    let error_non_positional = || {
        args.add_issue(
            i_s,
            IssueKind::ArgumentIssue(Box::from(
                "\"assert_type\" must be called with 2 positional arguments",
            )),
        );
        Inferred::new_any_from_error()
    };
    let ArgKind::Positional(first) = first.kind else {
        return error_non_positional();
    };
    let ArgKind::Positional(second_positional) = second.kind else {
        return error_non_positional()
    };
    let first = if matches!(result_context, ResultContext::ExpectUnused) {
        first.infer(i_s, &mut ResultContext::Unknown)
    } else {
        first.infer(i_s, result_context)
    };
    let first_type = first.as_cow_type(i_s);

    let Ok(second) = second_positional.node_ref
        .file
        .inference(i_s)
        .compute_cast_target(second_positional.node_ref) else {
        return Inferred::new_any_from_error()
    };
    let second_type = second.as_cow_type(i_s);
    if first_type.as_ref() != second_type.as_ref() {
        let mut format_data = FormatData::new_short(i_s.db);
        format_data.hide_implicit_literals = false;
        let mut actual = first_type.format(&format_data);
        let mut wanted = second_type.format(&format_data);
        if actual == wanted {
            format_data.verbose = true;
            actual = first_type.format(&format_data);
            wanted = second_type.format(&format_data);
        }
        args.add_issue(i_s, IssueKind::InvalidAssertType { actual, wanted });
    }
    first
}

#[derive(Debug)]
pub struct TypeVarClass();

impl TypeVarClass {
    pub(crate) fn execute(
        &self,
        i_s: &InferenceState,
        args: &dyn Args,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError,
    ) -> Inferred {
        if let Some(t) = maybe_type_var(i_s, args, result_context) {
            Inferred::new_unsaved_complex(ComplexPoint::TypeVarLike(t))
        } else {
            Inferred::new_any_from_error()
        }
    }
}

fn maybe_type_var(
    i_s: &InferenceState,
    args: &dyn Args,
    result_context: &ResultContext,
) -> Option<TypeVarLike> {
    if !matches!(result_context, ResultContext::AssignmentNewDefinition) {
        args.add_issue(i_s, IssueKind::UnexpectedTypeForTypeVar);
        return None;
    }
    let mut iterator = args.iter();
    if let Some(first_arg) = iterator.next() {
        let result = if let ArgKind::Positional(pos) = &first_arg.kind {
            pos.node_ref
                .as_named_expression()
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
        if let Some(name) = py_string.in_simple_assignment() {
            if name.as_code() != py_string.content() {
                name_node.add_issue(
                    i_s,
                    IssueKind::TypeVarNameMismatch {
                        class_name: "TypeVar",
                        string_name: Box::from(py_string.content()),
                        variable_name: Box::from(name.as_code()),
                    },
                );
            }
        } else {
            todo!()
        }

        let mut constraints = vec![];
        let mut bound = None;
        let mut default = None;
        let mut covariant = false;
        let mut contravariant = false;
        for arg in iterator {
            match arg.kind {
                ArgKind::Positional(pos) => {
                    let mut inference = pos.node_ref.file.inference(i_s);
                    if let Some(t) = inference.compute_type_var_constraint(
                        pos.node_ref.as_named_expression().expression(),
                    ) {
                        constraints.push(t);
                    } else {
                        //
                        debug!("TODO invalid type var constraint, this needs a lint?");
                        return None;
                    }
                }
                ArgKind::Keyword(KeywordArg {
                    key,
                    node_ref,
                    expression,
                    ..
                }) => match key {
                    "covariant" => {
                        let code = expression.as_code();
                        match code {
                            "True" => covariant = true,
                            "False" => (),
                            _ => {
                                node_ref.add_issue(
                                    i_s,
                                    IssueKind::TypeVarVarianceMustBeBool {
                                        argument: "covariant",
                                    },
                                );
                                return None;
                            }
                        }
                    }
                    "contravariant" => {
                        let code = expression.as_code();
                        match code {
                            "True" => contravariant = true,
                            "False" => (),
                            _ => {
                                node_ref.add_issue(
                                    i_s,
                                    IssueKind::TypeVarVarianceMustBeBool {
                                        argument: "contravariant",
                                    },
                                );
                                return None;
                            }
                        }
                    }
                    "bound" => {
                        if !constraints.is_empty() {
                            node_ref.add_issue(i_s, IssueKind::TypeVarValuesAndUpperBound);
                            return None;
                        }
                        if let Some(t) = node_ref
                            .file
                            .inference(i_s)
                            .compute_type_var_constraint(expression)
                        {
                            bound = Some(t)
                        } else {
                            debug!("TODO invalid type var bound, this needs a lint?");
                            return None;
                        }
                    }
                    "default" => {
                        if let Some(t) = node_ref
                            .file
                            .inference(i_s)
                            .compute_type_var_constraint(expression)
                        {
                            default = Some(t)
                        } else {
                            todo!()
                        }
                    }
                    _ => {
                        node_ref.add_issue(
                            i_s,
                            IssueKind::UnexpectedArgument {
                                class_name: "TypeVar",
                                argument_name: Box::from(key),
                            },
                        );
                        return None;
                    }
                },
                ArgKind::Comprehension { .. } => {
                    arg.add_issue(i_s, IssueKind::UnexpectedComprehension);
                    return None;
                }
                _ => arg.add_issue(i_s, IssueKind::UnexpectedArgumentTo { name: "TypeVar" }),
            }
        }
        if constraints.len() == 1 {
            args.add_issue(i_s, IssueKind::TypeVarOnlySingleRestriction);
            return None;
        }
        let kind = if let Some(bound) = bound {
            debug_assert!(constraints.is_empty());
            TypeVarKind::Bound(bound)
        } else if !constraints.is_empty() {
            TypeVarKind::Constraints(constraints.into())
        } else {
            TypeVarKind::Unrestricted
        };
        Some(TypeVarLike::TypeVar(Rc::new(TypeVar {
            name_string: TypeVarName::PointLink(PointLink {
                file: name_node.file_index(),
                node_index: py_string.index(),
            }),
            kind,
            default,
            variance: match (covariant, contravariant) {
                (false, false) => Variance::Invariant,
                (true, false) => Variance::Covariant,
                (false, true) => Variance::Contravariant,
                (true, true) => {
                    args.add_issue(i_s, IssueKind::TypeVarCoAndContravariant);
                    return None;
                }
            },
        })))
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

#[derive(Debug)]
pub struct TypeVarTupleClass();

impl TypeVarTupleClass {
    pub(crate) fn execute(
        &self,
        i_s: &InferenceState,
        args: &dyn Args,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError,
    ) -> Inferred {
        if let Some(t) = maybe_type_var_tuple(i_s, args, result_context) {
            Inferred::new_unsaved_complex(ComplexPoint::TypeVarLike(t))
        } else {
            Inferred::new_any_from_error()
        }
    }
}

fn maybe_type_var_tuple(
    i_s: &InferenceState,
    args: &dyn Args,
    result_context: &ResultContext,
) -> Option<TypeVarLike> {
    if !matches!(result_context, ResultContext::AssignmentNewDefinition) {
        args.add_issue(i_s, IssueKind::UnexpectedTypeForTypeVar);
        return None;
    }
    let mut iterator = args.iter();
    if let Some(first_arg) = iterator.next() {
        let result = if let ArgKind::Positional(pos) = &first_arg.kind {
            pos.node_ref
                .as_named_expression()
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
        if let Some(name) = py_string.in_simple_assignment() {
            if name.as_code() != py_string.content() {
                name_node.add_issue(
                    i_s,
                    IssueKind::TypeVarNameMismatch {
                        class_name: "TypeVarTuple",
                        string_name: Box::from(py_string.content()),
                        variable_name: Box::from(name.as_code()),
                    },
                );
            }
        } else {
            todo!()
        }

        let mut default = None;
        for arg in iterator {
            match arg.kind {
                ArgKind::Positional(_) => {
                    arg.add_issue(
                        i_s,
                        IssueKind::ArgumentIssue(
                            "Too many positional arguments for \"TypeVarTuple\"".into(),
                        ),
                    );
                    return None;
                }
                ArgKind::Keyword(KeywordArg {
                    key,
                    node_ref,
                    expression,
                    ..
                }) => match key {
                    "default" => {
                        if let Some(type_args) = node_ref
                            .file
                            .inference(i_s)
                            .compute_type_var_tuple_default(expression)
                        {
                            default = Some(type_args);
                        } else {
                            todo!()
                        }
                    }
                    _ => {
                        node_ref.add_issue(
                            i_s,
                            IssueKind::ArgumentIssue(
                                format!(
                                    r#"Unexpected keyword argument "{key}" for "TypeVarTuple""#
                                )
                                .into(),
                            ),
                        );
                        return None;
                    }
                },
                ArgKind::Comprehension { .. } => {
                    arg.add_issue(i_s, IssueKind::UnexpectedComprehension);
                    return None;
                }
                _ => todo!(),
            }
        }
        Some(TypeVarLike::TypeVarTuple(Rc::new(TypeVarTuple {
            name_string: PointLink {
                file: name_node.file_index(),
                node_index: py_string.index(),
            },
            default,
        })))
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

#[derive(Debug)]
pub struct ParamSpecClass();

impl ParamSpecClass {
    pub(crate) fn execute(
        &self,
        i_s: &InferenceState,
        args: &dyn Args,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError,
    ) -> Inferred {
        if let Some(t) = maybe_param_spec(i_s, args, result_context) {
            Inferred::new_unsaved_complex(ComplexPoint::TypeVarLike(t))
        } else {
            Inferred::new_any_from_error()
        }
    }
}

fn maybe_param_spec(
    i_s: &InferenceState,
    args: &dyn Args,
    result_context: &ResultContext,
) -> Option<TypeVarLike> {
    if !matches!(result_context, ResultContext::AssignmentNewDefinition) {
        args.add_issue(i_s, IssueKind::UnexpectedTypeForTypeVar);
        return None;
    }
    let mut iterator = args.iter();
    if let Some(first_arg) = iterator.next() {
        let result = if let ArgKind::Positional(pos) = &first_arg.kind {
            pos.node_ref
                .as_named_expression()
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
        if let Some(name) = py_string.in_simple_assignment() {
            if name.as_code() != py_string.content() {
                name_node.add_issue(
                    i_s,
                    IssueKind::TypeVarNameMismatch {
                        class_name: "ParamSpec",
                        string_name: Box::from(py_string.content()),
                        variable_name: Box::from(name.as_code()),
                    },
                );
            }
        } else {
            todo!()
        }

        let mut default = None;
        for arg in iterator {
            match arg.kind {
                ArgKind::Keyword(KeywordArg {
                    key,
                    node_ref,
                    expression,
                    ..
                }) if key == "default" => {
                    if let Some(c) = node_ref
                        .file
                        .inference(i_s)
                        .compute_param_spec_default(expression)
                    {
                        default = Some(c)
                    } else {
                        todo!()
                    }
                }
                ArgKind::Inferred { .. }
                | ArgKind::SlicesTuple { .. }
                | ArgKind::ParamSpec { .. } => unreachable!(),
                ArgKind::Positional { .. } => {
                    arg.add_issue(
                        i_s,
                        IssueKind::ArgumentIssue(
                            "Too many positional arguments for \"ParamSpec\"".into(),
                        ),
                    );
                    return None;
                }
                _ => {
                    arg.add_issue(i_s, IssueKind::ParamSpecTooManyKeywordArguments);
                    return None;
                }
            }
        }
        Some(TypeVarLike::ParamSpec(Rc::new(ParamSpec {
            name_string: PointLink {
                file: name_node.file_index(),
                node_index: py_string.index(),
            },
            default,
        })))
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

#[derive(Debug)]
pub struct NewTypeClass();

impl NewTypeClass {
    pub(crate) fn execute<'db>(
        &self,
        i_s: &InferenceState<'db, '_>,
        args: &dyn Args<'db>,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError,
    ) -> Inferred {
        if let Some(n) = maybe_new_type(i_s, args) {
            Inferred::new_unsaved_complex(ComplexPoint::NewTypeDefinition(Rc::new(n)))
        } else {
            Inferred::new_any_from_error()
        }
    }
}

fn maybe_new_type<'db>(i_s: &InferenceState<'db, '_>, args: &dyn Args<'db>) -> Option<NewType> {
    let Some((first, second)) = args.maybe_two_positional_args(i_s.db) else {
        args.add_issue(
            i_s,
            IssueKind::ArgumentIssue(Box::from(
                    "NewType(...) expects exactly two positional arguments")),
        );
        return None
    };
    let result = first
        .as_named_expression()
        .maybe_single_string_literal()
        .map(|py_string| (first, py_string));
    let (name_node, py_string) = match result {
        Some(result) => result,
        None => {
            first.add_issue(
                i_s,
                IssueKind::ArgumentIssue(Box::from(
                    "Argument 1 to NewType(...) must be a string literal",
                )),
            );
            return None;
        }
    };
    if let Some(name) = py_string.in_simple_assignment() {
        if name.as_code() != py_string.content() {
            name_node.add_issue(
                i_s,
                IssueKind::TypeVarNameMismatch {
                    class_name: "NewType",
                    string_name: Box::from(py_string.content()),
                    variable_name: Box::from(name.as_code()),
                },
            );
        }
    } else {
        todo!()
    }
    let type_node_ref = NodeRef::new(
        second.file,
        second.as_named_expression().expression().index(),
    );
    Some(NewType::new(
        PointLink {
            file: name_node.file_index(),
            node_index: py_string.index(),
        },
        type_node_ref.as_link(),
    ))
}
