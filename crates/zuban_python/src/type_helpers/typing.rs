use std::borrow::Cow;

use crate::{
    arguments::{ArgKind, Args, InferredArg},
    diagnostics::IssueKind,
    format_data::FormatData,
    inference_state::InferenceState,
    inferred::Inferred,
    matching::{CouldBeALiteral, ResultContext},
    type_::{ClassGenerics, Type, TypedDictGenerics},
    utils::join_with_commas,
};

pub(crate) fn execute_cast<'db>(i_s: &InferenceState<'db, '_>, args: &dyn Args<'db>) -> Inferred {
    let mut result = None;
    let mut actual = None;
    let mut count = 0;
    let mut had_non_positional = false;
    for arg in args.iter(i_s.mode) {
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
                        .name_resolution_for_types(i_s)
                        .compute_cast_target(positional.node_ref)
                        .ok()
                } else {
                    actual = Some(positional.infer(&mut ResultContext::ExpectUnused));
                }
            }
            _ => {
                arg.infer(&mut ResultContext::ExpectUnused);
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
    if args
        .in_file()
        .is_some_and(|file| file.flags(i_s.db).warn_redundant_casts)
    {
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

pub(crate) fn execute_reveal_type<'db>(
    i_s: &InferenceState<'db, '_>,
    args: &dyn Args<'db>,
    result_context: &mut ResultContext,
) -> Inferred {
    let mut iterator = args.iter(i_s.mode);
    let Some(arg) = iterator.next() else {
        args.add_issue(
            i_s,
            IssueKind::TooFewArguments(r#" for "reveal_type""#.into()),
        );
        return Inferred::new_any_from_error();
    };
    if iterator.next().is_some() {
        args.add_issue(
            i_s,
            IssueKind::TooManyArguments(r#" for "reveal_type""#.into()),
        );
        return Inferred::new_any_from_error();
    }
    if !matches!(
        &arg.kind,
        ArgKind::Positional(_) | ArgKind::Comprehension { .. }
    ) {
        args.add_issue(
            i_s,
            IssueKind::ArgumentIssue(
                r#""reveal_type" only accepts one positional argument"#.into(),
            ),
        );
        return Inferred::new_any_from_error();
    }

    let inferred = if matches!(result_context, ResultContext::ExpectUnused) {
        // For some reason mypy wants to generate a literal here if possible.
        arg.infer(&mut ResultContext::RevealType)
    } else {
        arg.infer(result_context)
    };
    let InferredArg::Inferred(inferred) = inferred else {
        unreachable!() // Not reachable, because we only allow positional args above
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
    arg.add_issue(
        i_s,
        IssueKind::Note(format!("Revealed type is \"{s}\"").into()),
    );
    inferred
}

fn reveal_type_info(i_s: &InferenceState, t: &Type) -> Box<str> {
    let format_data = FormatData::new_reveal_type(i_s.db);
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
) -> Inferred {
    if args.iter(i_s.mode).count() != 2 {
        args.add_issue(
            i_s,
            IssueKind::ArgumentIssue(Box::from("\"assert_type\" expects 2 arguments")),
        );
        return Inferred::new_any_from_error();
    };

    let mut iterator = args.iter(i_s.mode);
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
        return error_non_positional();
    };
    let first = if matches!(result_context, ResultContext::ExpectUnused) {
        first.infer(&mut ResultContext::Unknown)
    } else {
        first.infer(result_context)
    };
    let first_type = first.as_cow_type(i_s);

    let Ok(second) = second_positional
        .node_ref
        .file
        .name_resolution_for_types(i_s)
        .compute_cast_target(second_positional.node_ref)
    else {
        return Inferred::new_any_from_error();
    };
    let second_type = second.as_cow_type(i_s);
    if first_type.as_ref() != second_type.as_ref() {
        let mut format_data = FormatData::new_short(i_s.db);
        format_data.hide_implicit_literals = false;
        let mut actual = first_type.format(&format_data);
        let mut wanted = second_type.format(&format_data);
        if actual == wanted {
            format_data.enable_verbose();
            actual = first_type.format(&format_data);
            wanted = second_type.format(&format_data);
        }
        args.add_issue(i_s, IssueKind::InvalidAssertType { actual, wanted });
    }
    first
}
