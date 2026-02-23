use std::borrow::Cow;

use crate::{
    arguments::{ArgKind, Args, InferredArg},
    database::Database,
    diagnostics::IssueKind,
    format_data::FormatData,
    inference_state::InferenceState,
    inferred::Inferred,
    matching::{CheckedTypeRecursion, Generic, Generics},
    result_context::{CouldBeALiteral, ResultContext},
    type_::{
        CallableParams, ClassGenerics, GenericClass, ParamType, ReplaceTypeVarLikes as _,
        StarParamType, StarStarParamType, TupleArgs, Type, TypedDict, TypedDictGenerics,
    },
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
                    actual = Some(positional.infer(&mut ResultContext::Unknown));
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
        && let Some(actual) = actual
    {
        let t_in = actual.as_cow_type(i_s);
        let t_out = result.as_cow_type(i_s);
        if t_in.is_equal_type(i_s.db, &t_out) && !(t_in.is_any()) {
            args.add_issue(
                i_s,
                IssueKind::RedundantCast {
                    to: result.format_short(i_s),
                },
            );
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
                let m = td.members(i_s.db);
                return format!(
                    "def {}(*, {}) -> {}",
                    tvs.as_deref().unwrap_or(""),
                    join_with_commas(
                        m.named
                            .iter()
                            .map(|member| {
                                let mut s = format!(
                                    "{}: {}",
                                    member.name.as_str(i_s.db),
                                    member.type_.format(&format_data)
                                );
                                if !member.required {
                                    s += " = ...";
                                }
                                s
                            })
                            .chain(
                                m.extra_items
                                    .as_ref()
                                    .map(|e| { e.format_as_param(&format_data) })
                                    .into_iter()
                            )
                    ),
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
        first.infer(&mut ResultContext::RevealType)
    } else {
        first.infer(result_context)
    };
    let mut first_type = first.as_cow_type(i_s);

    // The untyped TypeVars are not really assertable and are internal types mostly for type
    // inference. Type assertion should simply report Any.
    if let Some(new) = first_type.replace_type_var_likes(i_s.db, &mut |usage| {
        usage
            .as_type_var_like()
            .is_untyped()
            .then(|| usage.as_any_generic_item())
    }) {
        first_type = Cow::Owned(new)
    }

    let Ok(second) = second_positional
        .node_ref
        .file
        .name_resolution_for_types(i_s)
        .compute_cast_target(second_positional.node_ref)
    else {
        return Inferred::new_any_from_error();
    };
    let second_type = second.as_cow_type(i_s);
    if !first_type.is_equal_type(i_s.db, &second_type) {
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

impl Type {
    pub fn is_equal_type(&self, db: &Database, other: &Type) -> bool {
        self.is_equal_type_internal(db, None, other, true, false)
    }

    pub fn is_equal_type_where_any_matches_all(&self, db: &Database, other: &Type) -> bool {
        self.is_equal_type_internal(db, None, other, true, true)
    }

    pub fn is_equal_type_without_unpacking_recursive_types(
        &self,
        db: &Database,
        other: &Type,
    ) -> bool {
        self.is_equal_type_internal(db, None, other, false, false)
    }

    pub fn is_equal_type_internal(
        &self,
        db: &Database,
        checking_type_recursion: Option<CheckedTypeRecursion>,
        other: &Type,
        unpack_recursive_type: bool,
        any_is_all: bool,
    ) -> bool {
        let eq = |t1: &Type, t2: &Type| {
            t1.is_equal_type_internal(
                db,
                checking_type_recursion,
                t2,
                unpack_recursive_type,
                any_is_all,
            )
        };
        let all_eq =
            |ts1: &[Type], ts2: &[Type]| ts1.iter().zip(ts2.iter()).all(|(t1, t2)| eq(t1, t2));
        let typed_dict_eq = |td1: &TypedDict, td2: &TypedDict| {
            let m1 = td1.members(db);
            let m2 = td2.members(db);
            m1.named.len() == m2.named.len()
                && m1.named.iter().zip(m2.named.iter()).all(|(m1, m2)| {
                    m1.name.as_str(db) == m2.name.as_str(db)
                        && m1.required == m2.required
                        && m1.read_only == m2.read_only
                        && eq(&m1.type_, &m2.type_)
                })
                && match (&m1.extra_items, &m2.extra_items) {
                    (None, None) => true,
                    (Some(t1), Some(t2)) => {
                        t1.t.is_equal_type_internal(
                            db,
                            checking_type_recursion,
                            &t2.t,
                            unpack_recursive_type,
                            any_is_all,
                        ) && t1.read_only == t2.read_only
                    }
                    _ => false,
                }
        };
        let tuple_args_eq = |t1: &TupleArgs, t2: &TupleArgs| match (t1, t2) {
            (TupleArgs::WithUnpack(w1), TupleArgs::WithUnpack(w2)) => {
                all_eq(&w1.before, &w2.before) && all_eq(&w1.after, &w2.after)
            }
            (TupleArgs::FixedLen(ts1), TupleArgs::FixedLen(ts2)) => all_eq(ts1, ts2),
            (TupleArgs::ArbitraryLen(t1), TupleArgs::ArbitraryLen(t2)) => eq(t1, t2),
            _ => false,
        };
        let params_eq = |p1: &CallableParams, p2: &CallableParams| match (p1, p2) {
            (CallableParams::Simple(ps1), CallableParams::Simple(ps2)) => {
                ps1.iter().zip(ps2.iter()).all(|(p1, p2)| {
                    p1.has_default == p2.has_default
                        && match (&p1.type_, &p2.type_) {
                            (ParamType::PositionalOnly(t1), ParamType::PositionalOnly(t2)) => {
                                eq(t1, t2)
                            }
                            (
                                ParamType::PositionalOrKeyword(t1),
                                ParamType::PositionalOrKeyword(t2),
                            )
                            | (ParamType::KeywordOnly(t1), ParamType::KeywordOnly(t2)) => {
                                eq(t1, t2)
                                    && match (p1.name.as_ref(), p2.name.as_ref()) {
                                        (Some(n1), Some(n2)) => n1.as_str(db) == n2.as_str(db),
                                        // Should these cases even happen?
                                        (None, None) => true,
                                        (_, _) => false,
                                    }
                            }
                            (ParamType::Star(pt1), ParamType::Star(pt2)) => match (pt1, pt2) {
                                (
                                    StarParamType::ArbitraryLen(t1),
                                    StarParamType::ArbitraryLen(t2),
                                ) => eq(t1, t2),
                                (
                                    StarParamType::ParamSpecArgs(u1),
                                    StarParamType::ParamSpecArgs(u2),
                                ) => u1 == u2,
                                (
                                    StarParamType::UnpackedTuple(tup1),
                                    StarParamType::UnpackedTuple(tup2),
                                ) => tuple_args_eq(&tup1.args, &tup2.args),
                                _ => false,
                            },
                            (ParamType::StarStar(s1), ParamType::StarStar(s2)) => match (s1, s2) {
                                (
                                    StarStarParamType::ValueType(t1),
                                    StarStarParamType::ValueType(t2),
                                ) => eq(t1, t2),
                                (
                                    StarStarParamType::ParamSpecKwargs(u1),
                                    StarStarParamType::ParamSpecKwargs(u2),
                                ) => u1 == u2,
                                (
                                    StarStarParamType::UnpackTypedDict(td1),
                                    StarStarParamType::UnpackTypedDict(td2),
                                ) => typed_dict_eq(td1, td2),
                                _ => false,
                            },
                            _ => false,
                        }
                })
            }
            (CallableParams::Any(_), CallableParams::Any(_)) => true,
            _ => false,
        };
        let matches_generics = |g1: Generics, g2: Generics| {
            g1.iter(db).zip(g2.iter(db)).all(|(g1, g2)| match (g1, g2) {
                (Generic::TypeArg(t1), Generic::TypeArg(t2)) => eq(&t1, &t2),
                (Generic::TypeArgs(ts1), Generic::TypeArgs(ts2)) => {
                    tuple_args_eq(&ts1.args, &ts2.args)
                }
                (Generic::ParamSpecArg(p1), Generic::ParamSpecArg(p2)) => {
                    p1.type_vars == p2.type_vars && params_eq(&p1.params, &p2.params)
                }
                _ => false,
            })
        };
        let generic_class_eq = |g1: &GenericClass, g2: &GenericClass| {
            g1.link == g2.link && { matches_generics(g1.class(db).generics, g2.class(db).generics) }
        };
        match (self, other) {
            (Type::Class(g1), Type::Class(g2)) => generic_class_eq(g1, g2),
            (Type::Dataclass(d1), Type::Dataclass(d2)) => generic_class_eq(&d1.class, &d2.class),
            (Type::Tuple(tup1), Type::Tuple(tup2)) => tuple_args_eq(&tup1.args, &tup2.args),
            (Type::NamedTuple(nt1), Type::NamedTuple(nt2)) => {
                tuple_args_eq(&nt1.as_tuple().args, &nt2.as_tuple().args)
            }
            (Type::TypedDict(td1), Type::TypedDict(td2)) => typed_dict_eq(td1, td2),
            (Type::Callable(c1), Type::Callable(c2)) => {
                eq(&c1.return_type, &c2.return_type)
                    && params_eq(&c1.params, &c2.params)
                    && c1.type_vars == c2.type_vars
                    && {
                        c1.guard.is_none() && c2.guard.is_none()
                            || c1
                                .guard
                                .as_ref()
                                .zip(c2.guard.as_ref())
                                .is_some_and(|(c1, c2)| {
                                    c1.from_type_is && c2.from_type_is && eq(&c1.type_, &c2.type_)
                                })
                    }
            }
            (Type::Type(t1), Type::Type(t2)) => eq(t1, t2),
            (t1 @ Type::RecursiveType(r1), t2) | (t2, t1 @ Type::RecursiveType(r1))
                if unpack_recursive_type =>
            {
                let checking_type_recursion = CheckedTypeRecursion {
                    current: (t1, t2),
                    previous: checking_type_recursion.as_ref(),
                };
                if checking_type_recursion.is_cycle() {
                    return true;
                }
                r1.calculated_type(db).is_equal_type_internal(
                    db,
                    Some(checking_type_recursion),
                    t2,
                    unpack_recursive_type,
                    any_is_all,
                )
            }
            (Type::Literal(l1), Type::Literal(l2)) => l1.value(db) == l2.value(db),
            (Type::Literal(l), Type::Class(c)) | (Type::Class(c), Type::Literal(l))
                if db.mypy_compatible() =>
            {
                l.implicit && l.fallback_node_ref(db).as_link() == c.link
            }
            (Type::LiteralString { .. }, Type::LiteralString { .. }) => true,
            (Type::Any(_), Type::Any(_)) => true,
            (Type::Never(_), Type::Never(_)) => true,
            (Type::Union(u1), Type::Union(u2)) => is_equal_union_or_intersection(
                db,
                checking_type_recursion,
                u1.entries.iter().map(|e| &e.type_),
                u2.entries.iter().map(|e| &e.type_),
                unpack_recursive_type,
                any_is_all,
            ),
            (Type::Intersection(i1), Type::Intersection(i2)) => is_equal_union_or_intersection(
                db,
                checking_type_recursion,
                i1.iter_entries(),
                i2.iter_entries(),
                unpack_recursive_type,
                any_is_all,
            ),
            (Type::EnumMember(m1), Type::EnumMember(m2)) => {
                m1.member_index == m2.member_index && m1.enum_.defined_at == m2.enum_.defined_at
            }
            (Type::Any(_), _) | (_, Type::Any(_)) => any_is_all,
            _ => self == other,
        }
    }
}

fn is_equal_union_or_intersection<'x>(
    db: &Database,
    checking_type_recursion: Option<CheckedTypeRecursion>,
    ts1: impl ExactSizeIterator<Item = &'x Type>,
    ts2: impl ExactSizeIterator<Item = &'x Type>,
    unpack_recursive_type: bool,
    any_is_all: bool,
) -> bool {
    if ts1.len() != ts2.len() {
        return false;
    }
    let mut all_second: Vec<_> = ts2.collect();
    'outer: for t1 in ts1 {
        for (i, t2) in all_second.iter().enumerate() {
            if t1.is_equal_type_internal(
                db,
                checking_type_recursion,
                t2,
                unpack_recursive_type,
                any_is_all,
            ) {
                all_second.remove(i);
                continue 'outer;
            }
        }
        return false;
    }
    all_second.is_empty()
}
