use std::{borrow::Cow, iter::Peekable, rc::Rc};

use parsa_python_cst::ParamKind;

use crate::{
    arguments::{Arg, ArgKind},
    database::Database,
    debug,
    format_data::{FormatData, ParamsStyle},
    inference_state::InferenceState,
    matching::{Match, Matcher},
    type_::{
        empty_types, match_tuple_type_arguments, AnyCause, CallableParam, CallableParams,
        ParamSpecUsage, ParamType, StarParamType, StarStarParamType, StringSlice, Tuple, TupleArgs,
        TupleUnpack, Type, TypedDict, TypedDictMember, Variance, WithUnpack,
    },
};

pub trait Param<'x>: Copy + std::fmt::Debug {
    fn has_default(&self) -> bool;
    fn name(&self, db: &'x Database) -> Option<&str>;
    fn specific<'db: 'x>(&self, db: &'db Database) -> WrappedParamType<'x>;
    fn kind(&self, db: &Database) -> ParamKind;
    fn into_callable_param(self) -> CallableParam;
}

pub fn matches_params_with_variance(
    i_s: &InferenceState,
    matcher: &mut Matcher,
    params1: &CallableParams,
    params2: &CallableParams,
    variance: Variance,
) -> Match {
    match variance {
        Variance::Covariant => matches_params(i_s, matcher, params1, params2),
        Variance::Contravariant => matches_params(i_s, matcher, params2, params1),
        Variance::Invariant => {
            matches_params(i_s, matcher, params1, params2)
                & matches_params(i_s, matcher, params2, params1)
        }
    }
}

pub fn matches_params(
    i_s: &InferenceState,
    matcher: &mut Matcher,
    params1: &CallableParams,
    params2: &CallableParams,
) -> Match {
    let result = matches_params_detailed(
        i_s,
        matcher,
        params1,
        params2,
        Variance::Contravariant,
        false,
    );
    debug!(
        "Matched params {} against {}: {result:?}",
        params1.format(&FormatData::new_short(i_s.db), ParamsStyle::CallableParams),
        params2.format(&FormatData::new_short(i_s.db), ParamsStyle::CallableParams),
    );
    result
}

fn matches_params_detailed(
    i_s: &InferenceState,
    matcher: &mut Matcher,
    params1: &CallableParams,
    params2: &CallableParams,
    // TODO it seems like this param is currently unused and always Contravariant
    inner_variance: Variance, // Variance of the types of the params
    skip_first_of_params2: bool,
) -> Match {
    use CallableParams::*;
    match (params1, params2) {
        (Simple(params1), Simple(params2)) => {
            if skip_first_of_params2 {
                matches_simple_params(
                    i_s,
                    matcher,
                    params1.iter(),
                    params2.iter().skip(1).peekable(),
                    inner_variance,
                )
            } else {
                matches_simple_params(
                    i_s,
                    matcher,
                    params1.iter(),
                    params2.iter().peekable(),
                    inner_variance,
                )
            }
        }
        (Any(cause), _) => {
            matcher.set_all_contained_type_vars_to_any_in_callable_params(i_s, params2, *cause);
            Match::new_true()
        }
        (_, Any(cause)) => {
            matcher.set_all_contained_type_vars_to_any_in_callable_params(i_s, params1, *cause);
            Match::new_true()
        }
        (_, Never(cause)) => Match::new_true(),
        (Never(cause), _) => Match::new_false(),
    }
}

pub fn matches_simple_params<
    'db: 'x + 'y,
    'x,
    'y,
    P1: Param<'x>,
    P2: Param<'y>,
    I1: Iterator<Item = P1> + Clone,
>(
    i_s: &InferenceState<'db, '_>,
    matcher: &mut Matcher,
    params1: I1,
    mut params2: Peekable<impl Iterator<Item = P2> + Clone>,
    variance: Variance,
) -> Match {
    let match_with_variance =
        |i_s: &_, matcher: &mut _, a: &Option<Cow<Type>>, b: &Option<Cow<Type>>, variance| {
            if let Some(a) = a {
                if let Some(b) = b {
                    return a.matches(i_s, matcher, b, variance);
                }
            }
            Match::new_true()
        };

    let match_ = |i_s: &_, matcher: &mut _, a: &Option<Cow<Type>>, b: &Option<Cow<Type>>| {
        match_with_variance(i_s, matcher, a, b, variance)
    };

    let mut unused_keyword_params: Vec<P2> = vec![];
    let mut mismatched_name_pos_params1: Vec<P1> = vec![];
    let mut mismatched_name_pos_params2: Vec<P2> = vec![];

    let mut matches = Match::new_true();
    let mut params1 = params1.peekable();
    'p1_iter: while let Some(param1) = params1.next() {
        if let Some(mut param2) = params2
            .peek()
            .or_else(|| unused_keyword_params.first())
            .copied()
        {
            let mut specific2 = param2.specific(i_s.db);
            if let WrappedParamType::Star(WrappedStar::ParamSpecArgs(u2)) = specific2 {
                matches &= matcher.match_or_add_param_spec(
                    i_s,
                    u2,
                    std::iter::once(param1).chain(params1),
                    variance.invert(),
                );
                return matches;
            }
            if param1.has_default() && !param2.has_default() {
                debug!(
                    "Mismatch callable, because {:?} has default and {:?} hasn't",
                    param1.name(i_s.db),
                    param2.name(i_s.db)
                );
                return Match::new_false();
            }
            let specific1 = param1.specific(i_s.db);

            if let Some(m) =
                match_unpack_from_other_side(i_s, matcher, &specific2, variance, || {
                    std::iter::once(param1)
                        .peekable()
                        .chain(&mut params1)
                        .peekable()
                })
            {
                matches &= m;
                params2.next();
                continue;
            }
            match &specific1 {
                WrappedParamType::PositionalOnly(t1) => match &specific2 {
                    WrappedParamType::PositionalOnly(t2)
                    | WrappedParamType::PositionalOrKeyword(t2) => {
                        matches &= match_(i_s, matcher, t1, t2)
                    }
                    WrappedParamType::Star(s2) => match s2 {
                        WrappedStar::ArbitraryLen(t2) => {
                            matches &= match_(i_s, matcher, t1, t2);
                            continue;
                        }
                        WrappedStar::ParamSpecArgs(u) => todo!(),
                        WrappedStar::UnpackedTuple(_) => {
                            debug!("Params mismatch because PositionalOnly vs. UnpackedTuple");
                            return Match::new_false();
                        }
                    },
                    _ => {
                        debug!(
                            "Params mismatch, because had {:?} vs {:?}",
                            param1.kind(i_s.db),
                            param2.kind(i_s.db)
                        );
                        return Match::new_false();
                    }
                },
                WrappedParamType::PositionalOrKeyword(t1) => match &specific2 {
                    WrappedParamType::PositionalOrKeyword(t2) => {
                        let name1 = param1.name(i_s.db);
                        let name2 = param2.name(i_s.db);
                        if name1 != name2 {
                            if matcher.ignore_positional_param_names() {
                                // This logic is so weird in mypy, have a look at the tests:
                                //
                                // - testPositionalOverridingArgumentNameInsensitivity
                                // - testPositionalOverridingArgumentNamesCheckedWhenMismatchingPos
                                //
                                // to see how this works.
                                if mismatched_name_pos_params2
                                    .iter()
                                    .any(|p2| p2.name(i_s.db) == name1)
                                {
                                    debug!(
                                        "Params mismatch because of name {name1:?} != {name2:?} \
                                            (ignored positional param names #1)"
                                    );
                                    return Match::new_false();
                                }
                                if mismatched_name_pos_params1
                                    .iter()
                                    .any(|p1| p1.name(i_s.db) == name2)
                                {
                                    debug!(
                                        "Params mismatch because of name {name1:?} != {name2:?} \
                                            (ignored positional param names #2)"
                                    );
                                    return Match::new_false();
                                }
                                mismatched_name_pos_params1.push(param1);
                                mismatched_name_pos_params2.push(param2);
                            } else {
                                debug!("Params mismatch because of name {name1:?} != {name2:?}");
                                return Match::new_false();
                            }
                        }
                        matches &= match_(i_s, matcher, t1, t2)
                    }
                    WrappedParamType::Star(WrappedStar::ArbitraryLen(s2)) => {
                        matches &= match_(i_s, matcher, t1, s2);
                        let mut cloned_params2 = params2.clone();
                        cloned_params2.next();
                        for p2 in cloned_params2 {
                            match p2.specific(i_s.db) {
                                WrappedParamType::StarStar(WrappedStarStar::ValueType(ref d2)) => {
                                    matches &= match_with_variance(
                                        i_s,
                                        matcher,
                                        s2,
                                        d2,
                                        Variance::Invariant,
                                    );
                                    continue 'p1_iter;
                                }
                                WrappedParamType::KeywordOnly(ref d2) => {
                                    if p2.name(i_s.db) == param1.name(i_s.db) {
                                        if p2.has_default() {
                                            matches &= match_(i_s, matcher, t1, d2);
                                            continue 'p1_iter;
                                        } else {
                                            debug!("Params mismatch because keyword param is not default");
                                            return Match::new_false();
                                        }
                                    }
                                }
                                _ => {
                                    debug!(
                                        "Params mismatch because PositionalOrKeyword \
                                            that could not be matched by *args, **kwargs"
                                    );
                                    return Match::new_false();
                                }
                            }
                        }
                        debug!(
                            "Params mismatch because we did not find a kwarg \
                                that fits the variadic param"
                        );
                        return Match::new_false();
                    }
                    WrappedParamType::PositionalOnly(t2)
                        if matcher.ignore_positional_param_names() =>
                    {
                        matches &= match_(i_s, matcher, t1, t2)
                    }
                    _ => {
                        debug!(
                            "Params mismatch, because had {:?} vs {:?}",
                            param1.kind(i_s.db),
                            param2.kind(i_s.db)
                        );
                        return Match::new_false();
                    }
                },
                WrappedParamType::KeywordOnly(t1) => {
                    if matches!(specific2, WrappedParamType::Star(_)) {
                        params2.next();
                        if let Some(p2) = params2.peek() {
                            param2 = *p2;
                            specific2 = param2.specific(i_s.db);
                        }
                    }
                    match &specific2 {
                        WrappedParamType::StarStar(WrappedStarStar::ValueType(t2)) => {
                            matches &= match_(i_s, matcher, t1, t2);
                            continue;
                        }
                        WrappedParamType::StarStar(WrappedStarStar::UnpackTypedDict(u)) => {
                            if let Some(member2) = param1
                                .name(i_s.db)
                                .and_then(|name1| u.find_member(i_s.db, name1))
                            {
                                // TODO check if param can be optional
                                if let Some(t1) = t1 {
                                    matches &= t1.matches(i_s, matcher, &member2.type_, variance);
                                }
                                continue;
                            } else {
                                debug!("Param mismatch because kw name was not found in unpack");
                                return Match::new_false();
                            }
                        }
                        WrappedParamType::StarStar(_) => {
                            debug!(
                                "Params mismatch, because had {:?} vs {:?}",
                                param1.kind(i_s.db),
                                param2.kind(i_s.db)
                            );
                            return Match::new_false();
                        }
                        _ => {
                            for (i, p2) in unused_keyword_params.iter().enumerate() {
                                if param1.name(i_s.db) == p2.name(i_s.db) {
                                    match unused_keyword_params.remove(i).specific(i_s.db) {
                                        WrappedParamType::KeywordOnly(t2)
                                        | WrappedParamType::PositionalOrKeyword(t2) => {
                                            matches &= match_(i_s, matcher, t1, &t2);
                                        }
                                        _ => unreachable!(),
                                    }
                                    continue 'p1_iter;
                                }
                            }
                            let mut found = false;
                            while params2
                                .peek()
                                .is_some_and(|p2| !matches!(p2.kind(i_s.db), ParamKind::StarStar))
                            {
                                param2 = *params2.peek().unwrap();
                                if param1.name(i_s.db) == param2.name(i_s.db) {
                                    match &param2.specific(i_s.db) {
                                        WrappedParamType::PositionalOrKeyword(t2)
                                        | WrappedParamType::KeywordOnly(t2) => {
                                            matches &= match_(i_s, matcher, t1, t2);
                                            found = true;
                                            break;
                                        }
                                        _ => continue,
                                    }
                                } else {
                                    params2.next();
                                    if matches!(
                                        param2.kind(i_s.db),
                                        ParamKind::PositionalOrKeyword | ParamKind::KeywordOnly
                                    ) {
                                        unused_keyword_params.push(param2);
                                    }
                                }
                            }
                            if !found {
                                debug!("Params mismatch, because keyword was not found");
                                return Match::new_false();
                            }
                        }
                    }
                }
                WrappedParamType::Star(WrappedStar::ParamSpecArgs(u1)) => {
                    matches &= matcher.match_or_add_param_spec(i_s, u1, params2, variance);
                    return matches;
                }
                WrappedParamType::Star(s1) => match &specific2 {
                    WrappedParamType::Star(s2) => match (s1, s2) {
                        (WrappedStar::ArbitraryLen(t1), WrappedStar::ArbitraryLen(t2)) => {
                            matches &= match_(i_s, matcher, t1, t2)
                        }
                        (WrappedStar::ArbitraryLen(_), WrappedStar::ParamSpecArgs(_)) => {
                            todo!()
                        }
                        (WrappedStar::UnpackedTuple(tup1), WrappedStar::UnpackedTuple(tup2)) => {
                            matches &= Type::Tuple(tup1.clone()).matches(
                                i_s,
                                matcher,
                                &Type::Tuple(tup2.clone()),
                                variance,
                            );
                        }
                        (WrappedStar::UnpackedTuple(tup1), WrappedStar::ArbitraryLen(t2)) => {
                            if let Some(t2) = t2 {
                                match &tup1.args {
                                    TupleArgs::ArbitraryLen(t1) => {
                                        matches &= t1.matches(i_s, matcher, t2, variance);
                                    }
                                    TupleArgs::FixedLen(ts1) => {
                                        for t1 in ts1.iter() {
                                            matches &= t1.matches(i_s, matcher, t2, variance);
                                        }
                                    }
                                    TupleArgs::WithUnpack(u1) => match &u1.unpack {
                                        TupleUnpack::ArbitraryLen(t1) => {
                                            for t2 in u1.before.iter() {
                                                matches &= t1.matches(i_s, matcher, t2, variance);
                                            }
                                            matches &= t1.matches(i_s, matcher, t2, variance);
                                            for t2 in u1.after.iter() {
                                                matches &= t1.matches(i_s, matcher, t2, variance);
                                            }
                                        }
                                        TupleUnpack::TypeVarTuple(tvt) => {
                                            if !u1.before.is_empty() || !u1.after.is_empty() {
                                                todo!()
                                            }
                                            matches &= matcher.match_or_add_type_var_tuple(
                                                i_s,
                                                tvt,
                                                TupleArgs::ArbitraryLen(Box::new((**t2).clone())),
                                                variance,
                                            )
                                        }
                                    },
                                }
                            }
                        }
                        (WrappedStar::ArbitraryLen(t1), WrappedStar::UnpackedTuple(tup2)) => {
                            match &tup2.args {
                                TupleArgs::ArbitraryLen(t2) => {
                                    if let Some(t1) = t1 {
                                        matches &= t1.matches(i_s, matcher, t2, variance);
                                    }
                                }
                                _ => {
                                    debug!("Param mismatch, because arbitrary len {:?} vs Unpack[{:?}]", t1.as_ref().map(|t| t.format_short(i_s.db)), tup2.format(&FormatData::new_short(i_s.db)));
                                    matches &= Match::new_false();
                                    todo!()
                                }
                            };
                        }
                        _ => todo!("{s1:?} {s2:?}"),
                    },
                    _ => match s1 {
                        WrappedStar::UnpackedTuple(tup1) => {
                            let Some(tup2_args) = gather_unpack_args(i_s.db, &mut params2) else {
                                debug!("Params mismatch, because tuple args");
                                return Match::new_false();
                            };
                            matches &= match_tuple_type_arguments(
                                i_s, matcher, &tup1.args, &tup2_args, variance,
                            );
                            continue;
                        }
                        _ => {
                            if !matcher.precise_matching
                                && is_trivial_suffix(i_s.db, specific1, params1.next())
                            {
                                debug!("Matched because of trivial suffix");
                                return matches;
                            }
                            debug!(
                                "Params mismatch, because of {:?} vs {:?}",
                                param1.kind(i_s.db),
                                param2.kind(i_s.db)
                            );
                            return Match::new_false();
                        }
                    },
                },
                WrappedParamType::StarStar(d1) => match specific2 {
                    WrappedParamType::StarStar(d2) => match (d1, d2) {
                        (WrappedStarStar::ValueType(t1), WrappedStarStar::ValueType(t2)) => {
                            matches &= match_(i_s, matcher, t1, &t2)
                        }
                        (
                            WrappedStarStar::ParamSpecKwargs(u1),
                            WrappedStarStar::ParamSpecKwargs(u2),
                        ) => {
                            //debug_assert!(*u1 != u2, "Args should have been checked earlier")
                        }
                        (
                            WrappedStarStar::UnpackTypedDict(td1),
                            WrappedStarStar::UnpackTypedDict(td2),
                        ) => {
                            let td1 = td1.clone();
                            let mut check = |td_x: &TypedDict, td_y: &TypedDict| {
                                td_x.matches(i_s, matcher, td_y, true)
                            };
                            matches &= match variance {
                                Variance::Contravariant => check(&td2, &td1),
                                Variance::Covariant => todo!(),
                                Variance::Invariant => todo!(),
                            }
                        }
                        (WrappedStarStar::UnpackTypedDict(td1), WrappedStarStar::ValueType(t2)) => {
                            if let Some(t2) = t2 {
                                for member in td1.members(i_s.db).iter() {
                                    matches &= member.type_.matches(i_s, matcher, &t2, variance)
                                }
                            }
                        }
                        (x, y) => todo!("{:?} {:?}", x, y),
                    },
                    WrappedParamType::PositionalOrKeyword(t2)
                    | WrappedParamType::KeywordOnly(t2) => match d1 {
                        WrappedStarStar::UnpackTypedDict(td1) => {
                            return matches_simple_params(
                                i_s,
                                matcher,
                                td1.members(i_s.db).iter().map(TypedDictMemberParam),
                                params2,
                                variance,
                            )
                        }
                        _ => {
                            debug!(
                                "Params mismatch, because had {:?} vs {:?}",
                                param1.kind(i_s.db),
                                param2.kind(i_s.db)
                            );
                            return Match::new_false();
                        }
                    },
                    _ => {
                        debug!(
                            "Params mismatch, because had {:?} vs {:?}",
                            param1.kind(i_s.db),
                            param2.kind(i_s.db)
                        );
                        return Match::new_false();
                    }
                },
            };
            params2.next();
        } else {
            match param1.specific(i_s.db) {
                WrappedParamType::Star(WrappedStar::UnpackedTuple(tup1))
                    if params1.next().is_none() =>
                {
                    matches &= match_tuple_type_arguments(
                        i_s,
                        matcher,
                        &tup1.args,
                        &TupleArgs::FixedLen(empty_types()),
                        variance,
                    );
                    break;
                }
                WrappedParamType::Star(WrappedStar::ParamSpecArgs(u1)) => {
                    matches &= matcher.match_or_add_param_spec(i_s, u1, params2, variance);
                    return matches;
                }
                specific1 => {
                    if !matcher.precise_matching
                        && is_trivial_suffix(i_s.db, specific1, params1.next())
                    {
                        debug!("Matched because of trivial suffix (too few params)");
                        return matches;
                    }
                    debug!(
                        "Params mismatch, because one side had fewer params: {:?}",
                        param1.name(i_s.db)
                    );
                    return Match::new_false();
                }
            }
        }
    }
    for unused in unused_keyword_params {
        if !unused.has_default() {
            debug!("Params mismatch, because had unused keyword params");
            return Match::new_false();
        }
    }
    for param2 in params2 {
        if let Some(m) =
            match_unpack_from_other_side(i_s, matcher, &param2.specific(i_s.db), variance, || {
                [].iter().peekable()
            })
        {
            matches &= m;
            continue;
        }
        if let WrappedParamType::Star(WrappedStar::ParamSpecArgs(u2)) = param2.specific(i_s.db) {
            matches &= matcher.match_or_add_param_spec(i_s, u2, params1, variance.invert());
            return matches;
        }
        if !param2.has_default()
            && !matches!(param2.kind(i_s.db), ParamKind::Star | ParamKind::StarStar)
        {
            debug!("Params mismatch, because the other side had an additional param");
            return Match::new_false();
        }
    }
    matches
}

fn is_trivial_suffix<'x, P1: Param<'x>>(
    db: &'x Database,
    p1: WrappedParamType,
    p2: Option<P1>,
) -> bool {
    // Mypy allows matching anything if the function ends with *args: Any, **kwargs: Any
    // This is described in Mypy's commit f41e24c8b31a110c2f01a753acba458977e41bfc
    let WrappedParamType::Star(WrappedStar::ArbitraryLen(star_t)) = p1 else {
        return false;
    };
    let Some(p2) = p2 else {
        return false;
    };
    let WrappedParamType::StarStar(WrappedStarStar::ValueType(star_star_t)) = p2.specific(db)
    else {
        return false;
    };

    let is_any = |t: &Option<Cow<Type>>| match t {
        Some(t) => matches!(t.as_ref(), Type::Any(_)),
        None => true,
    };

    is_any(&star_t) && is_any(&star_star_t)
}

fn match_unpack_from_other_side<'db: 'x, 'x, P: Param<'x>, IT: Iterator<Item = P>>(
    i_s: &InferenceState<'db, '_>,
    matcher: &mut Matcher,
    specific2: &WrappedParamType,
    variance: Variance,
    as_params: impl FnOnce() -> Peekable<IT>,
) -> Option<Match> {
    if let WrappedParamType::Star(WrappedStar::UnpackedTuple(unpacked2)) = specific2 {
        if let TupleArgs::WithUnpack(WithUnpack {
            unpack: TupleUnpack::TypeVarTuple(tvt2),
            ..
        }) = &unpacked2.args
        {
            if matcher.has_responsible_matcher(tvt2) {
                // TODO making params1 peekable is not possible in this way and will always
                // fetch a param too much.
                let mut params1 = as_params();
                let tup1_args = gather_unpack_args(i_s.db, &mut params1)?;
                return Some(match_tuple_type_arguments(
                    i_s,
                    matcher,
                    &tup1_args,
                    &unpacked2.args,
                    variance,
                ));
            }
        }
    }
    None
}

fn gather_unpack_args<'db: 'x, 'x, P: Param<'x>>(
    db: &'db Database,
    params: &mut Peekable<impl Iterator<Item = P>>,
) -> Option<TupleArgs> {
    let mut before = vec![];
    let mut unpacked_tup = None;
    let mut after = vec![];
    while let Some(next) = params.peek() {
        match next.specific(db) {
            WrappedParamType::PositionalOnly(t2) | WrappedParamType::PositionalOrKeyword(t2) => {
                let t2 = t2
                    .map(|t2| t2.into_owned())
                    .unwrap_or(Type::Any(AnyCause::Unannotated));
                if unpacked_tup.is_none() {
                    before.push(t2)
                } else {
                    after.push(t2)
                }
            }
            WrappedParamType::Star(WrappedStar::UnpackedTuple(tup)) => {
                unpacked_tup = Some(tup);
            }
            WrappedParamType::Star(WrappedStar::ArbitraryLen(t)) => todo!(),
            WrappedParamType::Star(WrappedStar::ParamSpecArgs(t)) => return None,
            _ => break,
        }
        params.next();
    }
    Some(if let Some(unpacked_tup) = &unpacked_tup {
        let new_args = unpacked_tup.args.clone();
        new_args.add_before_and_after(before, after)
    } else {
        debug_assert!(after.is_empty());
        TupleArgs::FixedLen(before.into())
    })
}

pub fn has_overlapping_params(
    i_s: &InferenceState,
    matcher: &mut Matcher,
    params1: &CallableParams,
    params2: &CallableParams,
) -> bool {
    match (params1, params2) {
        (CallableParams::Simple(params1), CallableParams::Simple(params2)) => {
            overload_has_overlapping_params(i_s, params1.iter(), params2.iter())
        }
        (CallableParams::Any(_), _) | (_, CallableParams::Any(_)) => true,
        (CallableParams::Never(_), _) | (_, CallableParams::Never(_)) => true,
    }
}

fn overload_has_overlapping_params<'db: 'x, 'x, P1: Param<'x>, P2: Param<'x>>(
    i_s: &InferenceState<'db, '_>,
    params1: impl Iterator<Item = P1>,
    params2: impl Iterator<Item = P2>,
) -> bool {
    // This feels like a bit of a weird and partial implementation. But Mypy also implements these
    // things only partially and returning false feels like the safe way to compatible, since
    // having overlapping params might enable some lints that are not desired for users.

    let to_type = |db: &'db _, p2: P2| match p2.specific(db) {
        WrappedParamType::PositionalOnly(t2)
        | WrappedParamType::PositionalOrKeyword(t2)
        | WrappedParamType::KeywordOnly(t2)
        | WrappedParamType::Star(WrappedStar::ArbitraryLen(t2))
        | WrappedParamType::StarStar(WrappedStarStar::ValueType(t2)) => t2,
        WrappedParamType::Star(WrappedStar::ParamSpecArgs(u)) => todo!(),
        WrappedParamType::Star(WrappedStar::UnpackedTuple(u)) => todo!(),
        WrappedParamType::StarStar(WrappedStarStar::ParamSpecKwargs(u)) => todo!(),
        WrappedParamType::StarStar(WrappedStarStar::UnpackTypedDict(u)) => todo!(),
    };
    let check_type = |i_s: &InferenceState<'db, '_>, t1: Option<&Type>, p2: P2| {
        if let Some(t1) = t1 {
            if let Some(t2) = to_type(i_s.db, p2) {
                return t1.simple_overlaps(i_s, &t2);
            }
        }
        true
    };
    let mut had_any_fallback_with_default = false;
    // Get rid of defaults first, because they always overlap.
    let db = i_s.db;
    let mut params2 = params2
        .filter(|p| {
            let has_default = p.has_default();
            if has_default {
                // TODO it's weird that we are creating a new InferenceState, because of borrowing
                // issues in this closure
                if let Some(t) = to_type(db, *p) {
                    if t.is_any() {
                        had_any_fallback_with_default = true;
                    }
                }
            }
            !has_default
        })
        .peekable();
    let mut unused_keyword_params: Vec<P2> = vec![];
    for param1 in params1.filter(|p| !p.has_default()) {
        match param1.specific(i_s.db) {
            WrappedParamType::PositionalOrKeyword(t1) | WrappedParamType::PositionalOnly(t1) => {
                if let Some(param2) = params2.peek() {
                    if !check_type(i_s, t1.as_deref(), *param2) {
                        return false;
                    }
                    match param2.kind(db) {
                        ParamKind::PositionalOrKeyword | ParamKind::PositionalOnly => {
                            params2.next(); // We only peeked.
                        }
                        ParamKind::KeywordOnly => return false,
                        ParamKind::Star => (),
                        ParamKind::StarStar => (),
                    }
                } else {
                    return false;
                }
            }
            WrappedParamType::KeywordOnly(t1) => {
                if let Some(param2) = params2.peek() {
                    if param2.kind(db) == ParamKind::Star {
                        params2.next();
                    }
                }
                if let Some(mut param2) = params2
                    .peek()
                    .or_else(|| unused_keyword_params.first())
                    .copied()
                {
                    match param2.kind(db) {
                        ParamKind::KeywordOnly => {
                            let mut found = false;
                            for (i, p2) in unused_keyword_params.iter().enumerate() {
                                if param1.name(db) == p2.name(db) {
                                    param2 = unused_keyword_params.remove(i);
                                    found = true;
                                    break;
                                }
                            }
                            if !found {
                                while match params2.peek() {
                                    Some(p2) => matches!(p2.kind(db), ParamKind::KeywordOnly),
                                    None => false,
                                } {
                                    param2 = params2.next().unwrap();
                                    if param1.name(db) == param2.name(db) {
                                        found = true;
                                        break;
                                    } else {
                                        unused_keyword_params.push(param2);
                                    }
                                }
                                if !found {
                                    return false;
                                }
                            }
                        }
                        ParamKind::StarStar => (),
                        _ => return false,
                    }
                    if !check_type(i_s, t1.as_deref(), param2) {
                        return false;
                    }
                } else {
                    return false;
                }
            }
            WrappedParamType::Star(WrappedStar::ArbitraryLen(t1)) => {
                while match params2.peek() {
                    Some(p) => !matches!(p.kind(db), ParamKind::KeywordOnly | ParamKind::StarStar),
                    None => false,
                } {
                    if let Some(param2) = params2.next() {
                        if !check_type(i_s, t1.as_deref(), param2) {
                            return false;
                        }
                    }
                }
            }
            WrappedParamType::Star(WrappedStar::UnpackedTuple(u)) => {
                todo!()
            }
            WrappedParamType::Star(WrappedStar::ParamSpecArgs(u)) => todo!(),
            WrappedParamType::StarStar(WrappedStarStar::ValueType(t1)) => {
                for param2 in params2 {
                    if !check_type(i_s, t1.as_deref(), param2) {
                        return false;
                    }
                }
                return !had_any_fallback_with_default;
            }
            WrappedParamType::StarStar(WrappedStarStar::ParamSpecKwargs(u)) => {
                todo!()
            }
            WrappedParamType::StarStar(WrappedStarStar::UnpackTypedDict(u)) => {
                // TODO
            }
        }
    }
    for param2 in params2 {
        if !matches!(param2.kind(db), ParamKind::Star | ParamKind::StarStar) {
            return false;
        }
    }
    !had_any_fallback_with_default
}

impl<'x> Param<'x> for &'x CallableParam {
    fn has_default(&self) -> bool {
        self.has_default
    }

    fn name(&self, db: &'x Database) -> Option<&str> {
        self.name.as_ref().map(|n| n.as_str(db))
    }

    fn specific<'db: 'x>(&self, db: &Database) -> WrappedParamType<'x> {
        match &self.type_ {
            ParamType::PositionalOnly(t) => {
                WrappedParamType::PositionalOnly(Some(Cow::Borrowed(t)))
            }
            ParamType::PositionalOrKeyword(t) => {
                WrappedParamType::PositionalOrKeyword(Some(Cow::Borrowed(t)))
            }
            ParamType::KeywordOnly(t) => WrappedParamType::KeywordOnly(Some(Cow::Borrowed(t))),
            ParamType::Star(s) => WrappedParamType::Star(match s {
                StarParamType::ArbitraryLen(t) => WrappedStar::ArbitraryLen(Some(Cow::Borrowed(t))),
                StarParamType::UnpackedTuple(u) => WrappedStar::UnpackedTuple(u.clone()),
                StarParamType::ParamSpecArgs(u) => WrappedStar::ParamSpecArgs(u),
            }),
            ParamType::StarStar(s) => WrappedParamType::StarStar(match s {
                StarStarParamType::ValueType(t) => {
                    WrappedStarStar::ValueType(Some(Cow::Borrowed(t)))
                }
                StarStarParamType::ParamSpecKwargs(u) => WrappedStarStar::ParamSpecKwargs(u),
                StarStarParamType::UnpackTypedDict(u) => {
                    WrappedStarStar::UnpackTypedDict(u.clone())
                }
            }),
        }
    }

    fn kind(&self, db: &Database) -> ParamKind {
        self.type_.param_kind()
    }

    fn into_callable_param(self) -> CallableParam {
        self.clone()
    }
}

pub enum UnpackTypedDictState {
    Unused(Rc<TypedDict>),
    CheckingUnusedKwArgs,
    Used,
}
impl UnpackTypedDictState {
    pub fn maybe_unchecked(&self) -> Option<Rc<TypedDict>> {
        match self {
            Self::Unused(td) => Some(td.clone()),
            _ => None,
        }
    }
}
pub struct InferrableParamIterator<'db, 'a, I, P, AI: Iterator> {
    db: &'db Database,
    arguments: AI,
    current_arg: Option<Arg<'db, 'a>>,
    params: I,
    pub unused_keyword_arguments: Vec<Arg<'db, 'a>>,
    current_starred_param: Option<P>,
    current_double_starred_param: Option<P>,
    pub too_many_positional_arguments: bool,
    arbitrary_length_handled: bool,
    pub unused_unpack_typed_dict: UnpackTypedDictState,
}

impl<'db, 'a, I, P, AI: Iterator<Item = Arg<'db, 'a>>> InferrableParamIterator<'db, 'a, I, P, AI> {
    pub fn new(db: &'db Database, params: I, arguments: AI) -> Self {
        Self {
            db,
            arguments,
            current_arg: None,
            params,
            unused_keyword_arguments: vec![],
            current_starred_param: None,
            current_double_starred_param: None,
            too_many_positional_arguments: false,
            arbitrary_length_handled: true,
            unused_unpack_typed_dict: UnpackTypedDictState::Used,
        }
    }

    pub fn has_unused_arguments(&mut self) -> bool {
        while let Some(arg) = self.next_arg() {
            if arg.in_args_or_kwargs_and_arbitrary_len() {
                self.current_arg = None;
            } else {
                // Should not modify arguments that are uncalled-for, because we use them later for
                // diagnostics.
                self.current_arg = Some(arg);
                return true;
            }
        }
        false
    }

    pub fn had_arbitrary_length_handled(self) -> bool {
        self.arbitrary_length_handled
    }

    pub fn next_arg(&mut self) -> Option<Arg<'db, 'a>> {
        let arg = self.current_arg.take().or_else(|| self.arguments.next());
        if let Some(a) = &arg {
            if a.in_args_or_kwargs_and_arbitrary_len() {
                self.arbitrary_length_handled = false;
                self.current_arg.clone_from(&arg);
            }
        }
        arg
    }

    fn maybe_exact_multi_arg(&mut self, is_keyword_arg: bool) -> Option<Arg<'db, 'a>> {
        self.next_arg().and_then(|arg| {
            if arg.is_keyword_argument() == is_keyword_arg {
                self.arbitrary_length_handled = true;
                self.current_arg = None;
                Some(arg)
            } else {
                self.current_arg = Some(arg);
                None
            }
        })
    }
}

impl<'db: 'x, 'a, 'x, I, P, AI> Iterator for InferrableParamIterator<'db, 'a, I, P, AI>
where
    I: Iterator<Item = P>,
    P: Param<'x>,
    AI: Iterator<Item = Arg<'db, 'a>>,
{
    type Item = InferrableParam<'db, 'a, P>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(param) = self.current_starred_param {
            if let Some(argument) = self.maybe_exact_multi_arg(false) {
                return Some(InferrableParam {
                    param,
                    argument: ParamArgument::Argument(argument),
                });
            } else {
                self.current_starred_param = None;
            }
        }
        if let Some(param) = self.current_double_starred_param {
            if let WrappedParamType::StarStar(WrappedStarStar::UnpackTypedDict(td)) =
                param.specific(self.db)
            {
                if !matches!(self.unused_unpack_typed_dict, UnpackTypedDictState::Used) {
                    for (i, unused) in self.unused_keyword_arguments.iter().enumerate() {
                        if let Some(key) = unused.keyword_name(self.db) {
                            if let Some(member) = td.find_member(self.db, key) {
                                self.unused_unpack_typed_dict =
                                    UnpackTypedDictState::CheckingUnusedKwArgs;
                                return Some(InferrableParam {
                                    param,
                                    argument: ParamArgument::MatchedUnpackedTypedDictMember {
                                        argument: self.unused_keyword_arguments.remove(i),
                                        type_: member.type_.clone(),
                                        name: member.name,
                                    },
                                });
                            }
                        }
                    }
                }
                while let Some(argument) = self.next_arg() {
                    if let Some(key) = argument.keyword_name(self.db) {
                        if let Some(member) = td.find_member(self.db, key) {
                            self.unused_unpack_typed_dict = UnpackTypedDictState::Used;
                            return Some(InferrableParam {
                                param,
                                argument: ParamArgument::MatchedUnpackedTypedDictMember {
                                    argument,
                                    type_: member.type_.clone(),
                                    name: member.name,
                                },
                            });
                        } else {
                            self.unused_keyword_arguments.push(argument);
                        }
                    } else if argument.in_args_or_kwargs_and_arbitrary_len() {
                        self.current_arg = None;
                        if matches!(
                            &argument.kind,
                            ArgKind::Inferred {
                                is_keyword: Some(None),
                                ..
                            }
                        ) {
                            self.unused_unpack_typed_dict = UnpackTypedDictState::Used;
                            return Some(InferrableParam {
                                param,
                                argument: ParamArgument::Argument(argument),
                            });
                        }
                    } else {
                        self.too_many_positional_arguments = true;
                    }
                }
            } else if let Some(argument) = self
                .maybe_exact_multi_arg(true)
                .or_else(|| self.unused_keyword_arguments.pop())
            {
                return Some(InferrableParam {
                    param,
                    argument: ParamArgument::Argument(argument),
                });
            } else {
                self.current_double_starred_param = None;
            }
        }
        let check_unused = |self_: &mut Self, param: P| {
            for (i, unused) in self_.unused_keyword_arguments.iter().enumerate() {
                let key = unused.keyword_name(self.db).unwrap();
                if Some(key) == param.name(self_.db) {
                    return Some(InferrableParam {
                        param,
                        argument: ParamArgument::Argument(self_.unused_keyword_arguments.remove(i)),
                    });
                }
            }
            None
        };
        self.params.next().and_then(|param| {
            let mut argument_with_index = None;
            match param.kind(self.db) {
                ParamKind::PositionalOrKeyword => {
                    while let Some(arg) = self.next_arg() {
                        if let Some(key) = arg.keyword_name(self.db) {
                            if Some(key) == param.name(self.db) {
                                argument_with_index = Some(arg);
                                break;
                            } else {
                                self.unused_keyword_arguments.push(arg);
                            }
                        } else {
                            argument_with_index = Some(arg);
                            break;
                        }
                    }
                    if argument_with_index.is_none() {
                        if let Some(p) = check_unused(self, param) {
                            return Some(p);
                        }
                    }
                }
                ParamKind::KeywordOnly => {
                    while let Some(arg) = self.next_arg() {
                        match arg.kind {
                            ArgKind::Inferred {
                                is_keyword: Some(None),
                                in_args_or_kwargs_and_arbitrary_len: true,
                                ..
                            } => {
                                argument_with_index = Some(arg);
                                break;
                            }
                            _ => {
                                if let Some(key) = arg.keyword_name(self.db) {
                                    if Some(key) == param.name(self.db) {
                                        argument_with_index = Some(arg);
                                        break;
                                    } else {
                                        self.unused_keyword_arguments.push(arg);
                                    }
                                } else if arg.in_args_or_kwargs_and_arbitrary_len() {
                                    self.current_arg = None;
                                } else {
                                    self.too_many_positional_arguments = true;
                                }
                            }
                        }
                    }
                    if argument_with_index.is_none() {
                        if let Some(p) = check_unused(self, param) {
                            return Some(p);
                        }
                    }
                }
                ParamKind::PositionalOnly => {
                    if let Some(arg) = self.next_arg() {
                        match arg.kind {
                            ArgKind::Positional { .. }
                            | ArgKind::Inferred {
                                is_keyword: None, ..
                            }
                            | ArgKind::InferredWithCustomAddIssue { .. }
                            | ArgKind::Comprehension { .. } => argument_with_index = Some(arg),
                            _ => {
                                if arg.keyword_name(self.db).is_some() {
                                    self.unused_keyword_arguments.push(arg);
                                }
                            }
                        }
                    }
                }
                ParamKind::Star => match param.specific(self.db) {
                    WrappedParamType::Star(WrappedStar::ParamSpecArgs(u)) => {
                        let next = self.params.next();
                        debug_assert!(matches!(
                            next.unwrap().specific(self.db),
                            WrappedParamType::StarStar(WrappedStarStar::ParamSpecKwargs(u)),
                        ));
                        return Some(InferrableParam {
                            param,
                            argument: ParamArgument::ParamSpecArgs(
                                u.clone(),
                                // TODO this is completely wrong. THERE IS ALSO current_arg
                                self.arguments.by_ref().collect(),
                            ),
                        });
                    }
                    WrappedParamType::Star(WrappedStar::UnpackedTuple(u)) => {
                        let mut args = vec![];
                        // Fetch all positional arguments
                        while let Some(arg) = self.next_arg() {
                            self.current_arg = None;
                            if arg.is_keyword_argument() {
                                self.current_arg = Some(arg);
                                break;
                            }
                            args.push(arg);
                        }
                        return Some(InferrableParam {
                            param,
                            argument: ParamArgument::TupleUnpack(args.into()),
                        });
                    }
                    WrappedParamType::Star(WrappedStar::ArbitraryLen(_)) => {
                        self.current_starred_param = Some(param);
                        return self.next();
                    }
                    _ => unreachable!(),
                },
                ParamKind::StarStar => {
                    self.current_double_starred_param = Some(param);
                    if let WrappedParamType::StarStar(WrappedStarStar::UnpackTypedDict(td)) =
                        param.specific(self.db)
                    {
                        self.unused_unpack_typed_dict = UnpackTypedDictState::Unused(td);
                    }
                    return self.next();
                }
            }
            Some(
                argument_with_index
                    .map(|a| InferrableParam {
                        param,
                        argument: ParamArgument::Argument(a),
                    })
                    .unwrap_or_else(|| InferrableParam {
                        param,
                        argument: ParamArgument::None,
                    }),
            )
        })
    }
}

#[derive(Clone, Copy, Debug)]
struct TypedDictMemberParam<'member>(&'member TypedDictMember);

impl<'member> Param<'member> for TypedDictMemberParam<'member> {
    fn has_default(&self) -> bool {
        !self.0.required
    }

    fn name(&self, db: &'member Database) -> Option<&str> {
        Some(self.0.name.as_str(db))
    }

    fn specific<'db: 'member>(&self, db: &'db Database) -> WrappedParamType<'member> {
        WrappedParamType::KeywordOnly(Some(Cow::Borrowed(&self.0.type_)))
    }

    fn kind(&self, db: &Database) -> ParamKind {
        ParamKind::KeywordOnly
    }

    fn into_callable_param(self) -> CallableParam {
        todo!()
    }
}

#[derive(Debug)]
pub enum ParamArgument<'db, 'a> {
    None,
    Argument(Arg<'db, 'a>),
    TupleUnpack(Box<[Arg<'db, 'a>]>), // For stuff like *args: *Ts
    MatchedUnpackedTypedDictMember {
        argument: Arg<'db, 'a>,
        type_: Type,
        name: StringSlice,
    },
    ParamSpecArgs(ParamSpecUsage, Box<[Arg<'db, 'a>]>),
}

#[derive(Debug)]
pub struct InferrableParam<'db, 'a, P> {
    pub param: P,
    pub argument: ParamArgument<'db, 'a>,
}

#[derive(Debug)]
pub enum WrappedParamType<'a> {
    PositionalOnly(Option<Cow<'a, Type>>),
    PositionalOrKeyword(Option<Cow<'a, Type>>),
    KeywordOnly(Option<Cow<'a, Type>>),
    Star(WrappedStar<'a>),
    StarStar(WrappedStarStar<'a>),
}

#[derive(Debug)]
pub enum WrappedStar<'a> {
    ArbitraryLen(Option<Cow<'a, Type>>),
    ParamSpecArgs(&'a ParamSpecUsage),
    UnpackedTuple(Rc<Tuple>),
}

#[derive(Debug)]
pub enum WrappedStarStar<'a> {
    ValueType(Option<Cow<'a, Type>>),
    ParamSpecKwargs(&'a ParamSpecUsage),
    UnpackTypedDict(Rc<TypedDict>),
}

impl ParamArgument<'_, '_> {
    pub fn is_lambda_argument(&self) -> bool {
        match self {
            Self::Argument(arg) => match &arg.kind {
                ArgKind::Positional(pos_arg) => pos_arg.named_expr.expression().is_lambda(),
                ArgKind::Keyword(kw) => kw.expression.is_lambda(),
                _ => false,
            },
            _ => false,
        }
    }
}
