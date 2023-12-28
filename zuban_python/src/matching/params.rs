use std::{borrow::Cow, iter::Peekable, rc::Rc};

use parsa_python_ast::ParamKind;

use super::{Match, Matcher};
use crate::{
    arguments::{Argument, ArgumentKind},
    database::{Database, PointLink},
    debug,
    inference_state::InferenceState,
    type_::{
        CallableParam, CallableParams, ParamSpecUsage, ParamType, StarParamType, StarStarParamType,
        StringSlice, Type, TypeVarLikes, TypedDict, TypedDictMember, Variance,
    },
};

pub trait Param<'x>: Copy + std::fmt::Debug {
    fn has_default(&self) -> bool;
    fn name(&self, db: &'x Database) -> Option<&str>;
    fn specific<'db: 'x>(&self, db: &'db Database) -> WrappedParamType<'x>;
    fn kind(&self, db: &Database) -> ParamKind;
}

pub fn matches_params(
    i_s: &InferenceState,
    matcher: &mut Matcher,
    params1: &CallableParams,
    params2: &CallableParams,
    type_vars2: Option<(&TypeVarLikes, PointLink)>,
    variance: Variance,
    skip_first_of_params2: bool,
) -> Match {
    if matcher.is_matching_reverse() {
        /*
        if type_vars2.is_none() {
            return matcher.match_reverse(|matcher| {
                matches_params(
                    i_s,
                    matcher,
                    params2,
                    params1,
                    type_vars2,
                    variance.invert(),
                    skip_first_of_params2,
                )
            });
        }
        */
        debug!("TODO should maybe be the line above");
    }

    use CallableParams::*;
    match (params1, params2) {
        (Simple(params1), Simple(params2)) => {
            if skip_first_of_params2 {
                matches_simple_params(
                    i_s,
                    matcher,
                    params1.iter(),
                    params2.iter().skip(1).peekable(),
                    variance,
                )
            } else {
                matches_simple_params(
                    i_s,
                    matcher,
                    params1.iter(),
                    params2.iter().peekable(),
                    variance,
                )
            }
        }
        (WithParamSpec(pre1, usage1), WithParamSpec(pre2, usage2)) => {
            if skip_first_of_params2 {
                todo!()
            }
            matcher.match_or_add_param_spec_against_param_spec(
                i_s, pre1, usage1, pre2, usage2, type_vars2, variance,
            )
        }
        (Any(_), _) => Match::new_true(),
        (Simple(params1), Any(cause)) => {
            for p in params1.iter() {
                if let Some(t) = p.type_.maybe_type() {
                    matcher.set_all_contained_type_vars_to_any(i_s, t, *cause);
                } else {
                    todo!()
                }
            }
            Match::new_true()
        }
        (WithParamSpec(pre, usage1), Any(cause)) => {
            for t in pre.iter() {
                matcher.set_all_contained_type_vars_to_any(i_s, t, *cause);
            }
            // TODO should probably set usage1 to any
            Match::new_true()
        }
        (WithParamSpec(types, param_spec), Simple(params2)) => {
            let mut params2 = params2.iter();
            if skip_first_of_params2 {
                params2.next();
            }
            matcher.match_or_add_param_spec(i_s, types, param_spec, params2, type_vars2, variance)
        }
        (Simple(_), WithParamSpec(..)) => Match::new_false(),
    }
}

pub fn matches_simple_params<'db: 'x + 'y, 'x, 'y, P1: Param<'x>, P2: Param<'y>>(
    i_s: &InferenceState<'db, '_>,
    matcher: &mut Matcher,
    mut params1: impl Iterator<Item = P1>,
    mut params2: Peekable<impl Iterator<Item = P2>>,
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
    for param1 in params1.by_ref() {
        if let Some(mut param2) = params2
            .peek()
            .or_else(|| unused_keyword_params.get(0))
            .copied()
        {
            if param1.has_default() && !param2.has_default() {
                return Match::new_false();
            }
            let specific1 = param1.specific(i_s.db);
            let specific2 = param2.specific(i_s.db);
            match &specific1 {
                WrappedParamType::PositionalOnly(t1) => match &specific2 {
                    WrappedParamType::PositionalOnly(t2)
                    | WrappedParamType::PositionalOrKeyword(t2) => {
                        matches &= match_(i_s, matcher, t1, t2)
                    }
                    WrappedParamType::Star(s2) => match s2 {
                        WrappedStar::ArbitraryLength(t2) => {
                            matches &= match_(i_s, matcher, t1, t2);
                            continue;
                        }
                        WrappedStar::ParamSpecArgs(u) => todo!(),
                    },
                    _ => return Match::new_false(),
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
                                    return Match::new_false();
                                }
                                if mismatched_name_pos_params1
                                    .iter()
                                    .any(|p1| p1.name(i_s.db) == name2)
                                {
                                    return Match::new_false();
                                }
                                mismatched_name_pos_params1.push(param1);
                                mismatched_name_pos_params2.push(param2);
                            } else {
                                return Match::new_false();
                            }
                        }
                        matches &= match_(i_s, matcher, t1, t2)
                    }
                    WrappedParamType::Star(WrappedStar::ArbitraryLength(s2)) => {
                        params2.next();
                        match params2.next().map(|p| p.specific(i_s.db)) {
                            Some(WrappedParamType::StarStar(WrappedStarStar::ValueType(
                                ref d2,
                            ))) => {
                                matches &=
                                    match_with_variance(i_s, matcher, s2, d2, Variance::Invariant);
                                matches &= match_(i_s, matcher, t1, s2);
                                for param1 in params1 {
                                    match &param1.specific(i_s.db) {
                                        WrappedParamType::PositionalOnly(t1)
                                        | WrappedParamType::PositionalOrKeyword(t1)
                                        | WrappedParamType::KeywordOnly(t1)
                                        | WrappedParamType::Star(WrappedStar::ArbitraryLength(
                                            t1,
                                        ))
                                        | WrappedParamType::StarStar(WrappedStarStar::ValueType(
                                            t1,
                                        )) => {
                                            // Since this is a *args, **kwargs signature we
                                            // just check that all annotations are matching.
                                            // TODO do we need to check both?
                                            matches &= match_(i_s, matcher, t1, d2);
                                            matches &= match_(i_s, matcher, t1, s2);
                                        }
                                        WrappedParamType::Star(WrappedStar::ParamSpecArgs(u)) => {
                                            todo!()
                                        }
                                        WrappedParamType::StarStar(
                                            WrappedStarStar::ParamSpecKwargs(u),
                                        ) => todo!(),
                                        WrappedParamType::StarStar(
                                            WrappedStarStar::UnpackTypedDict(u),
                                        ) => todo!(),
                                    }
                                }
                                return matches;
                            }
                            _ => return Match::new_false(),
                        }
                    }
                    WrappedParamType::PositionalOnly(t2)
                        if matcher.ignore_positional_param_names() =>
                    {
                        matches &= match_(i_s, matcher, t1, t2)
                    }
                    _ => return Match::new_false(),
                },
                WrappedParamType::KeywordOnly(t1) => match &specific2 {
                    WrappedParamType::StarStar(WrappedStarStar::ValueType(t2)) => {
                        matches &= match_(i_s, matcher, t1, t2);
                        continue;
                    }
                    WrappedParamType::StarStar(_) => return Match::new_false(),
                    _ => {
                        let mut found = false;
                        for (i, p2) in unused_keyword_params.iter().enumerate() {
                            if param1.name(i_s.db) == p2.name(i_s.db) {
                                match unused_keyword_params.remove(i).specific(i_s.db) {
                                    WrappedParamType::KeywordOnly(t2)
                                    | WrappedParamType::PositionalOrKeyword(t2) => {
                                        matches &= match_(i_s, matcher, t1, &t2);
                                    }
                                    _ => unreachable!(),
                                }
                                found = true;
                                break;
                            }
                        }
                        if !found {
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
                                return Match::new_false();
                            }
                        }
                    }
                },
                WrappedParamType::Star(s1) => match &specific2 {
                    WrappedParamType::Star(s2) => match (s1, s2) {
                        (WrappedStar::ArbitraryLength(t1), WrappedStar::ArbitraryLength(t2)) => {
                            matches &= match_(i_s, matcher, t1, t2)
                        }
                        (WrappedStar::ParamSpecArgs(u1), WrappedStar::ParamSpecArgs(u2)) => {
                            todo!()
                        }
                        (WrappedStar::ArbitraryLength(_), WrappedStar::ParamSpecArgs(_))
                        | (WrappedStar::ParamSpecArgs(_), WrappedStar::ArbitraryLength(_)) => {
                            todo!()
                        }
                    },
                    _ => return Match::new_false(),
                },
                WrappedParamType::StarStar(d1) => match specific2 {
                    WrappedParamType::StarStar(d2) => match (d1, d2) {
                        (WrappedStarStar::ValueType(t1), WrappedStarStar::ValueType(t2)) => {
                            matches &= match_(i_s, matcher, t1, &t2)
                        }
                        (
                            WrappedStarStar::ParamSpecKwargs(u1),
                            WrappedStarStar::ParamSpecKwargs(u2),
                        ) => todo!(),
                        (
                            WrappedStarStar::UnpackTypedDict(td1),
                            WrappedStarStar::UnpackTypedDict(td2),
                        ) => {
                            let td1 = td1.clone();
                            let mut check = |td_x: &TypedDict, td_y: &TypedDict| {
                                td_x.matches(i_s, matcher, &td_y, true)
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
                        _ => return Match::new_false(),
                    },
                    _ => return Match::new_false(),
                },
            };
            params2.next();
        } else {
            debug!("Params mismatch, because one side had less params: {param1:?}");
            return Match::new_false();
        }
    }
    for unused in unused_keyword_params {
        if !unused.has_default() {
            return Match::new_false();
        }
    }
    for param2 in params2 {
        if !param2.has_default()
            && !matches!(param2.kind(i_s.db), ParamKind::Star | ParamKind::StarStar)
        {
            return Match::new_false();
        }
    }
    matches
}

pub fn has_overlapping_params(
    i_s: &InferenceState,
    params1: &CallableParams,
    params2: &CallableParams,
) -> bool {
    match (params1, params2) {
        (CallableParams::Simple(params1), CallableParams::Simple(params2)) => {
            overload_has_overlapping_params(i_s, params1.iter(), params2.iter())
        }
        (CallableParams::WithParamSpec(_, _), CallableParams::WithParamSpec(_, _)) => todo!(),
        (CallableParams::Any(_), _) | (_, CallableParams::Any(_)) => todo!(),
        _ => todo!(),
    }
}

fn overload_has_overlapping_params<'db: 'x, 'x, P1: Param<'x>, P2: Param<'x>>(
    i_s: &InferenceState<'db, '_>,
    params1: impl Iterator<Item = P1>,
    params2: impl Iterator<Item = P2>,
) -> bool {
    #![allow(unreachable_code)]
    debug!("TODO this is not yet properly implemented and skipped in tests, see this commit");
    return false;
    let to_type = |db: &'db _, p2: P2| match p2.specific(db) {
        WrappedParamType::PositionalOnly(t2)
        | WrappedParamType::PositionalOrKeyword(t2)
        | WrappedParamType::KeywordOnly(t2)
        | WrappedParamType::Star(WrappedStar::ArbitraryLength(t2))
        | WrappedParamType::StarStar(WrappedStarStar::ValueType(t2)) => t2,
        WrappedParamType::Star(WrappedStar::ParamSpecArgs(u)) => todo!(),
        WrappedParamType::StarStar(WrappedStarStar::ParamSpecKwargs(u)) => todo!(),
        WrappedParamType::StarStar(WrappedStarStar::UnpackTypedDict(u)) => todo!(),
    };
    let check_type = |i_s: &InferenceState<'db, '_>, t1: Option<&Type>, p2: P2| {
        if let Some(t1) = t1 {
            if let Some(t2) = to_type(i_s.db, p2) {
                return t1.overlaps(i_s, &t2);
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
                        ParamKind::KeywordOnly => {
                            todo!()
                        }
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
                    .or_else(|| unused_keyword_params.get(0))
                    .copied()
                {
                    match param2.kind(db) {
                        ParamKind::PositionalOrKeyword => {
                            todo!()
                        }
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
            WrappedParamType::Star(WrappedStar::ArbitraryLength(t1)) => {
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
                todo!()
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
                StarParamType::ArbitraryLength(t) => {
                    WrappedStar::ArbitraryLength(Some(Cow::Borrowed(t)))
                }
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
}

pub struct InferrableParamIterator<'db, 'a, I, P, AI: Iterator> {
    db: &'db Database,
    arguments: AI,
    current_arg: Option<Argument<'db, 'a>>,
    params: I,
    pub unused_keyword_arguments: Vec<Argument<'db, 'a>>,
    current_starred_param: Option<P>,
    current_double_starred_param: Option<P>,
    pub too_many_positional_arguments: bool,
    arbitrary_length_handled: bool,
}

impl<'db, 'a, I, P, AI: Iterator<Item = Argument<'db, 'a>>>
    InferrableParamIterator<'db, 'a, I, P, AI>
{
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
        }
    }

    pub fn has_unused_keyword_arguments(&mut self) -> bool {
        !self.unused_keyword_arguments.is_empty()
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

    pub fn next_arg(&mut self) -> Option<Argument<'db, 'a>> {
        let arg = self.current_arg.take().or_else(|| self.arguments.next());
        if let Some(a) = &arg {
            if a.in_args_or_kwargs_and_arbitrary_len() {
                self.arbitrary_length_handled = false;
                self.current_arg = arg.clone();
            }
        }
        arg
    }

    fn maybe_exact_multi_arg(&mut self, is_keyword_arg: bool) -> Option<Argument<'db, 'a>> {
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
    AI: Iterator<Item = Argument<'db, 'a>>,
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
                while let Some(argument) = self.next_arg() {
                    if let Some(key) = argument.keyword_name(self.db) {
                        if let Some(member) = td.find_member(self.db, key) {
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
                            ArgumentKind::Inferred {
                                is_keyword: Some(None),
                                ..
                            }
                        ) {
                            return Some(InferrableParam {
                                param,
                                argument: ParamArgument::Argument(argument),
                            });
                        }
                    } else {
                        self.too_many_positional_arguments = true;
                    }
                }
            } else {
                if let Some(argument) = self
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
                            ArgumentKind::Inferred {
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
                            ArgumentKind::Positional { .. }
                            | ArgumentKind::Inferred {
                                is_keyword: None, ..
                            }
                            | ArgumentKind::InferredWithCustomAddIssue { .. }
                            | ArgumentKind::Comprehension { .. } => argument_with_index = Some(arg),
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
                        debug_assert!(matches!(
                            self.params.next().unwrap().specific(self.db),
                            WrappedParamType::StarStar(WrappedStarStar::ParamSpecKwargs(u)),
                        ));
                        return Some(InferrableParam {
                            param,
                            argument: ParamArgument::ParamSpecArgs(
                                u.clone(),
                                self.arguments.by_ref().collect(),
                            ),
                        });
                    }
                    _ => {
                        self.current_starred_param = Some(param);
                        return self.next();
                    }
                },
                ParamKind::StarStar => {
                    self.current_double_starred_param = Some(param);
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
}

#[derive(Debug)]
pub enum ParamArgument<'db, 'a> {
    None,
    Argument(Argument<'db, 'a>),
    MatchedUnpackedTypedDictMember {
        argument: Argument<'db, 'a>,
        type_: Type,
        name: StringSlice,
    },
    ParamSpecArgs(ParamSpecUsage, Box<[Argument<'db, 'a>]>),
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
    ArbitraryLength(Option<Cow<'a, Type>>),
    ParamSpecArgs(&'a ParamSpecUsage),
}

#[derive(Debug)]
pub enum WrappedStarStar<'a> {
    ValueType(Option<Cow<'a, Type>>),
    ParamSpecKwargs(&'a ParamSpecUsage),
    UnpackTypedDict(Rc<TypedDict>),
}
