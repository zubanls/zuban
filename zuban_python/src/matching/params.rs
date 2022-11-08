use parsa_python_ast::ParamKind;

use super::{Match, Matcher};
use crate::arguments::{Argument, ArgumentIterator, ArgumentKind, Arguments};
use crate::database::{
    CallableParam, CallableParams, Database, DbType, DoubleStarredParamSpecific, ParamSpecific,
    PointLink, StarredParamSpecific, Variance,
};
use crate::debug;
use crate::inference_state::InferenceState;
use crate::matching::Type;
use crate::utils::Peekable;
use crate::value::ParamWithArgument;

pub trait Param<'x>: Copy + std::fmt::Debug {
    fn has_default(&self) -> bool;
    fn name(&self, db: &'x Database) -> Option<&str>;
    fn specific<'db: 'x>(&self, i_s: &mut InferenceState<'db, '_>) -> WrappedParamSpecific<'x>;
    fn kind(&self, db: &Database) -> ParamKind;
    fn func_annotation_link(&self) -> Option<PointLink> {
        // Can be None for Callable
        None
    }
}

pub fn matches_params(
    i_s: &mut InferenceState,
    matcher: &mut Matcher,
    params1: &CallableParams,
    params2: &CallableParams,
    variance: Variance,
    skip_first_of_params2: bool,
) -> Match {
    if matcher.is_matching_reverse() {
        debug!("TODO should probably be the line below");
        //return matcher.match_reverse(|matcher| matches_params(i_s, matcher, params2, params1, variance.invert(), skip_first_of_params2))
    }

    use CallableParams::*;
    match (params1, params2) {
        (Simple(params1), Simple(params2)) => {
            if skip_first_of_params2 {
                matches_simple_params(
                    i_s,
                    matcher,
                    params1.iter(),
                    params2.iter().skip(1),
                    variance,
                )
            } else {
                matches_simple_params(i_s, matcher, params1.iter(), params2.iter(), variance)
            }
        }
        (WithParamSpec(_, _), WithParamSpec(_, _)) => todo!(),
        (Any, _) | (_, Any) => Match::new_true(),
        (WithParamSpec(types, param_spec), Simple(_)) => {
            matcher.match_or_add_param_spec(i_s, types, param_spec, params2)
        }
        (Simple(_), WithParamSpec(..)) => {
            todo!()
        }
    }
}

pub fn matches_simple_params<'db: 'x, 'x, P1: Param<'x>, P2: Param<'x>>(
    i_s: &mut InferenceState<'db, '_>,
    matcher: &mut Matcher,
    mut params1: impl Iterator<Item = P1>,
    params2: impl Iterator<Item = P2>,
    variance: Variance,
) -> Match {
    let match_with_variance = |i_s, a: Option<Type>, b: Option<Type>, variance| {
        if let Some(a) = a.as_ref() {
            if let Some(b) = b.as_ref() {
                return a.matches(i_s, matcher, b, variance);
            }
        }
        Match::new_true()
    };

    let match_ = |i_s, a, b| match_with_variance(i_s, a, b, variance);

    let mut params2 = Peekable::new(params2);
    let mut unused_keyword_params: Vec<P2> = vec![];

    for param1 in params1.by_ref() {
        if let Some(mut param2) = params2
            .peek()
            .or_else(|| unused_keyword_params.get(0))
            .copied()
        {
            if param1.has_default() && !param2.has_default() {
                return Match::new_false();
            }
            let matches_kind = match param1.specific(i_s) {
                WrappedParamSpecific::PositionalOnly(t1) => match param2.specific(i_s) {
                    WrappedParamSpecific::PositionalOnly(t2)
                    | WrappedParamSpecific::PositionalOrKeyword(t2) => match_(i_s, t1, t2),
                    WrappedParamSpecific::Starred(s) => match s {
                        WrappedStarred::Type(t2) => todo!(),
                    },
                    _ => Match::new_false(),
                },
                WrappedParamSpecific::PositionalOrKeyword(t1) => match param2.specific(i_s) {
                    WrappedParamSpecific::PositionalOrKeyword(t2) => {
                        if param1.name(i_s.db) != param2.name(i_s.db) {
                            return Match::new_false();
                        }
                        match_(i_s, t1, t2)
                    }
                    WrappedParamSpecific::Starred(WrappedStarred::Type(s2)) => {
                        params2.next();
                        match params2.next().map(|p| p.specific(i_s)) {
                            Some(WrappedParamSpecific::DoubleStarred(
                                WrappedDoubleStarred::Type(d2),
                            )) => {
                                let mut m = match_with_variance(i_s, s2, d2, Variance::Invariant);
                                m &= match_(i_s, t1, s2);
                                for param1 in params1 {
                                    match param1.specific(i_s) {
                                        WrappedParamSpecific::PositionalOnly(t1)
                                        | WrappedParamSpecific::PositionalOrKeyword(t1)
                                        | WrappedParamSpecific::KeywordOnly(t1)
                                        | WrappedParamSpecific::Starred(WrappedStarred::Type(t1))
                                        | WrappedParamSpecific::DoubleStarred(
                                            WrappedDoubleStarred::Type(t1),
                                        ) => {
                                            // Since this is a *args, **kwargs signature we
                                            // just check that all annotations are matching.
                                            // TODO do we need to check both?
                                            m &= match_(i_s, t1, d2);
                                            m &= match_(i_s, t1, s2);
                                        }
                                    }
                                }
                                m
                            }
                            _ => Match::new_false(),
                        }
                    }
                    _ => Match::new_false(),
                },
                WrappedParamSpecific::KeywordOnly(t1) => match param2.specific(i_s) {
                    WrappedParamSpecific::KeywordOnly(t2)
                    | WrappedParamSpecific::PositionalOrKeyword(t2) => {
                        let mut found = false;
                        for (i, p2) in unused_keyword_params.iter().enumerate() {
                            if param1.name(i_s.db) == p2.name(i_s.db) {
                                param2 = unused_keyword_params.remove(i);
                                found = true;
                                break;
                            }
                        }
                        if found {
                            match_(i_s, t1, t2)
                        } else {
                            while match params2.peek() {
                                Some(p2) => {
                                    matches!(
                                        p2.kind(i_s.db),
                                        ParamKind::KeywordOnly | ParamKind::PositionalOrKeyword
                                    )
                                }
                                None => false,
                            } {
                                param2 = *params2.peek().unwrap();
                                if param1.name(i_s.db) == param2.name(i_s.db) {
                                    match param2.specific(i_s) {
                                        WrappedParamSpecific::PositionalOrKeyword(t2)
                                        | WrappedParamSpecific::KeywordOnly(t2) => {
                                            let m = match_(i_s, t1, t2);
                                            if !m.bool() {
                                                return m;
                                            }
                                        }
                                        _ => unreachable!(),
                                    }
                                    found = true;
                                    break;
                                } else {
                                    params2.next();
                                    unused_keyword_params.push(param2);
                                }
                            }
                            if !found {
                                return Match::new_false();
                            }
                            todo!();
                        }
                    }
                    WrappedParamSpecific::DoubleStarred(WrappedDoubleStarred::Type(t2)) => {
                        let m = match_(i_s, t1, t2);
                        if !m.bool() {
                            return m;
                        }
                        continue;
                    }
                    _ => Match::new_false(),
                },
                WrappedParamSpecific::Starred(s1) => match param2.specific(i_s) {
                    WrappedParamSpecific::Starred(s2) => match (s1, s2) {
                        (WrappedStarred::Type(t1), WrappedStarred::Type(t2)) => match_(i_s, t1, t2),
                    },
                    _ => Match::new_false(),
                },
                WrappedParamSpecific::DoubleStarred(d1) => match param2.specific(i_s) {
                    WrappedParamSpecific::DoubleStarred(d2) => match (d1, d2) {
                        (WrappedDoubleStarred::Type(t1), WrappedDoubleStarred::Type(t2)) => {
                            match_(i_s, t1, t2)
                        }
                    },
                    _ => Match::new_false(),
                },
            };
            if !matches_kind.bool() {
                return matches_kind;
            }
            params2.next();
        } else {
            return Match::new_false();
        }
    }
    if !unused_keyword_params.is_empty() {
        return Match::new_false();
    }
    for param2 in params2 {
        if !param2.has_default()
            && !matches!(
                param2.kind(i_s.db),
                ParamKind::Starred | ParamKind::DoubleStarred
            )
        {
            return Match::new_false();
        }
    }
    Match::new_true()
}

pub fn has_overlapping_params<'db>(
    i_s: &mut InferenceState<'db, '_>,
    params1: &CallableParams,
    params2: &CallableParams,
) -> bool {
    match (params1, params2) {
        (CallableParams::Simple(params1), CallableParams::Simple(params2)) => {
            overload_has_overlapping_params(i_s, params1.iter(), params2.iter())
        }
        (CallableParams::WithParamSpec(_, _), CallableParams::WithParamSpec(_, _)) => todo!(),
        (CallableParams::Any, _) | (_, CallableParams::Any) => todo!(),
        _ => todo!(),
    }
}

pub fn overload_has_overlapping_params<'db: 'x, 'x, P1: Param<'x>, P2: Param<'x>>(
    i_s: &mut InferenceState<'db, '_>,
    params1: impl Iterator<Item = P1>,
    params2: impl Iterator<Item = P2>,
) -> bool {
    let check_type = |i_s: &mut _, param1: P1, param2: P2| {
        if let Some(t1) = param1.annotation_type(i_s) {
            if let Some(t2) = param2.annotation_type(i_s) {
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
                if let Some(t) = p.annotation_type(&mut InferenceState::new(db)) {
                    if matches!(t.maybe_db_type(), Some(DbType::Any)) {
                        had_any_fallback_with_default = true;
                    }
                }
            }
            !has_default
        })
        .peekable();
    let mut unused_keyword_params: Vec<P2> = vec![];
    for param1 in params1.filter(|p| !p.has_default()) {
        match param1.kind(db) {
            ParamKind::PositionalOrKeyword | ParamKind::PositionalOnly => {
                if let Some(param2) = params2.peek() {
                    if !check_type(i_s, param1, *param2) {
                        return false;
                    }
                    match param2.kind(db) {
                        ParamKind::PositionalOrKeyword | ParamKind::PositionalOnly => {
                            params2.next(); // We only peeked.
                        }
                        ParamKind::KeywordOnly => {
                            todo!()
                        }
                        ParamKind::Starred => (),
                        ParamKind::DoubleStarred => (),
                    }
                } else {
                    return false;
                }
            }
            ParamKind::KeywordOnly => {
                if let Some(param2) = params2.peek() {
                    if param2.kind(db) == ParamKind::Starred {
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
                        ParamKind::DoubleStarred => (),
                        _ => return false,
                    }
                    if !check_type(i_s, param1, param2) {
                        return false;
                    }
                } else {
                    return false;
                }
            }
            ParamKind::Starred => {
                while match params2.peek() {
                    Some(p) => !matches!(
                        p.kind(db),
                        ParamKind::KeywordOnly | ParamKind::DoubleStarred
                    ),
                    None => false,
                } {
                    if let Some(param2) = params2.next() {
                        if !check_type(i_s, param1, param2) {
                            return false;
                        }
                    }
                }
            }
            ParamKind::DoubleStarred => {
                for param2 in params2 {
                    if !check_type(i_s, param1, param2) {
                        return false;
                    }
                }
                return !had_any_fallback_with_default;
            }
        }
    }
    for param2 in params2 {
        if !matches!(
            param2.kind(db),
            ParamKind::Starred | ParamKind::DoubleStarred
        ) {
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
        self.name.map(|n| n.as_str(db))
    }

    fn specific<'db: 'x>(&self, i_s: &mut InferenceState<'db, '_>) -> WrappedParamSpecific<'x> {
        match &self.param_specific {
            ParamSpecific::PositionalOnly(t) => {
                WrappedParamSpecific::PositionalOnly(Some(Type::new(t)))
            }
            ParamSpecific::PositionalOrKeyword(t) => {
                WrappedParamSpecific::PositionalOrKeyword(Some(Type::new(t)))
            }
            ParamSpecific::KeywordOnly(t) => WrappedParamSpecific::KeywordOnly(Some(Type::new(t))),
            ParamSpecific::Starred(s) => WrappedParamSpecific::Starred(match s {
                StarredParamSpecific::Type(t) => WrappedStarred::Type(Some(Type::new(t))),
            }),
            ParamSpecific::DoubleStarred(s) => WrappedParamSpecific::DoubleStarred(match s {
                DoubleStarredParamSpecific::Type(t) => {
                    WrappedDoubleStarred::Type(Some(Type::new(t)))
                }
            }),
        }
    }

    fn kind(&self, db: &Database) -> ParamKind {
        self.param_specific.param_kind()
    }
}

pub struct InferrableParamIterator2<'db, 'a, I, P> {
    db: &'db Database,
    pub arguments: Peekable<ArgumentIterator<'db, 'a>>,
    params: I,
    pub unused_keyword_arguments: Vec<Argument<'db, 'a>>,
    current_starred_param: Option<P>,
    current_double_starred_param: Option<P>,
    pub too_many_positional_arguments: bool,
}

impl<'db, 'a, I, P> InferrableParamIterator2<'db, 'a, I, P> {
    pub fn new(db: &'db Database, params: I, arguments: &'a dyn Arguments<'db>) -> Self {
        Self {
            db,
            arguments: Peekable::new(arguments.iter_arguments()),
            params,
            unused_keyword_arguments: vec![],
            current_starred_param: None,
            current_double_starred_param: None,
            too_many_positional_arguments: false,
        }
    }

    pub fn has_unused_keyword_arguments(&mut self) -> bool {
        !self.unused_keyword_arguments.is_empty()
    }

    pub fn has_unused_arguments(&mut self) -> bool {
        while let Some(arg) = self.arguments.peek() {
            if arg.in_args_or_kwargs_and_arbitrary_len() {
                self.arguments.next();
                self.arguments.as_inner_mut().drop_args_kwargs_iterator()
            } else {
                return true;
            }
        }
        false
    }
}

impl<'db: 'x, 'a, 'x, I, P> Iterator for InferrableParamIterator2<'db, 'a, I, P>
where
    I: Iterator<Item = P>,
    P: Param<'x>,
{
    type Item = InferrableParam2<'db, 'a, P>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(param) = self.current_starred_param {
            if let Some(argument) = self.arguments.next_if(|arg| !arg.is_keyword_argument()) {
                if argument.in_args_or_kwargs_and_arbitrary_len() {
                    self.arguments.as_inner_mut().drop_args_kwargs_iterator()
                }
                return Some(InferrableParam2 {
                    param,
                    argument: Some(argument),
                });
            } else {
                self.current_starred_param = None;
            }
        }
        if let Some(param) = self.current_double_starred_param {
            if let Some(argument) = self.arguments.next_if(|arg| arg.is_keyword_argument()) {
                if argument.in_args_or_kwargs_and_arbitrary_len() {
                    self.arguments.as_inner_mut().drop_args_kwargs_iterator()
                }
                return Some(InferrableParam2 {
                    param,
                    argument: Some(argument),
                });
            } else {
                self.current_double_starred_param = None;
            }
        }
        let check_unused = |self_: &mut Self, param: P| {
            for (i, unused) in self_.unused_keyword_arguments.iter().enumerate() {
                match &unused.kind {
                    ArgumentKind::Keyword { key, .. } => {
                        if Some(*key) == param.name(self_.db) {
                            return Some(InferrableParam2 {
                                param,
                                argument: Some(self_.unused_keyword_arguments.remove(i)),
                            });
                        }
                    }
                    _ => unreachable!(),
                }
            }
            None
        };
        self.params.next().and_then(|param| {
            let mut argument_with_index = None;
            match param.kind(self.db) {
                ParamKind::PositionalOrKeyword => {
                    for arg in &mut self.arguments {
                        match arg.kind {
                            ArgumentKind::Keyword { key, .. } => {
                                if Some(key) == param.name(self.db) {
                                    argument_with_index = Some(arg);
                                    break;
                                } else {
                                    self.unused_keyword_arguments.push(arg);
                                }
                            }
                            _ => {
                                argument_with_index = Some(arg);
                                break;
                            }
                        }
                    }
                    if argument_with_index.is_none() {
                        if let Some(p) = check_unused(self, param) {
                            return Some(p);
                        }
                    }
                }
                ParamKind::KeywordOnly => {
                    while let Some(arg) = self.arguments.next() {
                        match arg.kind {
                            ArgumentKind::Keyword { key, .. } => {
                                if Some(key) == param.name(self.db) {
                                    argument_with_index = Some(arg);
                                    break;
                                } else {
                                    self.unused_keyword_arguments.push(arg);
                                }
                            }
                            _ => {
                                if arg.in_args_or_kwargs_and_arbitrary_len() {
                                    self.arguments.as_inner_mut().drop_args_kwargs_iterator()
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
                    argument_with_index = self.arguments.next();
                    if let Some(ref arg) = argument_with_index {
                        match arg.kind {
                            ArgumentKind::Positional { .. } | ArgumentKind::Inferred { .. } => (),
                            ArgumentKind::Keyword { .. } => {
                                self.unused_keyword_arguments
                                    .push(argument_with_index.take().unwrap());
                            }
                            _ => todo!("{arg:?}"),
                        }
                    }
                }
                ParamKind::Starred => {
                    self.current_starred_param = Some(param);
                    return self.next();
                }
                ParamKind::DoubleStarred => {
                    self.current_double_starred_param = Some(param);
                    return self.next();
                }
            }
            Some(
                argument_with_index
                    .map(|a| InferrableParam2 {
                        param,
                        argument: Some(a),
                    })
                    .unwrap_or_else(|| InferrableParam2 {
                        param,
                        argument: None,
                    }),
            )
        })
    }
}

#[derive(Debug)]
pub struct InferrableParam2<'db, 'a, P> {
    pub param: P,
    pub argument: Option<Argument<'db, 'a>>,
}

impl<'db, 'a, P> ParamWithArgument<'db, 'a> for InferrableParam2<'db, 'a, P> {
    fn human_readable_argument_index(&self) -> String {
        self.argument.as_ref().unwrap().human_readable_index()
    }
}

pub enum WrappedParamSpecific<'a> {
    PositionalOnly(Option<Type<'a>>),
    PositionalOrKeyword(Option<Type<'a>>),
    KeywordOnly(Option<Type<'a>>),
    Starred(WrappedStarred<'a>),
    DoubleStarred(WrappedDoubleStarred<'a>),
}

pub enum WrappedStarred<'a> {
    Type(Option<Type<'a>>),
}

pub enum WrappedDoubleStarred<'a> {
    Type(Option<Type<'a>>),
}
