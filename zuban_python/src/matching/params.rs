use parsa_python_ast::ParamKind;

use super::{Match, Matcher};
use crate::arguments::{Argument, ArgumentIterator, ArgumentKind, Arguments};
use crate::database::{CallableParam, CallableParams, Database, DbType, PointLink, Variance};
use crate::inference_state::InferenceState;
use crate::matching::Type;
use crate::utils::Peekable;
use crate::value::ParamWithArgument;

pub trait Param<'x>: Copy + std::fmt::Debug {
    fn has_default(&self) -> bool;
    fn name(&self, db: &'x Database) -> Option<&str>;
    fn annotation_type<'db: 'x>(&self, i_s: &mut InferenceState<'db, '_>) -> Option<Type<'x>>;
    fn func_annotation_link(&self) -> Option<PointLink> {
        // Can be None for Callable
        None
    }
    fn kind(&self, db: &Database) -> ParamKind;
}

pub fn matches_params<'db: 'x, 'x, P1: Param<'x>, P2: Param<'x>>(
    i_s: &mut InferenceState<'db, '_>,
    matcher: &mut Matcher,
    params1: Option<impl Iterator<Item = P1>>,
    params2: Option<impl Iterator<Item = P2>>,
    variance: Variance,
) -> Match {
    fn check_annotation<'db: 'x, 'x>(
        i_s: &mut InferenceState<'db, '_>,
        matcher: &mut Matcher,
        param1: impl Param<'x>,
        param2: impl Param<'x>,
        variance: Variance,
    ) -> Match {
        if let Some(t1) = param1.annotation_type(i_s) {
            if let Some(t2) = param2.annotation_type(i_s) {
                return t1.matches(i_s, matcher, &t2, variance);
            }
        }
        Match::new_true()
    }
    if let Some(mut params1) = params1 {
        if let Some(params2) = params2 {
            let mut params2 = Peekable::new(params2);
            let mut matches = Match::new_true();
            let mut unused_keyword_params: Vec<P2> = vec![];

            for param1 in params1.by_ref() {
                if let Some(mut param2) = params2
                    .peek()
                    .or_else(|| unused_keyword_params.get(0))
                    .copied()
                {
                    let pt1 = param1.kind(i_s.db);
                    let pt2 = param2.kind(i_s.db);
                    let matches_kind = match pt1 {
                        ParamKind::PositionalOnly => match pt2 {
                            ParamKind::PositionalOnly | ParamKind::PositionalOrKeyword => true,
                            ParamKind::Starred => {
                                let m = check_annotation(i_s, matcher, param1, param2, variance);
                                if !m.bool() {
                                    return m;
                                }
                                true
                            }
                            _ => false,
                        },
                        ParamKind::PositionalOrKeyword => {
                            if pt2 == ParamKind::Starred {
                                params2.next();
                                let maybe_kwargs = params2.next();
                                if let Some(maybe_kwargs) = maybe_kwargs {
                                    if maybe_kwargs.kind(i_s.db) != ParamKind::DoubleStarred
                                        || !check_annotation(
                                            i_s,
                                            matcher,
                                            param2,
                                            maybe_kwargs,
                                            Variance::Invariant,
                                        )
                                        .bool()
                                    {
                                        return Match::new_false();
                                    }
                                    for param1 in params1 {
                                        // Since this is a *args, **kwargs signature we just check
                                        // that all annotations are matching.
                                        matches &= check_annotation(
                                            i_s, matcher, param1, param2, variance,
                                        );
                                        matches &= check_annotation(
                                            i_s,
                                            matcher,
                                            param1,
                                            maybe_kwargs,
                                            variance,
                                        );
                                    }
                                    return matches;
                                } else {
                                    return Match::new_false();
                                }
                            }
                            pt1 == pt2 && param1.name(i_s.db) == param2.name(i_s.db)
                        }
                        ParamKind::KeywordOnly => match pt2 {
                            ParamKind::KeywordOnly | ParamKind::PositionalOrKeyword => {
                                let mut found = false;
                                for (i, p2) in unused_keyword_params.iter().enumerate() {
                                    if param1.name(i_s.db) == p2.name(i_s.db) {
                                        param2 = unused_keyword_params.remove(i);
                                        found = true;
                                        break;
                                    }
                                }
                                if !found {
                                    while match params2.peek() {
                                        Some(p2) => {
                                            matches!(
                                                p2.kind(i_s.db),
                                                ParamKind::KeywordOnly
                                                    | ParamKind::PositionalOrKeyword
                                            )
                                        }
                                        None => false,
                                    } {
                                        param2 = *params2.peek().unwrap();
                                        if param1.name(i_s.db) == param2.name(i_s.db) {
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
                                }
                                true
                            }
                            ParamKind::DoubleStarred => {
                                let m = check_annotation(i_s, matcher, param1, param2, variance);
                                if !m.bool() {
                                    return m;
                                }
                                continue;
                            }
                            _ => false,
                        },
                        ParamKind::Starred | ParamKind::DoubleStarred => pt1 == pt2,
                    };
                    params2.next();
                    if !matches_kind || param1.has_default() && !param2.has_default() {
                        return Match::new_false();
                    }
                    matches &= check_annotation(i_s, matcher, param1, param2, variance)
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
            return matches;
        }
    }
    // If there are no params, it means that anything is accepted, i.e. *args, **kwargs
    Match::new_true()
}

pub fn has_overlapping_params<'db>(
    i_s: &mut InferenceState<'db, '_>,
    params1: &CallableParams,
    params2: &CallableParams,
) -> bool {
    if let Some(params1) = params1 {
        if let Some(params2) = params2 {
            return overload_has_overlapping_params(i_s, params1.iter(), params2.iter());
        }
    }
    todo!()
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

    fn annotation_type<'db: 'x>(&self, i_s: &mut InferenceState<'db, '_>) -> Option<Type<'x>> {
        Some(Type::new(&self.db_type))
    }

    fn kind(&self, db: &Database) -> ParamKind {
        self.param_kind
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
