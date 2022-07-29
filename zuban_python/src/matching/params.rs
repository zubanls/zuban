use parsa_python_ast::ParamType;

use super::{Match, TypeVarMatcher};
use crate::arguments::{Argument, ArgumentIterator};
use crate::database::{CallableParam, Variance};
use crate::inference_state::InferenceState;
use crate::matching::Type;
use crate::value::ParamWithArgument;

pub trait Param<'db, 'x>: Copy + std::fmt::Debug {
    fn has_default(&self) -> bool;
    fn name(&self) -> Option<&str>;
    fn annotation_type(&self, i_s: &mut InferenceState<'db, '_>) -> Option<Type<'db, 'x>>;
    fn param_type(&self) -> ParamType;
}

pub fn matches_params<'db: 'x, 'x>(
    i_s: &mut InferenceState<'db, '_>,
    mut matcher: Option<&mut TypeVarMatcher<'db, '_>>,
    params1: Option<impl Iterator<Item = impl Param<'db, 'x>>>,
    params2: Option<impl Iterator<Item = impl Param<'db, 'x>>>,
) -> Match {
    if let Some(params1) = params1 {
        if let Some(mut params2) = params2 {
            let mut matches = Match::True;
            for param1 in params1 {
                if let Some(param2) = params2.next() {
                    let pt1 = param1.param_type();
                    let pt2 = param2.param_type();
                    if !(pt1 == pt2
                        || pt1 == ParamType::PositionalOnly
                            && pt2 == ParamType::PositionalOrKeyword
                        // TODO This is not good enough, there might be Callable[int, int] against *int
                        || pt1 == ParamType::PositionalOnly && pt2 == ParamType::Starred)
                    {
                        return Match::False;
                    }
                    if param1.has_default() && !param2.has_default() {
                        return Match::False;
                    }
                    if matches!(
                        param1.param_type(),
                        ParamType::PositionalOrKeyword | ParamType::KeywordOnly
                    ) && param1.name() != param2.name()
                    {
                        return Match::False;
                    }
                    if let Some(t1) = param1.annotation_type(i_s) {
                        if let Some(t2) = param2.annotation_type(i_s) {
                            matches &= t1.matches(
                                i_s,
                                matcher.as_deref_mut(),
                                &t2,
                                Variance::Contravariant,
                            )
                        }
                    }
                } else {
                    return Match::False;
                }
            }
            if params2.next().is_some() {
                return Match::False;
            }
            return matches;
        }
    }
    // If there are no params, it means that anything is accepted, i.e. *args, **kwargs
    Match::True
}

pub fn has_overlapping_params<'db: 'x, 'x>(
    i_s: &mut InferenceState<'db, '_>,
    params1: Option<impl Iterator<Item = impl Param<'db, 'x>>>,
    params2: Option<impl Iterator<Item = impl Param<'db, 'x>>>,
) -> bool {
    if let Some(params1) = params1 {
        if let Some(params2) = params2 {
            return overload_has_overlapping_params(i_s, params1, params2);
        }
    }
    todo!()
}
pub fn overload_has_overlapping_params<'db: 'x, 'x, P1: Param<'db, 'x>, P2: Param<'db, 'x>>(
    i_s: &mut InferenceState<'db, '_>,
    params1: impl Iterator<Item = P1>,
    params2: impl Iterator<Item = P2>,
) -> bool {
    let mut check_type = |param1: P1, param2: P2| {
        if let Some(t1) = param1.annotation_type(i_s) {
            if let Some(t2) = param2.annotation_type(i_s) {
                return t1.overlaps(i_s, &t2);
            }
        }
        true
    };
    // Get rid of defaults first, because they always overlap.
    let mut params2 = params2.filter(|p| !p.has_default()).peekable();
    for param1 in params1.filter(|p| !p.has_default()) {
        match param1.param_type() {
            ParamType::PositionalOrKeyword | ParamType::PositionalOnly => {
                if let Some(param2) = params2.peek() {
                    if !check_type(param1, *param2) {
                        return false;
                    }
                    match param2.param_type() {
                        ParamType::PositionalOrKeyword | ParamType::PositionalOnly => {
                            params2.next(); // We only peeked.
                        }
                        ParamType::KeywordOnly => {
                            todo!()
                        }
                        ParamType::Starred => (),
                        ParamType::DoubleStarred => (),
                    }
                } else {
                    return false;
                }
            }
            ParamType::KeywordOnly => {
                if let Some(param2) = params2.peek() {
                    if param2.param_type() == ParamType::Starred {
                        params2.next();
                    }
                }
                if let Some(param2) = params2.peek() {
                    if !check_type(param1, *param2) {
                        return false;
                    }
                    match param2.param_type() {
                        ParamType::PositionalOrKeyword => {
                            todo!()
                        }
                        ParamType::PositionalOnly => todo!(),
                        ParamType::Starred => {
                            todo!()
                        }
                        ParamType::KeywordOnly => {
                            todo!()
                        }
                        ParamType::DoubleStarred => (),
                    }
                } else {
                    return false;
                }
            }
            ParamType::Starred => {
                while match params2.peek() {
                    Some(p) => !matches!(
                        p.param_type(),
                        ParamType::KeywordOnly | ParamType::DoubleStarred
                    ),
                    None => false,
                } {
                    if let Some(param2) = params2.next() {
                        if !check_type(param1, param2) {
                            return false;
                        }
                    }
                }
            }
            ParamType::DoubleStarred => {
                for param2 in params2 {
                    if !check_type(param1, param2) {
                        return false;
                    }
                }
                return true;
            }
        }
    }
    for param2 in params2 {
        if !matches!(
            param2.param_type(),
            ParamType::Starred | ParamType::DoubleStarred
        ) {
            return false;
        }
    }
    true
}

impl<'db, 'x> Param<'db, 'x> for &'x CallableParam {
    fn has_default(&self) -> bool {
        false
    }

    fn name(&self) -> Option<&str> {
        None
    }

    fn annotation_type(&self, i_s: &mut InferenceState<'db, '_>) -> Option<Type<'db, 'x>> {
        Some(Type::from_db_type(i_s.db, &self.db_type))
    }

    fn param_type(&self) -> ParamType {
        self.param_type
    }
}

pub struct InferrableParamIterator2<'db, 'a, I, P> {
    pub arguments: std::iter::Peekable<ArgumentIterator<'db, 'a>>,
    params: I,
    pub unused_keyword_arguments: Vec<Argument<'db, 'a>>,
    current_starred_param: Option<P>,
    current_double_starred_param: Option<P>,
    pub too_many_positional_arguments: bool,
}

impl<'db, 'a, I, P> InferrableParamIterator2<'db, 'a, I, P> {
    pub fn new(params: I, arguments: std::iter::Peekable<ArgumentIterator<'db, 'a>>) -> Self {
        Self {
            arguments,
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
}

impl<'db, 'a, 'x, I: Iterator<Item = P>, P: Param<'db, 'x>> Iterator
    for InferrableParamIterator2<'db, 'a, I, P>
{
    type Item = InferrableParam2<'db, 'a, P>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(param) = self.current_starred_param {
            if let Some(argument) = self.arguments.next_if(|arg| !arg.is_keyword_argument()) {
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
                return Some(InferrableParam2 {
                    param,
                    argument: Some(argument),
                });
            } else {
                self.current_double_starred_param = None;
            }
        }
        self.params.next().and_then(|param| {
            for (i, unused) in self.unused_keyword_arguments.iter().enumerate() {
                match unused {
                    Argument::Keyword(name, reference) => {
                        if Some(*name) == param.name() {
                            return Some(InferrableParam2 {
                                param,
                                argument: Some(self.unused_keyword_arguments.remove(i)),
                            });
                        }
                    }
                    _ => unreachable!(),
                }
            }
            let mut argument = None;
            match param.param_type() {
                ParamType::PositionalOrKeyword => {
                    for arg in &mut self.arguments {
                        match arg {
                            Argument::Keyword(name, reference) => {
                                if Some(name) == param.name() {
                                    argument = Some(arg);
                                    break;
                                } else {
                                    self.unused_keyword_arguments.push(arg);
                                }
                            }
                            _ => {
                                argument = Some(arg);
                                break;
                            }
                        }
                    }
                }
                ParamType::KeywordOnly => {
                    for arg in &mut self.arguments {
                        match arg {
                            Argument::Keyword(name, reference) => {
                                if Some(name) == param.name() {
                                    argument = Some(arg);
                                    break;
                                } else {
                                    self.unused_keyword_arguments.push(arg);
                                }
                            }
                            _ => self.too_many_positional_arguments = true,
                        }
                    }
                }
                ParamType::PositionalOnly => {
                    argument = self.arguments.next();
                    if let Some(arg) = argument {
                        match arg {
                            Argument::Positional(_, _) => (),
                            Argument::Keyword(_, _) => {
                                self.unused_keyword_arguments.push(arg);
                                argument = None;
                            }
                            _ => todo!(),
                        }
                    }
                }
                ParamType::Starred => {
                    self.current_starred_param = Some(param);
                    return self.next();
                }
                ParamType::DoubleStarred => {
                    self.current_double_starred_param = Some(param);
                    return self.next();
                }
            }
            Some(InferrableParam2 { param, argument })
        })
    }
}

#[derive(Debug)]
pub struct InferrableParam2<'db, 'a, P> {
    pub param: P,
    pub argument: Option<Argument<'db, 'a>>,
}

impl<'db, 'a, P> ParamWithArgument<'db, 'a> for InferrableParam2<'db, 'a, P> {
    fn argument_index(&self) -> String {
        self.argument.as_ref().unwrap().index()
    }
}
