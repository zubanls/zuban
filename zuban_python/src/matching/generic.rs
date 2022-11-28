use std::borrow::Cow;

use super::{match_tuple_type_arguments, matches_params, FormatData, Match, Matcher, Type};
use crate::database::{CallableParams, GenericItem, TypeArguments, Variance};
use crate::inference_state::InferenceState;

#[derive(Debug)]
pub enum Generic<'a> {
    TypeArgument(Type<'a>),
    TypeVarTuple(Cow<'a, TypeArguments>),
    CallableParams(Cow<'a, CallableParams>),
}

impl<'a> Generic<'a> {
    pub fn new(g: &'a GenericItem) -> Self {
        match g {
            GenericItem::TypeArgument(t) => Self::TypeArgument(Type::new(t)),
            GenericItem::TypeArguments(args) => Self::TypeVarTuple(Cow::Borrowed(args)),
            GenericItem::CallableParams(params) => Self::CallableParams(Cow::Borrowed(params)),
        }
    }

    pub fn owned(g: GenericItem) -> Self {
        match g {
            GenericItem::TypeArgument(t) => Self::TypeArgument(Type::owned(t)),
            GenericItem::TypeArguments(args) => Self::TypeVarTuple(Cow::Owned(args)),
            GenericItem::CallableParams(params) => Self::CallableParams(Cow::Owned(params)),
        }
    }

    pub fn into_generic_item(self, i_s: &mut InferenceState) -> GenericItem {
        match self {
            Self::TypeArgument(t) => GenericItem::TypeArgument(t.into_db_type(i_s)),
            Self::TypeVarTuple(ts) => GenericItem::TypeArguments(ts.into_owned()),
            Self::CallableParams(params) => GenericItem::CallableParams(params.into_owned()),
        }
    }

    pub fn format(&self, format_data: &FormatData) -> Box<str> {
        match self {
            Self::TypeArgument(t) => t.format(format_data),
            Self::TypeVarTuple(ts) => ts.format(format_data),
            Self::CallableParams(params) => params.format(format_data, true),
        }
    }

    pub fn matches(
        &self,
        i_s: &mut InferenceState,
        matcher: &mut Matcher,
        other: &Self,
        variance: Variance,
    ) -> Match {
        if matcher.is_matching_reverse() {
            return matcher
                .match_reverse(|matcher| other.matches(i_s, matcher, self, variance.invert()));
        }
        match self {
            Self::TypeArgument(t1) => match other {
                Self::TypeArgument(ref t2) => t1.matches(i_s, matcher, t2, variance),
                _ => todo!(),
            },
            Self::TypeVarTuple(ts1) => match other {
                Self::TypeVarTuple(ref ts2) => {
                    if matcher.has_type_var_matcher() {
                        if let Some(ts) = ts1.args.has_type_var_tuple() {
                            return matcher.match_type_var_tuple(i_s, ts, &ts2.args, variance);
                        }
                    }
                    match_tuple_type_arguments(i_s, matcher, &ts1.args, &ts2.args, variance)
                }
                _ => todo!(),
            },
            Self::CallableParams(params1) => match other {
                Self::CallableParams(params2) => {
                    matches_params(i_s, matcher, params1, params2, variance, false)
                }
                _ => todo!(),
            },
        }
    }

    pub fn overlaps(self, i_s: &mut InferenceState, other: Self) -> bool {
        match self {
            Self::TypeArgument(t1) => match other {
                Self::TypeArgument(ref t2) => t1.overlaps(i_s, t2),
                _ => todo!(),
            },
            Self::TypeVarTuple(_) => match other {
                Self::TypeVarTuple(ref t2) => todo!(),
                _ => todo!(),
            },
            Self::CallableParams(params) => todo!(),
        }
    }

    pub fn expect_type_argument(self) -> Type<'a> {
        match self {
            Self::TypeArgument(t) => t,
            _ => todo!(),
        }
    }
}
