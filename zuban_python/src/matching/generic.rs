use std::borrow::Cow;

use super::{matches_params, FormatData, Match, Matcher, ParamsStyle};
use crate::{
    database::Database,
    inference_state::InferenceState,
    type_::{
        format_callable_params, match_tuple_type_arguments, CallableParams, GenericItem,
        ParamSpecArgument, Type, TypeArguments, TypeVarLike, Variance,
    },
};

#[derive(Debug)]
pub enum Generic<'a> {
    TypeArgument(Cow<'a, Type>),
    TypeVarTuple(Cow<'a, TypeArguments>),
    ParamSpecArgument(Cow<'a, ParamSpecArgument>),
}

impl<'a> Generic<'a> {
    pub fn new(g: &'a GenericItem) -> Self {
        match g {
            GenericItem::TypeArgument(t) => Self::TypeArgument(Cow::Borrowed(t)),
            GenericItem::TypeArguments(args) => Self::TypeVarTuple(Cow::Borrowed(args)),
            GenericItem::ParamSpecArgument(params) => {
                Self::ParamSpecArgument(Cow::Borrowed(params))
            }
        }
    }

    pub fn owned(g: GenericItem) -> Self {
        match g {
            GenericItem::TypeArgument(t) => Self::TypeArgument(Cow::Owned(t)),
            GenericItem::TypeArguments(args) => Self::TypeVarTuple(Cow::Owned(args)),
            GenericItem::ParamSpecArgument(params) => Self::ParamSpecArgument(Cow::Owned(params)),
        }
    }

    pub fn into_generic_item(self, db: &Database) -> GenericItem {
        match self {
            Self::TypeArgument(t) => GenericItem::TypeArgument(t.into_owned()),
            Self::TypeVarTuple(ts) => GenericItem::TypeArguments(ts.into_owned()),
            Self::ParamSpecArgument(params) => GenericItem::ParamSpecArgument(params.into_owned()),
        }
    }

    pub fn format(&self, format_data: &FormatData) -> Option<Box<str>> {
        match self {
            Self::TypeArgument(t) => Some(t.format(format_data)),
            Self::TypeVarTuple(ts) => ts.format(format_data),
            Self::ParamSpecArgument(args) => Some(match &args.params {
                CallableParams::Simple(params) => format!(
                    "[{}]",
                    &format_callable_params(format_data, None, false, params.iter(), false)
                )
                .into(),
                CallableParams::Any(_) => Box::from("Any"),
                CallableParams::WithParamSpec(..) => {
                    args.params.format(format_data, ParamsStyle::CallableParams)
                }
            }),
        }
    }

    pub fn matches(
        &self,
        i_s: &InferenceState,
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
                    match_tuple_type_arguments(i_s, matcher, &ts1.args, &ts2.args, variance)
                }
                _ => todo!(),
            },
            Self::ParamSpecArgument(p1) => match other {
                Self::ParamSpecArgument(p2) => matches_params(
                    i_s,
                    matcher,
                    &p1.params,
                    &p2.params,
                    p2.type_vars
                        .as_ref()
                        .map(|t| (&t.type_vars, t.in_definition)),
                    variance,
                    false,
                ),
                _ => todo!(),
            },
        }
    }

    pub fn overlaps(self, i_s: &InferenceState, other: Self) -> bool {
        match self {
            Self::TypeArgument(t1) => match other {
                Self::TypeArgument(ref t2) => t1.overlaps(i_s, t2),
                _ => todo!(),
            },
            Self::TypeVarTuple(_) => match other {
                Self::TypeVarTuple(ref t2) => todo!(),
                _ => todo!(),
            },
            Self::ParamSpecArgument(params) => todo!(),
        }
    }

    pub fn expect_type_argument(self) -> Cow<'a, Type> {
        match self {
            Self::TypeArgument(t) => t,
            _ => unreachable!(),
        }
    }

    pub fn expect_type_arguments(self) -> Cow<'a, TypeArguments> {
        match self {
            Self::TypeVarTuple(ts) => ts,
            _ => unreachable!(),
        }
    }

    pub fn maybe_simple_type_var_like(&self) -> Option<TypeVarLike> {
        match self {
            Self::TypeArgument(t) => match t.as_ref() {
                Type::TypeVar(t) => Some(TypeVarLike::TypeVar(t.type_var.clone())),
                _ => None,
            },
            Self::TypeVarTuple(ts) => todo!(),
            Self::ParamSpecArgument(params) => match &params.params {
                CallableParams::WithParamSpec(_, p) => {
                    Some(TypeVarLike::ParamSpec(p.param_spec.clone()))
                }
                _ => None,
            },
        }
    }

    pub fn merge_matching_parts(self, db: &Database, other: Self) -> GenericItem {
        match self {
            Self::TypeArgument(t1) => {
                let Self::TypeArgument(t2) = other else {
                    unreachable!()
                };
                GenericItem::TypeArgument(t1.merge_matching_parts(db, &t2))
            }
            Self::TypeVarTuple(ts1) => {
                let Self::TypeVarTuple(ts2) = other else {
                    unreachable!()
                };
                GenericItem::TypeArguments(TypeArguments::new(
                    ts1.args.merge_matching_parts(db, &ts2.args),
                ))
            }
            Self::ParamSpecArgument(params) => todo!(),
        }
    }
}
