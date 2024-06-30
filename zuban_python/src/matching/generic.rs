use std::borrow::Cow;

use super::{matches_params_with_variance, Match, Matcher};
use crate::{
    database::Database,
    format_data::{FormatData, ParamsStyle},
    inference_state::InferenceState,
    type_::{
        format_callable_params, format_params_as_param_spec, match_tuple_type_arguments,
        CallableParams, GenericItem, ParamSpecArg, TupleArgs, Type, TypeArgs, TypeVarLike,
        Variance,
    },
};

#[derive(Debug)]
pub enum Generic<'a> {
    TypeArg(Cow<'a, Type>),
    TypeArgs(Cow<'a, TypeArgs>),
    ParamSpecArg(Cow<'a, ParamSpecArg>),
}

impl<'a> Generic<'a> {
    pub fn new(g: &'a GenericItem) -> Self {
        match g {
            GenericItem::TypeArg(t) => Self::TypeArg(Cow::Borrowed(t)),
            GenericItem::TypeArgs(args) => Self::TypeArgs(Cow::Borrowed(args)),
            GenericItem::ParamSpecArg(params) => Self::ParamSpecArg(Cow::Borrowed(params)),
        }
    }

    pub fn owned(g: GenericItem) -> Self {
        match g {
            GenericItem::TypeArg(t) => Self::TypeArg(Cow::Owned(t)),
            GenericItem::TypeArgs(args) => Self::TypeArgs(Cow::Owned(args)),
            GenericItem::ParamSpecArg(params) => Self::ParamSpecArg(Cow::Owned(params)),
        }
    }

    pub fn into_generic_item(self, db: &Database) -> GenericItem {
        match self {
            Self::TypeArg(t) => GenericItem::TypeArg(t.into_owned()),
            Self::TypeArgs(ts) => GenericItem::TypeArgs(ts.into_owned()),
            Self::ParamSpecArg(params) => GenericItem::ParamSpecArg(params.into_owned()),
        }
    }

    pub fn format(&self, format_data: &FormatData) -> Option<Box<str>> {
        match self {
            Self::TypeArg(t) => Some(t.format(format_data)),
            Self::TypeArgs(ts) => ts.format(format_data),
            Self::ParamSpecArg(args) => Some(match &args.params {
                CallableParams::Simple {
                    params,
                    format_as_param_spec,
                } => {
                    if *format_as_param_spec {
                        format_params_as_param_spec(format_data, params)
                    } else {
                        format!(
                            "[{}]",
                            &format_callable_params(format_data, false, params.iter(), false)
                        )
                        .into()
                    }
                }
                CallableParams::Any(_) => Box::from("Any"),
                CallableParams::Never(_) => Box::from("Never"),
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
            Self::TypeArg(t1) => match other {
                Self::TypeArg(ref t2) => t1.matches(i_s, matcher, t2, variance),
                _ => unreachable!(),
            },
            Self::TypeArgs(ts1) => match other {
                Self::TypeArgs(ref ts2) => {
                    match_tuple_type_arguments(i_s, matcher, &ts1.args, &ts2.args, variance)
                }
                _ => unreachable!(),
            },
            Self::ParamSpecArg(p1) => match other {
                Self::ParamSpecArg(p2) => {
                    matches_params_with_variance(i_s, matcher, &p1.params, &p2.params, variance)
                }
                _ => unreachable!(),
            },
        }
    }

    pub fn overlaps(self, i_s: &InferenceState, matcher: &mut Matcher, other: Self) -> bool {
        match self {
            Self::TypeArg(t1) => match other {
                Self::TypeArg(ref t2) => t1.overlaps(i_s, matcher, t2),
                _ => unreachable!(),
            },
            Self::TypeArgs(_) => match other {
                Self::TypeArgs(ref t2) => todo!(),
                _ => unreachable!(),
            },
            Self::ParamSpecArg(spec_args1) => match other {
                // I'm not sure why Mypy decided that ParamSpecs always overlap.
                Self::ParamSpecArg(spec_args2) => true,
                _ => unreachable!(),
            },
        }
    }

    pub fn expect_type_argument(self) -> Cow<'a, Type> {
        match self {
            Self::TypeArg(t) => t,
            _ => unreachable!(),
        }
    }

    pub fn expect_type_arguments(self) -> Cow<'a, TypeArgs> {
        match self {
            Self::TypeArgs(ts) => ts,
            _ => unreachable!(),
        }
    }

    pub fn maybe_simple_type_var_like(&self) -> Option<TypeVarLike> {
        match self {
            Self::TypeArg(t) => match t.as_ref() {
                Type::TypeVar(t) => Some(TypeVarLike::TypeVar(t.type_var.clone())),
                _ => None,
            },
            Self::TypeArgs(ts) => todo!(),
            Self::ParamSpecArg(params) => match &params.params {
                CallableParams::WithParamSpec(_, p) => {
                    Some(TypeVarLike::ParamSpec(p.param_spec.clone()))
                }
                _ => None,
            },
        }
    }

    pub fn merge_matching_parts(self, db: &Database, other: Self) -> GenericItem {
        match self {
            Self::TypeArg(t1) => {
                let Self::TypeArg(t2) = other else {
                    unreachable!()
                };
                GenericItem::TypeArg(t1.merge_matching_parts(db, &t2))
            }
            Self::TypeArgs(ts1) => {
                let Self::TypeArgs(ts2) = other else {
                    unreachable!()
                };
                GenericItem::TypeArgs(TypeArgs::new(ts1.args.merge_matching_parts(db, &ts2.args)))
            }
            Self::ParamSpecArg(params) => todo!(),
        }
    }

    pub fn find_in_type(&self, db: &Database, check: &mut impl FnMut(&Type) -> bool) -> bool {
        match self {
            Generic::TypeArg(t) => t.find_in_type(db, check),
            Generic::TypeArgs(ts) => match &ts.args {
                TupleArgs::FixedLen(ts) => ts.iter().any(|t| t.find_in_type(db, check)),
                TupleArgs::ArbitraryLen(t) => t.find_in_type(db, check),
                TupleArgs::WithUnpack(with_unpack) => with_unpack.find_in_type(db, check),
            },
            Generic::ParamSpecArg(a) => a.params.find_in_type(db, check),
        }
    }
}
