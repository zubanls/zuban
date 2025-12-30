use std::sync::Arc;

use super::{super::Match, Matcher, MatcherFormatResult};
use crate::{
    database::Database,
    debug,
    format_data::{FormatData, ParamsStyle},
    inference_state::InferenceState,
    params::matches_params_with_variance,
    type_::{
        AnyCause, CallableParams, GenericItem, NeverCause, ParamSpecArg, ParamType,
        ReplaceTypeVarLikes, StarStarParamType, TupleArgs, TupleUnpack, Type, TypeArgs,
        TypeVarKind, TypeVarLike, TypeVarLikeUsage, Variance, WithUnpack,
        match_tuple_type_arguments,
    },
    type_helpers::Class,
};

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum Bound {
    Uncalculated { fallback: Option<Type> },

    Invariant(BoundKind),
    Upper(BoundKind),
    UpperAndLower(BoundKind, BoundKind),
    Lower(BoundKind),
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum BoundKind {
    TypeVar(Type),
    TypeVarTuple(TupleArgs),
    ParamSpec(CallableParams),
}

impl Default for Bound {
    fn default() -> Self {
        Self::Uncalculated { fallback: None }
    }
}

impl Bound {
    pub fn new_type_args(ts: TupleArgs, variance: Variance) -> Self {
        Self::new(BoundKind::TypeVarTuple(ts), variance)
    }

    pub fn new_param_spec(params: CallableParams, variance: Variance) -> Self {
        Self::new(BoundKind::ParamSpec(params), variance)
    }

    pub(super) fn new(k: BoundKind, variance: Variance) -> Self {
        match variance {
            Variance::Invariant => Self::Invariant(k),
            Variance::Covariant => Self::Lower(k),
            Variance::Contravariant => Self::Upper(k),
        }
    }

    pub fn format(
        &self,
        usage: &TypeVarLikeUsage,
        format_data: &FormatData,
        style: ParamsStyle,
    ) -> MatcherFormatResult {
        self.format_with_fallback(format_data, style, |_| {
            match usage.as_type_var_like() {
                TypeVarLike::TypeVar(type_var) => {
                    if let TypeVarKind::Bound(bound) = type_var.kind(format_data.db) {
                        return MatcherFormatResult::Str(bound.format(format_data));
                    }
                }
                TypeVarLike::TypeVarTuple(_) => return MatcherFormatResult::TypeVarTupleUnknown,
                _ => (),
            }
            MatcherFormatResult::Str(Type::Never(NeverCause::Other).format(format_data))
        })
    }

    pub fn format_with_fallback(
        &self,
        format_data: &FormatData,
        style: ParamsStyle,
        on_fallback: impl FnOnce(&Option<Type>) -> MatcherFormatResult,
    ) -> MatcherFormatResult {
        match self {
            Self::Invariant(t) | Self::Upper(t) | Self::Lower(t) | Self::UpperAndLower(t, _) => {
                MatcherFormatResult::Str(t.format(format_data, style))
            }
            Self::Uncalculated { fallback } => on_fallback(fallback),
        }
    }

    pub fn search_type_vars<C: FnMut(TypeVarLikeUsage) + ?Sized>(&self, found_type_var: &mut C) {
        let t = match self {
            Self::Invariant(t) | Self::Lower(t) | Self::Upper(t) => t,
            Self::UpperAndLower(upper, lower) => {
                upper.search_type_vars(found_type_var);
                lower
            }
            Self::Uncalculated { fallback: Some(t) } => {
                t.search_type_vars(found_type_var);
                return;
            }
            Self::Uncalculated { fallback: None } => return,
        };
        t.search_type_vars(found_type_var)
    }

    pub(super) fn replace_type_var_likes(
        &self,
        db: &Database,
        on_type_var_like: &mut impl FnMut(TypeVarLikeUsage) -> Option<GenericItem>,
    ) -> Option<Self> {
        Some(match self {
            Self::Invariant(t) => Self::Invariant(t.replace_type_var_likes(db, on_type_var_like)?),
            Self::Upper(t) => Self::Upper(t.replace_type_var_likes(db, on_type_var_like)?),
            Self::Lower(t) => Self::Upper(t.replace_type_var_likes(db, on_type_var_like)?),
            Self::UpperAndLower(upper, lower) => {
                let new_upper = upper.replace_type_var_likes(db, on_type_var_like);
                let new_lower = lower.replace_type_var_likes(db, on_type_var_like);
                if new_upper.is_none() && new_lower.is_none() {
                    return None;
                }
                Self::UpperAndLower(
                    new_upper.unwrap_or_else(|| upper.clone()),
                    new_lower.unwrap_or_else(|| lower.clone()),
                )
            }
            Self::Uncalculated { fallback: Some(t) } => Self::Uncalculated {
                fallback: Some(t.replace_type_var_likes(db, on_type_var_like)?),
            },
            Self::Uncalculated { fallback: None } => Self::Uncalculated { fallback: None },
        })
    }

    pub fn into_generic_item(
        self,
        db: &Database,
        on_uncalculated: impl FnOnce(Option<Type>) -> GenericItem,
    ) -> GenericItem {
        self.into_maybe_generic_item(db, |t| Some(on_uncalculated(t)))
            .expect("Since we never return None in fallback, we should be able to unwrap")
    }

    pub fn into_maybe_generic_item(
        self,
        db: &Database,
        on_uncalculated: impl FnOnce(Option<Type>) -> Option<GenericItem>,
    ) -> Option<GenericItem> {
        Some(match self {
            // If the upper bound is a literal, we do not want to use the lower bound.
            Self::UpperAndLower(t @ BoundKind::TypeVar(Type::Literal(_)), _) => {
                t.into_generic_item()
            }
            Self::Lower(BoundKind::TypeVar(Type::Literal(l)))
            | Self::UpperAndLower(_, BoundKind::TypeVar(Type::Literal(l)))
                if l.implicit =>
            {
                GenericItem::TypeArg(l.fallback_type(db))
            }
            Self::Invariant(k) | Self::Upper(k) | Self::Lower(k) | Self::UpperAndLower(_, k) => {
                k.into_generic_item()
            }
            Self::Uncalculated { fallback } => return on_uncalculated(fallback),
        })
    }

    pub fn set_to_any(&mut self, tv: &TypeVarLike, cause: AnyCause) {
        *self = Self::Invariant(BoundKind::new_any(tv, cause))
    }

    pub fn avoid_type_vars_from_class_self_arguments(&mut self, class: Class) {
        let is_self_type_var = match self {
            Self::Invariant(k) | Self::Lower(k) | Self::Upper(k) => match k {
                BoundKind::TypeVar(Type::TypeVar(tv))
                    if class.node_ref.as_link() == tv.in_definition =>
                {
                    true
                }
                BoundKind::TypeVarTuple(tuple_args) => match tuple_args {
                    TupleArgs::WithUnpack(t) if t.before.is_empty() && t.after.is_empty() => {
                        matches!(
                            &t.unpack,
                            TupleUnpack::TypeVarTuple(u)
                            if u.in_definition == class.node_ref.as_link()
                        )
                    }
                    _ => false,
                },
                BoundKind::ParamSpec(CallableParams::Simple(params)) => {
                    params.last().is_some_and(|p| {
                        matches!(
                            &p.type_,
                            ParamType::StarStar(StarStarParamType::ParamSpecKwargs(u))
                            if u.in_definition == class.node_ref.as_link()
                        )
                    })
                }
                _ => false,
            },
            Self::UpperAndLower(..) => unreachable!(),
            Self::Uncalculated { .. } => false,
        };
        if is_self_type_var {
            *self = Self::Uncalculated { fallback: None };
        }
    }

    pub fn has_any(&self, i_s: &InferenceState) -> bool {
        match self {
            Self::Invariant(k) | Self::Upper(k) | Self::Lower(k) => k.has_any(i_s),
            Self::UpperAndLower(upper, lower) => upper.has_any(i_s) || lower.has_any(i_s),
            Self::Uncalculated {
                fallback: Some(fallback),
            } => fallback.has_any(i_s),
            Self::Uncalculated { fallback: None } => false,
        }
    }

    pub fn maybe_any(&self) -> Option<AnyCause> {
        match self {
            Self::Invariant(k) | Self::Upper(k) | Self::Lower(k) => k.maybe_any(),
            Self::UpperAndLower(upper, lower) => {
                upper.maybe_any().filter(|_| lower.maybe_any().is_some())
            }
            Self::Uncalculated { .. } => None,
        }
    }

    pub fn is_none(&self) -> bool {
        match self {
            Self::Invariant(k) | Self::Upper(k) | Self::Lower(k) => k.is_none(),
            Self::UpperAndLower(upper, lower) => upper.is_none() || lower.is_none(),
            Self::Uncalculated {
                fallback: Some(fallback),
            } => matches!(fallback, Type::None),
            Self::Uncalculated { fallback: None } => false,
        }
    }
}

impl BoundKind {
    pub fn new_any(tv: &TypeVarLike, cause: AnyCause) -> Self {
        match tv {
            TypeVarLike::TypeVar(_) => Self::TypeVar(Type::Any(cause)),
            TypeVarLike::TypeVarTuple(_) => {
                Self::TypeVarTuple(TupleArgs::ArbitraryLen(Arc::new(Type::Any(cause))))
            }
            TypeVarLike::ParamSpec(_) => Self::ParamSpec(CallableParams::Any(cause)),
        }
    }

    fn format(&self, format_data: &FormatData, style: ParamsStyle) -> Box<str> {
        match &self {
            Self::TypeVar(bound) => bound.format(format_data),
            Self::TypeVarTuple(ts) => ts.format(format_data),
            Self::ParamSpec(p) => p.format(format_data, style),
        }
    }

    pub fn format_short(&self, db: &Database) -> Box<str> {
        self.format(&FormatData::new_short(db), ParamsStyle::CallableParams)
    }

    fn simple_matches(&self, i_s: &InferenceState, other: &Self, variance: Variance) -> Match {
        self.matches(i_s, &mut Matcher::default(), other, variance)
    }

    pub(super) fn is_simple_same_type(&self, i_s: &InferenceState, other: &Self) -> Match {
        self.simple_matches(i_s, other, Variance::Invariant)
    }

    pub(super) fn is_simple_super_type_of(&self, i_s: &InferenceState, other: &Self) -> Match {
        self.simple_matches(i_s, other, Variance::Covariant)
    }

    pub(super) fn is_simple_sub_type_of(&self, i_s: &InferenceState, other: &Self) -> Match {
        self.simple_matches(i_s, other, Variance::Contravariant)
    }

    pub(super) fn common_base_type(&self, i_s: &InferenceState, other: &Self) -> Option<Self> {
        match (self, other) {
            (Self::TypeVar(t1), Self::TypeVar(t2)) => {
                Some(Self::TypeVar(if i_s.flags().use_joins {
                    t1.common_base_type(i_s, t2)
                } else {
                    t1.avoid_implicit_literal_cow(i_s.db)
                        .simplified_union(i_s, &t2.avoid_implicit_literal_cow(i_s.db))
                }))
            }
            (Self::TypeVarTuple(tup1), Self::TypeVarTuple(tup2)) => Some(Self::TypeVarTuple(
                tup1.simplified_union_for_type_var_tuple(i_s, tup2)?,
            )),
            (Self::ParamSpec(params1), Self::ParamSpec(params2)) => params1
                .common_base_type(i_s, params2, None)
                .map(Self::ParamSpec),
            _ => unreachable!(),
        }
    }

    pub(super) fn common_sub_type(&self, i_s: &InferenceState, other: &Self) -> Option<Self> {
        match (self, other) {
            (Self::TypeVar(t1), Self::TypeVar(t2)) => {
                Some(Self::TypeVar(t1.common_sub_type(i_s, t2)?))
            }
            (Self::TypeVarTuple(tup1), Self::TypeVarTuple(tup2)) => {
                Some(Self::TypeVarTuple(tup1.common_sub_type(i_s, tup2)?))
            }
            (Self::ParamSpec(params1), Self::ParamSpec(params2)) => {
                debug!(
                    "Common subtype for ParamSpec '{}' and '{}'",
                    params1.format(&FormatData::new_short(i_s.db), ParamsStyle::Unreachable),
                    params2.format(&FormatData::new_short(i_s.db), ParamsStyle::Unreachable),
                );
                params1.common_sub_type(i_s, params2).map(Self::ParamSpec)
            }
            _ => unreachable!(),
        }
    }

    fn search_type_vars<C: FnMut(TypeVarLikeUsage) + ?Sized>(&self, found_type_var: &mut C) {
        match self {
            Self::TypeVar(t) => t.search_type_vars(found_type_var),
            Self::TypeVarTuple(tup) => tup.search_type_vars(found_type_var),
            Self::ParamSpec(params) => params.search_type_vars(found_type_var),
        }
    }

    fn into_generic_item(self) -> GenericItem {
        match self {
            Self::TypeVar(t) => GenericItem::TypeArg(t),
            Self::TypeVarTuple(ts) => GenericItem::TypeArgs(TypeArgs::new(ts)),
            Self::ParamSpec(param_spec) => GenericItem::ParamSpecArg(ParamSpecArg {
                params: param_spec,
                type_vars: None,
            }),
        }
    }

    fn replace_type_var_likes(
        &self,
        db: &Database,
        on_type_var_like: &mut impl FnMut(TypeVarLikeUsage) -> Option<GenericItem>,
    ) -> Option<Self> {
        Some(match self {
            Self::TypeVar(t) => Self::TypeVar(t.replace_type_var_likes(db, on_type_var_like)?),
            Self::TypeVarTuple(tup) => {
                Self::TypeVarTuple(tup.replace_type_var_likes(db, on_type_var_like)?)
            }
            Self::ParamSpec(params) => Self::ParamSpec(params.replace_type_var_likes_and_self(
                db,
                on_type_var_like,
                &|| None,
            )?),
        })
    }

    fn has_any(&self, i_s: &InferenceState) -> bool {
        match self {
            Self::TypeVar(t) => t.has_any(i_s),
            Self::TypeVarTuple(ts) => ts.has_any(i_s),
            Self::ParamSpec(params) => params.has_any(i_s),
        }
    }

    fn maybe_any(&self) -> Option<AnyCause> {
        match self {
            Self::TypeVar(Type::Any(cause)) => Some(*cause),
            Self::TypeVar(_) => None,
            Self::TypeVarTuple(ts) => ts.maybe_any(),
            Self::ParamSpec(params) => match params {
                CallableParams::Any(cause) => Some(*cause),
                _ => None,
            },
        }
    }

    fn is_none(&self) -> bool {
        match self {
            Self::TypeVar(t) => matches!(t, Type::None),
            _ => false,
        }
    }

    pub(crate) fn matches(
        &self,
        i_s: &InferenceState,
        matcher: &mut Matcher,
        other: &Self,
        variance: Variance,
    ) -> Match {
        match (self, other) {
            (Self::TypeVar(t1), Self::TypeVar(t2)) => t1.matches(i_s, matcher, t2, variance),
            (Self::TypeVarTuple(tup1), Self::TypeVarTuple(tup2)) => {
                match_tuple_type_arguments(i_s, matcher, tup1, tup2, variance)
            }
            (Self::ParamSpec(params1), Self::ParamSpec(params2)) => {
                matches_params_with_variance(i_s, matcher, params1, params2, variance)
            }
            _ => unreachable!(),
        }
    }
}

impl TupleArgs {
    fn simplified_union_for_type_var_tuple(
        &self,
        i_s: &InferenceState,
        other: &Self,
    ) -> Option<Self> {
        if self == other {
            return Some(self.clone());
        }
        Some(match (self, other) {
            (TupleArgs::FixedLen(ts1), TupleArgs::FixedLen(ts2)) if ts1.len() == ts2.len() => {
                TupleArgs::FixedLen(
                    ts1.iter()
                        .zip(ts2.iter())
                        .map(|(t1, t2)| {
                            if i_s.db.project.settings.mypy_compatible {
                                Some(t1.simplified_union(i_s, t2))
                            } else {
                                t1.common_base_if_subtype(i_s, t2)
                            }
                        })
                        .collect::<Option<_>>()?,
                )
            }
            (TupleArgs::FixedLen(_), TupleArgs::FixedLen(_))
                // Conformance tests don't allow unions with different length, Mypy allows it
                if !i_s.db.project.settings.mypy_compatible =>
            {
                return None;
            }
            (TupleArgs::WithUnpack(w1), TupleArgs::WithUnpack(w2))
                if w1.before.len() == w2.before.len() && w1.after.len() == w2.after.len() =>
            {
                TupleArgs::WithUnpack(WithUnpack {
                    before: w1
                        .before
                        .iter()
                        .zip(w2.before.iter())
                        .map(|(t1, t2)| t1.simplified_union(i_s, t2))
                        .collect(),
                    unpack: match (&w1.unpack, &w2.unpack) {
                        (TupleUnpack::ArbitraryLen(t1), TupleUnpack::ArbitraryLen(t2)) => {
                            TupleUnpack::ArbitraryLen(t1.simplified_union(i_s, t2))
                        }
                        (TupleUnpack::TypeVarTuple(tvt1), TupleUnpack::TypeVarTuple(tvt2))
                            if tvt1 == tvt2 =>
                        {
                            TupleUnpack::TypeVarTuple(tvt1.clone())
                        }
                        _ => {
                            if w1.unpack.is_any() {
                                w1.unpack.clone()
                            } else if w2.unpack.is_any() {
                                w2.unpack.clone()
                            } else {
                                return None;
                            }
                        }
                    },
                    after: w1
                        .after
                        .iter()
                        .zip(w2.after.iter())
                        .map(|(t1, t2)| t1.simplified_union(i_s, t2))
                        .collect(),
                })
            }
            (TupleArgs::FixedLen(_) | TupleArgs::ArbitraryLen(_), TupleArgs::FixedLen(_) | TupleArgs::ArbitraryLen(_)) => TupleArgs::ArbitraryLen(Arc::new(
                self.simplified_union_of_tuple_entries(i_s)
                    .simplified_union(i_s, &other.simplified_union_of_tuple_entries(i_s)),
            )),
            _ => return None
        })
    }
}

impl Type {
    fn common_base_if_subtype(&self, i_s: &InferenceState, t2: &Self) -> Option<Self> {
        // Conformance tests do not allow tuple merging for TypeVarTuples,
        // we therefore only match subtypes.
        if self.is_any() {
            return Some(self.clone());
        } else if t2.is_any() {
            return Some(t2.clone());
        }
        let t1 = self.avoid_implicit_literal_cow(i_s.db);
        let t2 = t2.avoid_implicit_literal_cow(i_s.db);
        if t1.is_simple_super_type_of(i_s, &t2).bool() {
            Some(t1.into_owned())
        } else if t2.is_simple_super_type_of(i_s, &t1).bool() {
            Some(t2.into_owned())
        } else {
            None
        }
    }
}
