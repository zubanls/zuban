use super::{
    super::{FormatData, Match},
    Matcher, MatcherFormatResult,
};
use crate::{
    database::Database,
    inference_state::InferenceState,
    matching::{matches_params_with_variance, ParamsStyle},
    type_::{
        match_tuple_type_arguments, AnyCause, CallableParams, GenericItem, ParamSpecArg, TupleArgs,
        Type, TypeArgs, TypeVar, TypeVarKind, TypeVarLike, TypeVarLikeUsage, Variance,
    },
    type_helpers::Class,
};

#[derive(Debug, Clone, PartialEq)]
pub enum Bound {
    Uncalculated { fallback: Option<Type> },

    Invariant(BoundKind),
    Upper(BoundKind),
    UpperAndLower(BoundKind, BoundKind),
    Lower(BoundKind),
}

#[derive(Debug, Clone, PartialEq)]
pub enum BoundKind {
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
    pub fn new_type_arg(t: Type, variance: Variance, type_var: &TypeVar) -> Self {
        let k = BoundKind::TypeVar(t);
        match variance {
            Variance::Invariant => Self::Invariant(k),
            Variance::Covariant => match &type_var.kind {
                TypeVarKind::Bound(bound) => {
                    Self::UpperAndLower(BoundKind::TypeVar(bound.clone()), k)
                }
                _ => Self::Lower(k),
            },
            Variance::Contravariant => Self::Upper(k),
        }
    }

    pub fn new_type_args(ts: TupleArgs, variance: Variance) -> Self {
        Self::new(BoundKind::TypeVarTuple(ts), variance)
    }

    pub fn new_param_spec(params: CallableParams, variance: Variance) -> Self {
        Self::new(BoundKind::ParamSpec(params), variance)
    }

    fn new(k: BoundKind, variance: Variance) -> Self {
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
        MatcherFormatResult::Str(match self {
            Self::Invariant(t) | Self::Upper(t) | Self::Lower(t) | Self::UpperAndLower(t, _) => {
                t.format(format_data, style)
            }
            Self::Uncalculated { fallback } => {
                match usage.as_type_var_like() {
                    TypeVarLike::TypeVar(type_var) => {
                        if let TypeVarKind::Bound(bound) = &type_var.kind {
                            return MatcherFormatResult::Str(bound.format(format_data));
                        }
                    }
                    TypeVarLike::TypeVarTuple(_) => {
                        return MatcherFormatResult::TypeVarTupleUnknown
                    }
                    _ => (),
                }
                Type::Never.format(format_data)
            }
        })
    }

    pub fn merge(&mut self, db: &Database, other: Self) -> Match {
        if self == &other {
            return Match::new_true();
        }
        let i_s = InferenceState::new(db);
        let mut m = Match::new_true();
        if let Self::Uncalculated { fallback } = self {
            if !matches!(&other, Self::Uncalculated { .. }) || fallback.is_none() {
                *self = other;
            }
            return Match::new_true();
        }
        let (t, variance) = match other {
            Self::Upper(t) => (t, Variance::Contravariant),
            Self::Lower(t) => (t, Variance::Covariant),
            Self::Invariant(t) => (t, Variance::Invariant),
            Self::UpperAndLower(upper, t) => {
                m = self.merge_or_mismatch(&i_s, &upper, Variance::Contravariant);
                (t, Variance::Covariant)
            }
            Self::Uncalculated { .. } => return Match::new_true(),
        };
        m & self.merge_or_mismatch(&i_s, &t, variance)
    }

    pub fn merge_or_mismatch(
        &mut self,
        i_s: &InferenceState,
        other: &BoundKind,
        variance: Variance,
    ) -> Match {
        // First check if the value is between the bounds.
        let matches = match self {
            Self::Invariant(t) => {
                let m = t.is_simple_same_type(i_s, other);
                if m.bool() {
                    return m; // In the false case we still have to check for the variance cases.
                }
                m
            }
            Self::Upper(lower) => lower.is_simple_super_type_of(i_s, other),
            Self::Lower(upper) => upper.is_simple_sub_type_of(i_s, other),
            Self::UpperAndLower(lower, upper) => {
                lower.is_simple_super_type_of(i_s, other) & upper.is_simple_sub_type_of(i_s, other)
            }
            Self::Uncalculated { .. } => unreachable!(),
        };
        if matches.bool() {
            // If we are between the bounds we might need to update lower/upper bounds
            match variance {
                Variance::Invariant => *self = Self::Invariant(other.clone()),
                Variance::Covariant => self.update_lower_bound(i_s, other),
                Variance::Contravariant => self.update_upper_bound(i_s, other),
            }
        } else {
            // If we are not between the lower and upper bound, but the value is co or
            // contravariant, it can still be valid.
            match variance {
                Variance::Invariant => (),
                Variance::Covariant => match self {
                    Self::Lower(t) => {
                        // TODO shouldn't this also do a limited common base type search in the
                        // case of LowerAndUpper?
                        let m = t.is_simple_super_type_of(i_s, other);
                        *t = t.common_base_type(i_s, other);
                        if !m.bool() {
                            return Match::new_true();
                        }
                        return m;
                    }
                    Self::Invariant(t) | Self::UpperAndLower(_, t) => {
                        return t.is_simple_super_type_of(i_s, other)
                    }
                    Self::Upper(t) => {}
                    Self::Uncalculated { .. } => unreachable!(),
                },
                Variance::Contravariant => match self {
                    Self::Upper(t) => {
                        // TODO shouldn't we also check LowerAndUpper like this?
                        let m = t.is_simple_sub_type_of(i_s, other);
                        if !m.bool() {
                            if let Some(new) = t.common_sub_type(i_s, other) {
                                *t = new;
                                return Match::new_true();
                            } else {
                                return Match::new_false();
                            }
                        }
                        return m;
                    }
                    Self::Invariant(t) | Self::UpperAndLower(t, _) => {
                        return t.is_simple_sub_type_of(i_s, other);
                    }
                    Self::Lower(_) => {}
                    Self::Uncalculated { .. } => unreachable!(),
                },
            };
        }
        matches
    }

    fn update_upper_bound(&mut self, i_s: &InferenceState, upper: &BoundKind) {
        match self {
            Self::Upper(old) => *self = Self::Upper(upper.clone()),
            Self::Lower(lower) | Self::UpperAndLower(_, lower) => {
                *self = Self::UpperAndLower(upper.clone(), lower.clone())
            }
            _ => unreachable!(),
        }
    }

    fn update_lower_bound(&mut self, i_s: &InferenceState, lower: &BoundKind) {
        match self {
            Self::Lower(old) => *self = Self::Lower(old.common_base_type(i_s, lower)),
            Self::Upper(upper) => *self = Self::UpperAndLower(upper.clone(), lower.clone()),
            Self::UpperAndLower(upper, old) => {
                *self = Self::UpperAndLower(upper.clone(), old.common_base_type(i_s, lower))
            }
            _ => unreachable!(),
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

    pub fn replace_type_var_likes(
        &self,
        db: &Database,
        on_type_var_like: &mut impl FnMut(TypeVarLikeUsage) -> GenericItem,
    ) -> Self {
        match self {
            Self::Invariant(t) => Self::Invariant(t.replace_type_var_likes(db, on_type_var_like)),
            Self::Upper(t) => Self::Upper(t.replace_type_var_likes(db, on_type_var_like)),
            Self::Lower(t) => Self::Upper(t.replace_type_var_likes(db, on_type_var_like)),
            Self::UpperAndLower(upper, lower) => Self::UpperAndLower(
                upper.replace_type_var_likes(db, on_type_var_like),
                lower.replace_type_var_likes(db, on_type_var_like),
            ),
            Self::Uncalculated { fallback: Some(t) } => Self::Uncalculated {
                fallback: Some(t.replace_type_var_likes(db, on_type_var_like)),
            },
            Self::Uncalculated { fallback: None } => Self::Uncalculated { fallback: None },
        }
    }

    pub fn into_generic_item(
        self,
        db: &Database,
        on_uncalculated: impl FnOnce(Option<Type>) -> GenericItem,
    ) -> GenericItem {
        match self {
            // If the upper bound is a literal, we do not want to use the lower bound.
            Self::UpperAndLower(t @ BoundKind::TypeVar(Type::Literal(_)), _) => {
                t.into_generic_item()
            }
            Self::Lower(BoundKind::TypeVar(Type::Literal(l)))
            | Self::UpperAndLower(_, BoundKind::TypeVar(Type::Literal(l)))
                if l.implicit =>
            {
                GenericItem::TypeArg(db.python_state.literal_type(&l.kind))
            }
            Self::Invariant(k) | Self::Upper(k) | Self::Lower(k) | Self::UpperAndLower(_, k) => {
                k.into_generic_item()
            }
            Self::Uncalculated { fallback } => on_uncalculated(fallback),
        }
    }

    pub fn set_to_any(&mut self, tv: &TypeVarLike, cause: AnyCause) {
        *self = Self::Invariant(match tv {
            TypeVarLike::TypeVar(_) => BoundKind::TypeVar(Type::Any(cause)),
            TypeVarLike::TypeVarTuple(_) => {
                BoundKind::TypeVarTuple(TupleArgs::ArbitraryLen(Box::new(Type::Any(cause))))
            }
            TypeVarLike::ParamSpec(_) => BoundKind::ParamSpec(CallableParams::Any(cause)),
        })
    }

    pub fn avoid_type_vars_from_class_self_arguments(&mut self, class: Class) {
        let is_self_type_var = match self {
            Self::Invariant(k) | Self::Lower(k) | Self::Upper(k) => match k {
                BoundKind::TypeVar(Type::TypeVar(tv))
                    if class.node_ref.as_link() == tv.in_definition =>
                {
                    true
                }
                BoundKind::TypeVarTuple(_) => todo!(),
                BoundKind::ParamSpec(CallableParams::WithParamSpec(pre, p2))
                    if pre.is_empty() && class.node_ref.as_link() == p2.in_definition =>
                {
                    true
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
            Self::UpperAndLower(lower, upper) => lower.has_any(i_s) || upper.has_any(i_s),
            Self::Uncalculated {
                fallback: Some(fallback),
            } => fallback.has_any(i_s),
            Self::Uncalculated { fallback: None } => false,
        }
    }

    pub fn is_none(&self) -> bool {
        match self {
            Self::Invariant(k) | Self::Upper(k) | Self::Lower(k) => k.is_none(),
            Self::UpperAndLower(lower, upper) => lower.is_none() || upper.is_none(),
            Self::Uncalculated {
                fallback: Some(fallback),
            } => matches!(fallback, Type::None),
            Self::Uncalculated { fallback: None } => false,
        }
    }
}

impl BoundKind {
    fn format(&self, format_data: &FormatData, style: ParamsStyle) -> Box<str> {
        return match &self {
            Self::TypeVar(bound) => bound.format(format_data),
            Self::TypeVarTuple(ts) => ts.format(format_data),
            Self::ParamSpec(p) => p.format(format_data, style),
        };
    }

    pub fn format_short(&self, db: &Database) -> Box<str> {
        self.format(&FormatData::new_short(db), ParamsStyle::CallableParams)
    }

    fn simple_matches(&self, i_s: &InferenceState, other: &Self, variance: Variance) -> Match {
        self.matches(i_s, &mut Matcher::default(), other, variance)
    }

    fn is_simple_same_type(&self, i_s: &InferenceState, other: &Self) -> Match {
        self.simple_matches(i_s, other, Variance::Invariant)
    }

    fn is_simple_super_type_of(&self, i_s: &InferenceState, other: &Self) -> Match {
        self.simple_matches(i_s, other, Variance::Covariant)
    }

    fn is_simple_sub_type_of(&self, i_s: &InferenceState, other: &Self) -> Match {
        self.simple_matches(i_s, other, Variance::Contravariant)
    }

    fn common_base_type(&self, i_s: &InferenceState, other: &Self) -> Self {
        match (self, other) {
            (Self::TypeVar(t1), Self::TypeVar(t2)) => Self::TypeVar(t1.common_base_type(i_s, t2)),
            (Self::TypeVarTuple(tup1), Self::TypeVarTuple(tup2)) => {
                Self::TypeVarTuple(tup1.common_base_type(i_s, tup2))
            }
            (Self::ParamSpec(params1), Self::ParamSpec(params2)) => todo!(),
            _ => unreachable!(),
        }
    }

    fn common_sub_type(&self, i_s: &InferenceState, other: &Self) -> Option<Self> {
        match (self, other) {
            (Self::TypeVar(t1), Self::TypeVar(t2)) => Some(Self::TypeVar(
                t1.common_sub_type(i_s, t2).unwrap_or(Type::Never),
            )),
            (Self::TypeVarTuple(tup1), Self::TypeVarTuple(tup2)) => todo!(),
            (Self::ParamSpec(params1), Self::ParamSpec(params2)) => {
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
        on_type_var_like: &mut impl FnMut(TypeVarLikeUsage) -> GenericItem,
    ) -> Self {
        match self {
            Self::TypeVar(t) => Self::TypeVar(t.replace_type_var_likes(db, on_type_var_like)),
            Self::TypeVarTuple(tup) => Self::TypeVarTuple(tup.replace_type_var_likes_and_self(
                db,
                on_type_var_like,
                &|| Type::Self_,
            )),
            Self::ParamSpec(params) => Self::ParamSpec(
                params
                    .replace_type_var_likes_and_self(db, &mut None, None, on_type_var_like, &|| {
                        Type::Self_
                    })
                    .0,
            ),
        }
    }

    fn has_any(&self, i_s: &InferenceState) -> bool {
        match self {
            Self::TypeVar(t) => t.has_any(i_s),
            Self::TypeVarTuple(ts) => ts.has_any(i_s),
            Self::ParamSpec(params) => params.has_any(i_s),
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
