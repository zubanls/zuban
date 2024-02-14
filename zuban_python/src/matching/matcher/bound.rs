use super::super::{FormatData, Match};
use crate::{
    database::Database,
    inference_state::InferenceState,
    matching::ParamsStyle,
    type_::{
        AnyCause, CallableParams, FormatStyle, GenericItem, ParamSpecArg, TupleArgs, Type,
        TypeArgs, TypeVar, TypeVarKind, TypeVarLike, TypeVarLikeUsage, Variance,
    },
    type_helpers::Class,
};

#[derive(Debug, Clone, PartialEq)]
pub enum TypeVarBound {
    Invariant(Type),
    Upper(Type),
    UpperAndLower(Type, Type),
    Lower(Type),
}

impl TypeVarBound {
    pub fn new(t: Type, variance: Variance, type_var: &TypeVar) -> Self {
        match variance {
            Variance::Invariant => Self::Invariant(t),
            Variance::Covariant => match &type_var.kind {
                TypeVarKind::Bound(bound) => Self::UpperAndLower(bound.clone(), t),
                _ => Self::Lower(t),
            },
            Variance::Contravariant => Self::Upper(t),
        }
    }

    pub fn format(&self, db: &Database, style: FormatStyle) -> Box<str> {
        match self {
            Self::Invariant(t) | Self::Upper(t) | Self::Lower(t) | Self::UpperAndLower(t, _) => {
                t.format(&FormatData::with_style(db, style))
            }
        }
    }

    pub fn into_type(self, db: &Database) -> Type {
        match self {
            // If the upper bound is a literal, we do not want to use the lower bound.
            Self::UpperAndLower(t @ Type::Literal(_), _) => t,
            Self::Lower(Type::Literal(l)) | Self::UpperAndLower(_, Type::Literal(l))
                if l.implicit =>
            {
                db.python_state.literal_type(&l.kind)
            }
            Self::Invariant(t) | Self::Upper(t) | Self::Lower(t) | Self::UpperAndLower(_, t) => t,
        }
    }

    fn update_upper_bound(&mut self, i_s: &InferenceState, upper: &Type) {
        match self {
            Self::Upper(old) => *self = Self::Upper(upper.clone()),
            Self::Lower(lower) | Self::UpperAndLower(_, lower) => {
                *self = Self::UpperAndLower(upper.clone(), lower.clone())
            }
            Self::Invariant(_) => unreachable!(),
        }
    }

    fn update_lower_bound(&mut self, i_s: &InferenceState, lower: &Type) {
        match self {
            Self::Lower(old) => *self = Self::Lower(old.common_base_type(i_s, lower)),
            Self::Upper(upper) => *self = Self::UpperAndLower(upper.clone(), lower.clone()),
            Self::UpperAndLower(upper, old) => {
                *self = Self::UpperAndLower(upper.clone(), old.common_base_type(i_s, lower))
            }
            Self::Invariant(_) => unreachable!(),
        }
    }

    pub fn merge_or_mismatch(
        &mut self,
        i_s: &InferenceState,
        other: &Type,
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
                },
                Variance::Contravariant => match self {
                    Self::Upper(t) => {
                        // TODO shouldn't we also check LowerAndUpper like this?
                        let m = t.is_simple_sub_type_of(i_s, other);
                        if !m.bool() {
                            if let Some(new) = t.common_sub_type(i_s, other) {
                                *t = new;
                            } else {
                                *t = Type::Never;
                            }
                            return Match::new_true();
                        }
                        return m;
                    }
                    Self::Invariant(t) | Self::UpperAndLower(t, _) => {
                        return t.is_simple_sub_type_of(i_s, other);
                    }
                    Self::Lower(_) => {}
                },
            };
        }
        matches
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Bound {
    TypeVar(TypeVarBound),
    TypeVarTuple(TupleArgs),
    ParamSpec(CallableParams),
    Uncalculated { fallback: Option<Type> },
}

impl Default for Bound {
    fn default() -> Self {
        Self::Uncalculated { fallback: None }
    }
}

impl Bound {
    pub fn format(
        &self,
        usage: &TypeVarLikeUsage,
        format_data: &FormatData,
        params_style: ParamsStyle,
    ) -> Box<str> {
        return match &self {
            Self::TypeVar(bound) => bound.format(format_data.db, format_data.style),
            Self::TypeVarTuple(ts) => ts.format(format_data),
            Self::ParamSpec(p) => p.format(format_data, params_style),
            Self::Uncalculated { fallback } => {
                if let TypeVarLike::TypeVar(type_var) = usage.as_type_var_like() {
                    if let TypeVarKind::Bound(bound) = &type_var.kind {
                        return bound.format(format_data);
                    }
                }
                Type::Never.format(format_data)
            }
        };
    }

    pub fn merge(&mut self, db: &Database, other: Self) -> Match {
        if self == &other {
            return Match::new_true();
        }
        let i_s = InferenceState::new(db);
        match (self, other) {
            (Self::TypeVar(bound1), Self::TypeVar(bound2)) => {
                let mut m = Match::new_true();
                let (t, variance) = match bound2 {
                    TypeVarBound::Upper(t) => (t, Variance::Contravariant),
                    TypeVarBound::Lower(t) => (t, Variance::Covariant),
                    TypeVarBound::Invariant(t) => (t, Variance::Invariant),
                    TypeVarBound::UpperAndLower(upper, t) => {
                        m = bound1.merge_or_mismatch(&i_s, &upper, Variance::Contravariant);
                        (t, Variance::Covariant)
                    }
                };
                m & bound1.merge_or_mismatch(&i_s, &t, variance)
            }
            (Self::TypeVarTuple(tup1), Self::TypeVarTuple(tup2)) => {
                dbg!(tup1, tup2);
                //match_tuple_type_arguments(&i_s, &mut Matcher::default(), tup1, &tup2, Variance::Invariant);
                todo!()
            }
            (Self::ParamSpec(p1), Self::ParamSpec(p2)) => {
                //matches_params(&i_s, &mut Matcher::default(), p1, &p2, Variance::Invariant, false)
                dbg!(p1, p2);
                todo!()
            }
            (Self::Uncalculated { fallback: Some(_) }, Self::Uncalculated { .. }) => {
                Match::new_true()
            }
            (slf @ Self::Uncalculated { fallback: _ }, other) => {
                *slf = other;
                Match::new_true()
            }
            (_, Self::Uncalculated { fallback: _ }) => Match::new_true(),
            _ => unreachable!(),
        }
    }

    pub fn search_type_vars<C: FnMut(TypeVarLikeUsage) + ?Sized>(&self, found_type_var: &mut C) {
        match self {
            Self::TypeVar(tv) => {
                let t = match tv {
                    TypeVarBound::Invariant(t)
                    | TypeVarBound::Lower(t)
                    | TypeVarBound::Upper(t) => t,
                    TypeVarBound::UpperAndLower(upper, lower) => {
                        upper.search_type_vars(found_type_var);
                        lower
                    }
                };
                t.search_type_vars(found_type_var)
            }
            Self::TypeVarTuple(tup) => tup.search_type_vars(found_type_var),
            Self::ParamSpec(params) => params.search_type_vars(found_type_var),
            Self::Uncalculated { fallback: Some(t) } => t.search_type_vars(found_type_var),
            Self::Uncalculated { fallback: None } => (),
        }
    }

    pub fn replace_type_var_likes(
        &self,
        db: &Database,
        on_type_var_like: &mut impl FnMut(TypeVarLikeUsage) -> GenericItem,
    ) -> Self {
        match self {
            Self::TypeVar(tv) => Self::TypeVar(match tv {
                TypeVarBound::Invariant(t) => {
                    TypeVarBound::Invariant(t.replace_type_var_likes(db, on_type_var_like))
                }
                TypeVarBound::Upper(t) => {
                    TypeVarBound::Upper(t.replace_type_var_likes(db, on_type_var_like))
                }
                TypeVarBound::Lower(t) => {
                    TypeVarBound::Upper(t.replace_type_var_likes(db, on_type_var_like))
                }
                TypeVarBound::UpperAndLower(upper, lower) => TypeVarBound::UpperAndLower(
                    upper.replace_type_var_likes(db, on_type_var_like),
                    lower.replace_type_var_likes(db, on_type_var_like),
                ),
            }),
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
            Self::Uncalculated { fallback: Some(t) } => Self::Uncalculated {
                fallback: Some(t.replace_type_var_likes(db, on_type_var_like)),
            },
            Self::Uncalculated { fallback: None } => Self::Uncalculated { fallback: None },
        }
    }

    pub fn as_generic_item(
        &self,
        db: &Database,
        on_uncalculated: impl FnOnce() -> GenericItem,
    ) -> GenericItem {
        match self {
            Self::TypeVar(t) => GenericItem::TypeArg(t.clone().into_type(db)),
            Self::TypeVarTuple(ts) => GenericItem::TypeArgs(TypeArgs::new(ts.clone())),
            Self::ParamSpec(param_spec) => GenericItem::ParamSpecArg(ParamSpecArg {
                params: param_spec.clone(),
                type_vars: None,
            }),
            // Any is just ignored by the context later.
            Self::Uncalculated { .. } => on_uncalculated(),
        }
    }

    pub fn into_generic_item(
        self,
        db: &Database,
        on_uncalculated: impl FnOnce() -> GenericItem,
    ) -> GenericItem {
        match self {
            Self::TypeVar(t) => GenericItem::TypeArg(t.into_type(db)),
            Self::TypeVarTuple(ts) => GenericItem::TypeArgs(TypeArgs::new(ts)),
            Self::ParamSpec(params) => GenericItem::ParamSpecArg(ParamSpecArg {
                params,
                type_vars: None,
            }),
            Self::Uncalculated {
                fallback: Some(fallback),
            } => GenericItem::TypeArg(fallback),
            Self::Uncalculated { fallback: None } => on_uncalculated(),
        }
    }

    pub fn set_to_any(&mut self, tv: &TypeVarLike, cause: AnyCause) {
        *self = match tv {
            TypeVarLike::TypeVar(_) => Bound::TypeVar(TypeVarBound::Invariant(Type::Any(cause))),
            TypeVarLike::TypeVarTuple(_) => {
                Bound::TypeVarTuple(TupleArgs::ArbitraryLen(Box::new(Type::Any(cause))))
            }
            TypeVarLike::ParamSpec(_) => Bound::ParamSpec(CallableParams::Any(cause)),
        }
    }

    pub fn avoid_type_vars_from_class_self_arguments(&mut self, class: Class) {
        let is_self_type_var = match self {
            Bound::TypeVar(
                TypeVarBound::Invariant(t) | TypeVarBound::Lower(t) | TypeVarBound::Upper(t),
            ) => match t {
                Type::TypeVar(tv) if class.node_ref.as_link() == tv.in_definition => true,
                _ => false,
            },
            Bound::TypeVar(TypeVarBound::UpperAndLower(_, _)) => unreachable!(),
            Bound::TypeVarTuple(tvt) => todo!(),
            Bound::ParamSpec(p) => match p {
                CallableParams::WithParamSpec(pre, p2)
                    if pre.is_empty() && class.node_ref.as_link() == p2.in_definition =>
                {
                    true
                }
                _ => false,
            },
            Bound::Uncalculated { .. } => false,
        };
        if is_self_type_var {
            *self = Bound::Uncalculated { fallback: None };
        }
    }

    pub fn has_any(&self, i_s: &InferenceState) -> bool {
        match self {
            Self::TypeVar(
                TypeVarBound::Invariant(t) | TypeVarBound::Upper(t) | TypeVarBound::Lower(t),
            ) => t.has_any(i_s),
            Self::TypeVar(TypeVarBound::UpperAndLower(t1, t2)) => t1.has_any(i_s) | t2.has_any(i_s),
            Self::TypeVarTuple(ts) => ts.has_any(i_s),
            Self::ParamSpec(params) => match &params {
                CallableParams::Simple(params) => params
                    .iter()
                    .any(|t| t.type_.maybe_type().is_some_and(|t| t.has_any(i_s))),
                CallableParams::WithParamSpec(pre, _) => pre.iter().any(|t| t.has_any(i_s)),
                CallableParams::Any(_) => true,
            },
            Self::Uncalculated {
                fallback: Some(fallback),
            } => fallback.has_any(i_s),
            Self::Uncalculated { fallback: None } => false,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Bound2 {
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

impl Default for Bound2 {
    fn default() -> Self {
        Self::Uncalculated { fallback: None }
    }
}

impl Bound2 {
    pub fn format(
        &self,
        usage: &TypeVarLikeUsage,
        format_data: &FormatData,
        style: ParamsStyle,
    ) -> Box<str> {
        match self {
            Self::Invariant(t) | Self::Upper(t) | Self::Lower(t) | Self::UpperAndLower(t, _) => {
                t.format(format_data, style)
            }
            Self::Uncalculated { fallback } => {
                if let TypeVarLike::TypeVar(type_var) = usage.as_type_var_like() {
                    if let TypeVarKind::Bound(bound) = &type_var.kind {
                        return bound.format(format_data);
                    }
                }
                Type::Never.format(format_data)
            }
        }
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
                            *t = t.common_sub_type(i_s, other);
                            return Match::new_true();
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

    pub fn as_generic_item(
        &self,
        db: &Database,
        on_uncalculated: impl FnOnce() -> GenericItem,
    ) -> GenericItem {
        match self {
            // If the upper bound is a literal, we do not want to use the lower bound.
            Self::UpperAndLower(t @ BoundKind::TypeVar(Type::Literal(_)), _) => t.as_generic_item(),
            Self::Lower(BoundKind::TypeVar(Type::Literal(l)))
            | Self::UpperAndLower(_, BoundKind::TypeVar(Type::Literal(l)))
                if l.implicit =>
            {
                GenericItem::TypeArg(db.python_state.literal_type(&l.kind))
            }
            Self::Invariant(k) | Self::Upper(k) | Self::Lower(k) | Self::UpperAndLower(_, k) => {
                k.as_generic_item()
            }
            // Any is just ignored by the context later.
            Self::Uncalculated { .. } => on_uncalculated(),
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
}

impl BoundKind {
    fn format(&self, format_data: &FormatData, style: ParamsStyle) -> Box<str> {
        return match &self {
            Self::TypeVar(bound) => bound.format(format_data),
            Self::TypeVarTuple(ts) => ts.format(format_data),
            Self::ParamSpec(p) => p.format(format_data, style),
        };
    }

    fn is_simple_same_type(&self, i_s: &InferenceState, other: &Self) -> Match {
        match (self, other) {
            (Self::TypeVar(t1), Self::TypeVar(t2)) => t1.is_simple_same_type(i_s, t2),
            (Self::TypeVarTuple(tup1), Self::TypeVarTuple(tup2)) => todo!(),
            (Self::ParamSpec(params1), Self::ParamSpec(params2)) => todo!(),
            _ => unreachable!(),
        }
    }

    fn is_simple_super_type_of(&self, i_s: &InferenceState, other: &Self) -> Match {
        match (self, other) {
            (Self::TypeVar(t1), Self::TypeVar(t2)) => t1.is_simple_super_type_of(i_s, t2),
            (Self::TypeVarTuple(tup1), Self::TypeVarTuple(tup2)) => todo!(),
            (Self::ParamSpec(params1), Self::ParamSpec(params2)) => todo!(),
            _ => unreachable!(),
        }
    }

    fn is_simple_sub_type_of(&self, i_s: &InferenceState, other: &Self) -> Match {
        match (self, other) {
            (Self::TypeVar(t1), Self::TypeVar(t2)) => t1.is_simple_sub_type_of(i_s, t2),
            (Self::TypeVarTuple(tup1), Self::TypeVarTuple(tup2)) => todo!(),
            (Self::ParamSpec(params1), Self::ParamSpec(params2)) => todo!(),
            _ => unreachable!(),
        }
    }

    fn common_base_type(&self, i_s: &InferenceState, other: &Self) -> Self {
        match (self, other) {
            (Self::TypeVar(t1), Self::TypeVar(t2)) => Self::TypeVar(t1.common_base_type(i_s, t2)),
            (Self::TypeVarTuple(tup1), Self::TypeVarTuple(tup2)) => todo!(),
            (Self::ParamSpec(params1), Self::ParamSpec(params2)) => todo!(),
            _ => unreachable!(),
        }
    }

    fn common_sub_type(&self, i_s: &InferenceState, other: &Self) -> Self {
        match (self, other) {
            (Self::TypeVar(t1), Self::TypeVar(t2)) => {
                Self::TypeVar(t1.common_sub_type(i_s, t2).unwrap_or(Type::Never))
            }
            (Self::TypeVarTuple(tup1), Self::TypeVarTuple(tup2)) => todo!(),
            (Self::ParamSpec(params1), Self::ParamSpec(params2)) => todo!(),
            _ => unreachable!(),
        }
    }

    fn search_type_vars<C: FnMut(TypeVarLikeUsage) + ?Sized>(&self, found_type_var: &mut C) {
        match self {
            BoundKind::TypeVar(t) => t.search_type_vars(found_type_var),
            BoundKind::TypeVarTuple(tup) => tup.search_type_vars(found_type_var),
            BoundKind::ParamSpec(params) => params.search_type_vars(found_type_var),
        }
    }

    fn as_generic_item(&self) -> GenericItem {
        match self {
            Self::TypeVar(t) => GenericItem::TypeArg(t.clone()),
            Self::TypeVarTuple(ts) => GenericItem::TypeArgs(TypeArgs::new(ts.clone())),
            Self::ParamSpec(param_spec) => GenericItem::ParamSpecArg(ParamSpecArg {
                params: param_spec.clone(),
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
            BoundKind::TypeVar(t) => t.has_any(i_s),
            BoundKind::TypeVarTuple(ts) => ts.has_any(i_s),
            BoundKind::ParamSpec(params) => params.has_any(i_s),
        }
    }
}
