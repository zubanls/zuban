use super::super::{FormatData, Match};
use crate::{
    database::Database,
    inference_state::InferenceState,
    type_::{
        CallableParams, FormatStyle, GenericItem, TupleArgs, Type, TypeVar, TypeVarKind,
        TypeVarLikeUsage, Variance,
    },
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
            Self::TypeVarTuple(tup) => Bound::TypeVarTuple(tup.replace_type_var_likes_and_self(
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
}

/*
#[derive(Debug, Clone, PartialEq)]
enum BoundKind {
    TypeVar(Type),
    TypeVarTuple(TupleArgs),
    ParamSpec(CallableParams),

    Invariant(BoundKind),
    Upper(BoundKind),
    UpperAndLower(BoundKind, BoundKind),
    Lower(BoundKind),
}
*/
