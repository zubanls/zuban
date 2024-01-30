use super::super::{FormatData, Match};
use crate::{
    database::Database,
    inference_state::InferenceState,
    type_::{FormatStyle, Type, TypeVar, TypeVarKind, Variance},
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
