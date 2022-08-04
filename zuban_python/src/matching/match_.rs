use std::ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign};
use std::rc::Rc;

use crate::database::{DbType, TypeVar, TypeVarIndex};

pub enum SignatureMatch {
    False,
    FalseButSimilar,
    TrueWithAny(Vec<usize>),
    True,
}

#[derive(Clone, Debug)]
pub enum Match {
    False(MismatchReason),
    FalseButSimilar(MismatchReason),
    TrueWithAny,
    True,
}

#[derive(Clone, Debug)]
pub enum MismatchReason {
    None,
    CannotInferTypeArgument(TypeVarIndex),
    ConstraintMismatch {
        expected: DbType,
        type_var: Rc<TypeVar>,
    },
}

impl Match {
    pub fn new_false() -> Self {
        Self::False(MismatchReason::None)
    }

    pub fn bool(&self) -> bool {
        matches!(self, Self::True | Self::TrueWithAny)
    }
}

impl BitAnd for Match {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        match self {
            Self::True => rhs,
            Self::TrueWithAny => match rhs {
                Self::True => Self::TrueWithAny,
                _ => rhs,
            },
            Self::FalseButSimilar(reason) => match rhs {
                Self::False(_) => Self::False(reason),
                _ => Self::FalseButSimilar(reason),
            },
            Self::False(reason) => Self::False(reason),
        }
    }
}

impl BitOr for Match {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        match self {
            Self::True => Self::True,
            Self::TrueWithAny => match rhs {
                Self::True => Self::True,
                _ => Self::TrueWithAny,
            },
            Self::FalseButSimilar(_) => match rhs {
                Self::True => Self::True,
                _ => self,
            },
            Self::False(_) => rhs,
        }
    }
}

impl BitAndAssign for Match {
    fn bitand_assign(&mut self, rhs: Self) {
        let left = std::mem::replace(self, Match::True);
        *self = left & rhs
    }
}

impl BitOrAssign for Match {
    fn bitor_assign(&mut self, rhs: Self) {
        let left = std::mem::replace(self, Match::True);
        *self = left | rhs
    }
}

impl From<bool> for Match {
    fn from(item: bool) -> Self {
        match item {
            true => Match::True,
            _ => Match::False(MismatchReason::None),
        }
    }
}
