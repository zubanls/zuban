use std::ops::{BitAnd, BitAndAssign};
use std::rc::Rc;

use crate::database::{DbType, PointLink, TypeVar, TypeVarIndex};

#[derive(Debug)]
pub struct ArgumentIndexWithParam {
    pub argument_index: usize,
    pub param_annotation_link: PointLink,
}

#[derive(Debug)]
pub enum SignatureMatch {
    False,
    FalseButSimilar,
    TrueWithAny {
        argument_indices: Box<[ArgumentIndexWithParam]>,
    },
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

    pub fn similar_if_false(self) -> Self {
        match self {
            Self::False(reason) => Self::FalseButSimilar(reason),
            _ => self,
        }
    }

    pub fn or(self, mut callable: impl FnOnce() -> Self) -> Self {
        if self.bool() {
            self
        } else {
            let result = callable();
            if result.bool() || matches!(self, Match::False(MismatchReason::None)) {
                result
            } else {
                self
            }
        }
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

impl BitAndAssign for Match {
    fn bitand_assign(&mut self, rhs: Self) {
        let left = std::mem::replace(self, Match::True);
        *self = left & rhs
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
