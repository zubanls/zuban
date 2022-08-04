use std::ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign};

pub enum SignatureMatch {
    False,
    FalseButSimilar,
    TrueWithAny(Vec<usize>),
    True,
}

#[derive(Clone, Debug)]
pub enum Match {
    False,
    FalseButSimilar,
    TrueWithAny,
    True,
}

impl Match {
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
            Self::FalseButSimilar => match rhs {
                Self::False => Self::False,
                _ => self,
            },
            Self::False => Self::False,
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
            Self::FalseButSimilar => match rhs {
                Self::True => Self::True,
                _ => self,
            },
            Self::False => rhs,
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
            _ => Match::False,
        }
    }
}
