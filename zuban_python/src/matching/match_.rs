use std::ops::{BitAnd, BitAndAssign};
use std::rc::Rc;

use crate::type_::{DbType, TypeVar};

#[derive(Debug)]
pub struct ArgumentIndexWithParam {
    pub argument_index: usize,
    pub type_: DbType,
}

#[derive(Debug)]
pub enum SignatureMatch {
    False {
        similar: bool,
    },
    TrueWithAny {
        argument_indices: Box<[ArgumentIndexWithParam]>,
    },
    True {
        arbitrary_length_handled: bool,
    },
}

impl SignatureMatch {
    pub fn new_true() -> Self {
        Self::True {
            arbitrary_length_handled: true,
        }
    }
    pub fn bool(&self) -> bool {
        matches!(self, Self::True { .. } | Self::TrueWithAny { .. })
    }
}

#[derive(Debug)]
pub enum Match {
    False {
        similar: bool,
        reason: MismatchReason,
    },
    True {
        with_any: bool,
    },
}

#[derive(Clone, Debug)]
pub enum MismatchReason {
    None,
    ConstraintMismatch {
        expected: DbType,
        type_var: Rc<TypeVar>,
    },
    ProtocolMismatches {
        notes: Box<[Box<str>]>,
    },
    SequenceInsteadOfListNeeded,
    MappingInsteadOfDictNeeded,
}

impl Match {
    pub const fn new_false() -> Self {
        Self::False {
            reason: MismatchReason::None,
            similar: false,
        }
    }

    pub const fn new_true() -> Self {
        Self::True { with_any: false }
    }

    pub fn any<T>(items: impl Iterator<Item = T>, mut callable: impl FnMut(T) -> Self) -> Self {
        let mut result = Self::new_true();
        for item in items {
            let r = callable(item);
            if r.bool() {
                return r;
            }
            result &= r;
        }
        result
    }

    pub fn all<T>(items: impl Iterator<Item = T>, mut callable: impl FnMut(T) -> Self) -> Self {
        let mut result = Self::new_true();
        for item in items {
            result &= callable(item);
        }
        result
    }

    pub fn bool(&self) -> bool {
        matches!(self, Self::True { .. })
    }

    pub fn similar_if_false(self) -> Self {
        match self {
            Self::False {
                reason,
                similar: false,
            } => Self::False {
                reason,
                similar: true,
            },
            _ => self,
        }
    }

    #[inline]
    pub fn or(self, callable: impl FnOnce() -> Self) -> Self {
        if self.bool() {
            self
        } else {
            let result = callable();
            if result.bool()
                || matches!(
                    self,
                    Match::False {
                        reason: MismatchReason::None,
                        similar: false
                    }
                )
            {
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
            Self::True { with_any: false } => rhs,
            Self::True { with_any: true } => match rhs {
                Self::True { with_any: false } => Self::True { with_any: true },
                _ => rhs,
            },
            Self::False {
                reason,
                similar: true,
            } => match rhs {
                Self::False { similar: false, .. } => Self::False {
                    reason,
                    similar: false,
                },
                _ => Self::False {
                    reason,
                    similar: true,
                },
            },
            Self::False { .. } => self,
        }
    }
}

impl BitAndAssign for Match {
    fn bitand_assign(&mut self, rhs: Self) {
        let left = std::mem::replace(self, Match::new_true());
        *self = left & rhs
    }
}

impl From<bool> for Match {
    fn from(item: bool) -> Self {
        match item {
            true => Match::new_true(),
            _ => Match::new_false(),
        }
    }
}
