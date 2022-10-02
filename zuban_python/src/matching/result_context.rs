use std::fmt;

use super::Type;
use crate::database::DbType;
use crate::InferenceState;

#[derive(Clone, Copy)]
pub enum ResultContext<'a> {
    Known(&'a Type<'a>),
    LazyKnown(&'a dyn Fn(&mut InferenceState) -> DbType),
    Unknown,
}

impl<'a> ResultContext<'a> {
    pub fn with_type_if_exists<T>(
        &self,
        i_s: &mut InferenceState,
        callable: impl FnOnce(&mut InferenceState, &Type<'_>) -> T,
    ) -> Option<T> {
        match self {
            Self::Known(t) => Some(callable(i_s, t)),
            Self::LazyKnown(c) => {
                let t = c(i_s);
                Some(callable(i_s, &Type::new(&t)))
            }
            Self::Unknown => None,
        }
    }
}

impl fmt::Debug for ResultContext<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Known(t) => write!(f, "Known({t:?})"),
            Self::LazyKnown(c) => write!(f, "LazyKnown(_)"),
            Self::Unknown => write!(f, "UnKnown"),
        }
    }
}
