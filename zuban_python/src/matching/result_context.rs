use std::fmt;

use super::Type;
use crate::database::DbType;
use crate::InferenceState;

#[derive(Clone, Copy)]
pub enum ResultContext<'db, 'a> {
    Known(&'a Type<'db, 'a>),
    LazyKnown(&'a dyn Fn(&mut InferenceState<'db, '_>) -> DbType),
    Unknown,
}

impl<'db, 'a> ResultContext<'db, 'a> {
    pub fn with_type_if_exists(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        mut callable: impl FnMut(&mut InferenceState<'db, '_>, &Type<'db, '_>),
    ) {
        match self {
            Self::Known(t) => callable(i_s, t),
            Self::LazyKnown(c) => {
                let t = c(i_s);
                callable(i_s, &Type::from_db_type(i_s.db, &t))
            }
            Self::Unknown => (),
        }
    }
}

impl fmt::Debug for ResultContext<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Known(t) => write!(f, "Known({t:?})"),
            Self::LazyKnown(c) => write!(f, "LazyKnown(_)"),
            Self::Unknown => write!(f, "UnKnown"),
        }
    }
}
