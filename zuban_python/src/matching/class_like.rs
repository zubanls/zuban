use super::Match;
use crate::database::{Database, DbType, Variance};
use crate::inference_state::InferenceState;
use crate::value::{Class, LookupResult, MroIterator};

#[derive(Debug, Clone, Copy)]
pub enum ClassLikeLegacy<'db, 'a> {
    Class(Class<'db, 'a>),
}

impl<'db, 'a> ClassLikeLegacy<'db, 'a> {
    fn is_object_class(&self, db: &Database) -> Match {
        match self {
            Self::Class(c) => c.is_object_class(db),
            _ => Match::new_false(),
        }
    }

    fn mro(&self, i_s: &mut InferenceState<'db, '_>) -> MroIterator<'db, '_> {
        match self {
            Self::Class(c) => c.mro(i_s),
            _ => todo!(), //MroIterator::new(i_s.db, *self, None, [].iter()),
        }
    }
}
