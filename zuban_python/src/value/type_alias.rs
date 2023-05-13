use std::rc::Rc;

use super::Value;

use crate::database::{DbType, TypeAlias as DbTypeAlias};

use crate::inference_state::InferenceState;
use crate::matching::Type;

#[derive(Debug)]
pub struct TypeAlias<'a> {
    alias: &'a DbTypeAlias,
}

impl<'db, 'a> Value<'db, 'a> for TypeAlias<'a> {
    fn as_type(&self, i_s: &InferenceState<'db, '_>) -> Type<'a> {
        Type::owned(DbType::Type(Rc::new(
            self.alias.as_db_type_and_set_type_vars_any(i_s.db),
        )))
    }
}
