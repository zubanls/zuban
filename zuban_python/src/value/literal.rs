use super::Value;
use crate::database::{DbType, Literal as DbLiteral};
use crate::inference_state::InferenceState;
use crate::matching::Type;

#[derive(Debug, Copy, Clone)]
pub struct Literal {
    db_literal: DbLiteral,
}

impl<'db, 'a, 'b> Literal {
    pub fn new(db_literal: DbLiteral) -> Self {
        Self { db_literal }
    }
}

impl<'db, 'a> Value<'db, 'a> for Literal {
    fn as_type(&self, i_s: &InferenceState<'db, '_>) -> Type<'a> {
        Type::owned(DbType::Literal(self.db_literal))
    }
}
