use super::Value;
use crate::database::{DbType, Literal as DbLiteral};
use crate::inference_state::InferenceState;
use crate::matching::Type;

#[derive(Debug, Copy, Clone)]
pub struct Literal<'db, 'a, 'b> {
    db_literal: DbLiteral,
    value: &'b dyn Value<'db, 'a>,
}

impl<'db, 'a, 'b> Literal<'db, 'a, 'b> {
    pub fn new(db_literal: DbLiteral, value: &'b dyn Value<'db, 'a>) -> Self {
        Self { db_literal, value }
    }
}

impl<'db, 'a> Value<'db, 'a> for Literal<'db, 'a, '_> {
    fn name(&self) -> &str {
        self.value.name()
    }

    fn as_type(&self, i_s: &InferenceState<'db, '_>) -> Type<'a> {
        Type::owned(DbType::Literal(self.db_literal))
    }
}
