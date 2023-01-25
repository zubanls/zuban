use super::{LookupResult, Module, Value, ValueKind};
use crate::database::{Database, DbType, Literal as DbLiteral};
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
    fn kind(&self) -> ValueKind {
        self.value.kind()
    }

    fn name(&self) -> &str {
        self.value.name()
    }

    fn qualified_name(&self, db: &'a Database) -> String {
        self.value.qualified_name(db)
    }

    fn module(&self, db: &'a Database) -> Module<'a> {
        self.value.module(db)
    }

    fn description(&self, i_s: &mut InferenceState) -> String {
        self.value.description(i_s)
    }

    fn lookup_internal(&self, i_s: &mut InferenceState, name: &str) -> LookupResult {
        self.value.lookup_internal(i_s, name)
    }

    fn should_add_lookup_error(&self, i_s: &mut InferenceState) -> bool {
        self.value.should_add_lookup_error(i_s)
    }

    fn as_type(&self, i_s: &mut InferenceState<'db, '_>) -> Type<'a> {
        Type::owned(DbType::Literal(self.db_literal))
    }
}
