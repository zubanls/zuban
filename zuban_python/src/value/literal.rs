use super::{LookupResult, Module, Value};
use crate::database::{Database, DbType, Literal as DbLiteral};
use crate::inference_state::InferenceState;
use crate::matching::Type;
use crate::node_ref::NodeRef;

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

    fn qualified_name(&self, db: &'a Database) -> String {
        self.value.qualified_name(db)
    }

    fn module(&self, db: &'a Database) -> Module<'a> {
        self.value.module(db)
    }

    fn lookup_internal(
        &self,
        i_s: &InferenceState,
        node_ref: Option<NodeRef>,
        name: &str,
    ) -> LookupResult {
        self.value.lookup_internal(i_s, node_ref, name)
    }

    fn should_add_lookup_error(&self, db: &Database) -> bool {
        self.value.should_add_lookup_error(db)
    }

    fn as_type(&self, i_s: &InferenceState<'db, '_>) -> Type<'a> {
        Type::owned(DbType::Literal(self.db_literal))
    }
}
