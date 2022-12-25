use super::{LookupResult, Module, OnLookupError, Value, ValueKind};
use crate::database::{Database, DbType, Literal as DbLiteral};
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::matching::Type;
use crate::node_ref::NodeRef;

#[derive(Debug, Copy, Clone)]
pub struct Literal<'db, 'a, 'b> {
    node_ref: NodeRef<'a>,
    value: &'b dyn Value<'db, 'a>,
}

impl<'db, 'a, 'b> Literal<'db, 'a, 'b> {
    pub fn new(node_ref: NodeRef<'a>, value: &'b dyn Value<'db, 'a>) -> Self {
        Self { node_ref, value }
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

    fn lookup(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        name: &str,
        on_error: OnLookupError<'db, '_>,
    ) -> LookupResult {
        self.value.lookup(i_s, name, on_error)
    }

    fn lookup_implicit(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        name: &str,
        on_error: OnLookupError<'db, '_>,
    ) -> Inferred {
        self.value.lookup_implicit(i_s, name, on_error)
    }

    fn as_module(&self) -> Option<&Module<'a>> {
        None
    }

    fn as_type(&self, i_s: &mut InferenceState<'db, '_>) -> Type<'a> {
        Type::owned(DbType::Literal(DbLiteral {
            definition: self.node_ref.as_link(),
            implicit: false,
        }))
    }
}
