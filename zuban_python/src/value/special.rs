use super::{Value, ValueKind};
use crate::inference_state::InferenceState;
use crate::{
    database::{Database, SpecialType},
    node_ref::NodeRef,
};

#[derive(Debug)]
pub struct SpecialTypeAsValue<'a> {
    db: &'a Database,
    special_type: &'a dyn SpecialType,
}

impl<'a> SpecialTypeAsValue<'a> {
    pub fn new(db: &'a Database, special_type: &'a dyn SpecialType) -> Self {
        Self { db, special_type }
    }
}

impl<'db, 'a> Value<'db, 'a> for SpecialTypeAsValue<'a> {
    fn kind(&self) -> ValueKind {
        ValueKind::Object
    }

    fn name(&self) -> &'a str {
        self.special_type.name(self.db)
    }

    fn lookup_internal(
        &self,
        i_s: &InferenceState,
        node_ref: Option<NodeRef>,
        name: &str,
    ) -> super::LookupResult {
        todo!()
    }
}
