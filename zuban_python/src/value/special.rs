use super::{LookupResult, Value, ValueKind};
use crate::database::DbType;
use crate::getitem::SliceType;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::matching::{ResultContext, Type};
use crate::{
    database::{Database, SpecialType},
    node_ref::NodeRef,
};

#[derive(Debug)]
pub struct SpecialTypeAsValue<'a> {
    db: &'a Database,
    special_type: &'a dyn SpecialType,
    db_type_ptr: &'a DbType,
}

impl<'a> SpecialTypeAsValue<'a> {
    pub fn new(
        db: &'a Database,
        special_type: &'a dyn SpecialType,
        db_type_ptr: &'a DbType,
    ) -> Self {
        Self {
            db,
            special_type,
            db_type_ptr,
        }
    }
}

impl<'db, 'a> Value<'db, 'a> for SpecialTypeAsValue<'a> {
    fn kind(&self) -> ValueKind {
        self.special_type.kind()
    }

    fn name(&self) -> &'a str {
        self.special_type.name(self.db)
    }

    fn lookup_internal(
        &self,
        i_s: &InferenceState,
        node_ref: Option<NodeRef>,
        name: &str,
    ) -> LookupResult {
        self.special_type.lookup_internal(i_s, node_ref, name)
    }

    fn as_type(&self, i_s: &InferenceState<'db, '_>) -> Type<'a> {
        Type::new(self.db_type_ptr)
    }

    fn get_item(
        &self,
        i_s: &InferenceState,
        slice_type: &SliceType,
        result_context: &mut ResultContext,
    ) -> Inferred {
        self.special_type.get_item(i_s, slice_type, result_context)
    }
}
