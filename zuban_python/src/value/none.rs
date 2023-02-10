use super::{LookupResult, Value, ValueKind};
use crate::database::DbType;
use crate::debug;
use crate::getitem::SliceType;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::matching::{ResultContext, Type};
use crate::node_ref::NodeRef;

#[derive(Debug)]
pub struct NoneInstance();

impl<'db, 'a> Value<'db, 'a> for NoneInstance {
    fn kind(&self) -> ValueKind {
        ValueKind::Constant
    }

    fn name(&self) -> &str {
        "None"
    }

    fn lookup_internal(
        &self,
        i_s: &mut InferenceState,
        node_ref: Option<NodeRef>,
        name: &str,
    ) -> LookupResult {
        debug!("TODO None lookup");
        LookupResult::None
    }

    fn as_type(&self, i_s: &mut InferenceState<'db, '_>) -> Type<'a> {
        Type::new(&DbType::None)
    }

    fn is_none(&self) -> bool {
        true
    }

    fn get_item(
        &self,
        i_s: &mut InferenceState,
        slice_type: &SliceType,
        result_context: &mut ResultContext,
    ) -> Inferred {
        debug!("TODO None[...]");
        Inferred::new_any()
    }
}
