use super::{LookupResult, Value};
use crate::database::DbType;
use crate::debug;
use crate::getitem::SliceType;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::matching::{ResultContext, Type};
use crate::node_ref::NodeRef;

#[derive(Debug)]
pub struct NoneInstance();

impl NoneInstance {
    pub fn lookup_internal(
        &self,
        i_s: &InferenceState,
        node_ref: Option<NodeRef>,
        name: &str,
    ) -> LookupResult {
        debug!("TODO None lookup");
        LookupResult::None
    }
}

impl<'db, 'a> Value<'db, 'a> for NoneInstance {
    fn name(&self) -> &str {
        "None"
    }

    fn as_type(&self, i_s: &InferenceState<'db, '_>) -> Type<'a> {
        Type::new(&DbType::None)
    }

    fn is_none(&self) -> bool {
        true
    }

    fn get_item(
        &self,
        i_s: &InferenceState,
        slice_type: &SliceType,
        result_context: &mut ResultContext,
    ) -> Inferred {
        debug!("TODO None[...]");
        Inferred::new_any()
    }
}
