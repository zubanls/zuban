use super::{LookupResult, Value};
use crate::database::DbType;
use crate::debug;
use crate::inference_state::InferenceState;
use crate::matching::Type;
use crate::node_ref::NodeRef;

#[derive(Debug)]
pub struct NoneInstance();

impl NoneInstance {
    pub fn lookup(
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
    fn as_type(&self, i_s: &InferenceState<'db, '_>) -> Type<'a> {
        Type::new(&DbType::None)
    }
}
