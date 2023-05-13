use super::LookupResult;
use crate::debug;
use crate::inference_state::InferenceState;
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
