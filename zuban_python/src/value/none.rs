use super::{ClassLike, LookupResult, Value, ValueKind};
use crate::debug;
use crate::getitem::SliceType;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;

#[derive(Debug)]
pub struct NoneInstance();

impl<'db, 'a> Value<'db, 'a> for NoneInstance {
    fn kind(&self) -> ValueKind {
        ValueKind::Constant
    }

    fn name(&self) -> &'db str {
        "None"
    }

    fn lookup_internal(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> LookupResult<'db> {
        debug!("TODO None lookup");
        LookupResult::None
    }

    fn class(&self, i_s: &mut InferenceState<'db, '_>) -> ClassLike<'db, 'a> {
        ClassLike::None
    }

    fn is_none(&self) -> bool {
        true
    }

    fn get_item(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        slice_type: &SliceType<'db, '_>,
    ) -> Inferred<'db> {
        debug!("TODO None[...]");
        Inferred::new_any()
    }
}
