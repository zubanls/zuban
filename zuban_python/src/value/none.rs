use super::{ClassLike, LookupResult, Value, ValueKind};
use crate::inference_state::InferenceState;

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
        todo!()
    }

    fn class(&self, i_s: &mut InferenceState<'db, '_>) -> ClassLike<'db, 'a> {
        todo!()
    }

    fn is_none(&self) -> bool {
        true
    }
}
