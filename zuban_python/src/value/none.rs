use super::{LookupResult, Value, ValueKind};
use crate::database::DbType;
use crate::debug;
use crate::getitem::SliceType;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::matching::Type;

#[derive(Debug)]
pub struct NoneInstance();

impl<'a> Value<'a> for NoneInstance {
    fn kind(&self) -> ValueKind {
        ValueKind::Constant
    }

    fn name(&self) -> &'a str {
        "None"
    }

    fn lookup_internal(&self, i_s: &mut InferenceState, name: &str) -> LookupResult {
        debug!("TODO None lookup");
        LookupResult::None
    }

    fn as_type<'db: 'a>(&self, i_s: &mut InferenceState<'db, '_>) -> Type<'a> {
        Type::new(&DbType::None)
    }

    fn is_none(&self) -> bool {
        true
    }

    fn get_item(&self, i_s: &mut InferenceState, slice_type: &SliceType) -> Inferred {
        debug!("TODO None[...]");
        Inferred::new_any()
    }
}
