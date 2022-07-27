use super::{LookupResult, Value, ValueKind};
use crate::debug;
use crate::getitem::SliceType;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::matching::ClassLike;

#[derive(Debug)]
pub struct NeverInstance();

impl<'db, 'a> Value<'db, 'a> for NeverInstance {
    fn kind(&self) -> ValueKind {
        ValueKind::Constant
    }

    fn name(&self) -> &'db str {
        "<nothing>"
    }

    fn lookup_internal(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> LookupResult<'db> {
        debug!("TODO None lookup");
        todo!("TODO report error for never.{name}");
        //LookupResult::None
    }

    fn class(&self, i_s: &mut InferenceState<'db, '_>) -> ClassLike<'db, 'a> {
        ClassLike::Never
    }

    fn get_item(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        slice_type: &SliceType<'db, '_>,
    ) -> Inferred<'db> {
        todo!("TODO report error for never[...]");
        //Inferred::new_any()
    }
}
