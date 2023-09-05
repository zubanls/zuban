use crate::{
    file::infer_string_index,
    getitem::{SliceType, SliceTypeContent},
    inference_state::InferenceState,
    inferred::Inferred,
    matching::{LookupKind, ResultContext},
};

use super::Instance;

pub struct TypedDictHelper<'a>(pub Instance<'a>);

impl<'a> TypedDictHelper<'a> {
    pub fn get_item(
        &self,
        i_s: &InferenceState,
        slice_type: &SliceType,
        result_context: &mut ResultContext,
    ) -> Inferred {
        match slice_type.unpack() {
            SliceTypeContent::Simple(simple) => infer_string_index(i_s, simple, |name| {
                self.0
                    .lookup(i_s, slice_type.as_node_ref(), name, LookupKind::Normal)
                    .into_maybe_inferred()
                    .or_else(|| todo!())
            }),
            SliceTypeContent::Slice(_) => todo!(),
            SliceTypeContent::Slices(_) => todo!(),
        }
    }
}
