use std::sync::Arc;

use crate::{
    arguments::Args,
    inference_state::InferenceState,
    inferred::Inferred,
    matching::{OnTypeError, ResultContext},
    type_::Type,
};

type CustomBehaviorCallback = for<'db> fn(
    i_s: &InferenceState<'db, '_>,
    args: &dyn Args<'db>,
    result_context: &mut ResultContext,
    on_type_error: OnTypeError,
    bound: Option<&Type>,
) -> Inferred;

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
enum CustomBehaviorKind {
    Method { bound: Option<Arc<Type>> },
}

#[allow(clippy::derived_hash_with_manual_eq)]
#[derive(Debug, Eq, Hash, Clone)]
pub(crate) struct CustomBehavior {
    callback: CustomBehaviorCallback,
    kind: CustomBehaviorKind,
}

impl PartialEq for CustomBehavior {
    fn eq(&self, _: &Self) -> bool {
        // For now these simply don't match, I'm not sure it's important that they ever do.
        // PartialEq is implemented more as a "quickly check if the types are exactly the same,
        // otherwise simply fall back to normal type matching behavior, which is much more complex
        // anyways".
        false
    }
}

impl CustomBehavior {
    pub(crate) fn new_method(callback: CustomBehaviorCallback, bound: Option<Arc<Type>>) -> Self {
        Self {
            callback,
            kind: CustomBehaviorKind::Method { bound },
        }
    }

    pub fn bind(&self, bound: Arc<Type>) -> Self {
        Self {
            callback: self.callback,
            kind: match self.kind {
                CustomBehaviorKind::Method { bound: None } => {
                    CustomBehaviorKind::Method { bound: Some(bound) }
                }
                _ => self.kind.clone(),
            },
        }
    }

    pub(crate) fn execute<'db>(
        &self,
        i_s: &InferenceState<'db, '_>,
        args: &dyn Args<'db>,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError,
    ) -> Inferred {
        let bound = match &self.kind {
            CustomBehaviorKind::Method { bound } => bound.as_deref(),
        };
        (self.callback)(i_s, args, result_context, on_type_error, bound)
    }
}
