use super::Instance;
use crate::{
    arguments::Args,
    inference_state::InferenceState,
    inferred::Inferred,
    matching::{LookupKind, OnTypeError, ResultContext},
};

pub(crate) fn method_with_fallback<'db, 'x, T>(
    i_s: &InferenceState<'db, '_>,
    args: &dyn Args<'db>,
    result_context: &mut ResultContext,
    on_type_error: OnTypeError,
    td: T,
    name: &str,
    handler: fn(i_s: &InferenceState<'db, '_>, td: T, args: &dyn Args<'db>) -> Option<Inferred>,
    fallback_instance: impl FnOnce() -> Instance<'x>,
) -> Inferred {
    handler(i_s, td, args).unwrap_or_else(|| {
        fallback_instance()
            .lookup(
                i_s,
                |issue| args.add_issue(i_s, issue),
                name,
                LookupKind::OnlyType,
            )
            .into_inferred()
            .execute_with_details(i_s, args, result_context, on_type_error)
    })
}
