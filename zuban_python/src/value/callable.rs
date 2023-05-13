use super::{Class, LookupResult, OnTypeError};
use crate::arguments::Arguments;
use crate::database::{CallableContent, DbType};
use crate::debug;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::matching::{calculate_callable_type_vars_and_return, ResultContext, Type};
use crate::node_ref::NodeRef;

#[derive(Debug, Copy, Clone)]
pub struct Callable<'a> {
    pub db_type: &'a DbType,
    pub content: &'a CallableContent,
}

impl<'a> Callable<'a> {
    pub fn new(db_type: &'a DbType, content: &'a CallableContent) -> Self {
        Self { db_type, content }
    }

    pub fn execute_internal<'db>(
        &self,
        i_s: &InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        on_type_error: OnTypeError<'db, '_>,
        class: Option<&Class>,
        result_context: &mut ResultContext,
    ) -> Inferred {
        let calculated_type_vars = calculate_callable_type_vars_and_return(
            i_s,
            class,
            self.content,
            args.iter(),
            &|| args.as_node_ref(),
            result_context,
            on_type_error,
        );
        let g_o = Type::new(&self.content.result_type);
        g_o.execute_and_resolve_type_vars(i_s, None, None, &calculated_type_vars)
    }

    pub fn lookup(
        &self,
        i_s: &InferenceState,
        node_ref: Option<NodeRef>,
        name: &str,
    ) -> LookupResult {
        debug!("TODO callable lookups");
        LookupResult::None
    }
}
