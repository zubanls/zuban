use super::function::format_pretty_function_like;
use super::Class;
use crate::arguments::Arguments;
use crate::database::{CallableContent, CallableParams, DbType};
use crate::debug;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::matching::{
    calculate_callable_type_vars_and_return, LookupResult, OnTypeError, ResultContext, Type,
};
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

pub fn format_pretty_callable(i_s: &InferenceState, callable: &CallableContent) -> Box<str> {
    match &callable.params {
        CallableParams::Simple(params) => {
            let x = params
                .iter()
                .next()
                .and_then(|p| p.param_specific.maybe_positional_db_type())
                .map(|t| t.format_short(i_s.db));
            format_pretty_function_like(
                i_s,
                None,
                callable.class_name.map(|c| c.as_str(i_s.db)) == x.as_deref(),
                callable.name.map(|s| s.as_str(i_s.db)).unwrap_or(""),
                callable.type_vars.as_ref(),
                params.iter(),
                Some(Type::new(&callable.result_type)),
            )
        }
        CallableParams::WithParamSpec(_, _) => todo!(),
        CallableParams::Any => todo!(),
    }
}
