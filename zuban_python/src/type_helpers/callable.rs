use super::function::format_pretty_function_like;
use super::Class;
use crate::arguments::Arguments;
use crate::database::{CallableContent, CallableParams, Database};
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::matching::{
    calculate_callable_type_vars_and_return, FormatData, OnTypeError, ResultContext, Type,
};

#[derive(Debug, Copy, Clone)]
pub struct Callable<'a> {
    pub content: &'a CallableContent,
    pub defined_in: Option<Class<'a>>,
}

impl<'a> Callable<'a> {
    pub fn new(content: &'a CallableContent, defined_in: Option<Class<'a>>) -> Self {
        Self {
            content,
            defined_in,
        }
    }

    pub fn diagnostic_string(&self, db: &Database) -> Option<String> {
        self.content.name.map(|n| {
            let name = n.as_str(db);
            match self.content.class_name {
                Some(c) => format!("\"{}\" of \"{}\"", name, c.as_str(db)),
                None => format!("\"{name}\""),
            }
        })
    }

    pub fn execute<'db>(
        &self,
        i_s: &InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        on_type_error: OnTypeError<'db, '_>,
        result_context: &mut ResultContext,
    ) -> Inferred {
        let calculated_type_vars = calculate_callable_type_vars_and_return(
            i_s,
            self.defined_in.as_ref(),
            *self,
            args.iter(),
            &|| args.as_node_ref(),
            false,
            result_context,
            Some(on_type_error),
        );
        let g_o = Type::new(&self.content.result_type);
        g_o.execute_and_resolve_type_vars(
            i_s,
            self.defined_in.as_ref(),
            self.defined_in.as_ref(),
            &calculated_type_vars,
        )
    }
}

pub fn format_pretty_callable(format_data: &FormatData, callable: &CallableContent) -> Box<str> {
    let db = format_data.db;
    let name = callable.name.map(|s| s.as_str(db)).unwrap_or("");
    match &callable.params {
        CallableParams::Simple(params) => {
            let first_param = params
                .iter()
                .next()
                .and_then(|p| p.param_specific.maybe_positional_db_type())
                .map(|t| t.format_short(db));
            format_pretty_function_like(
                format_data,
                None,
                callable.class_name.map(|c| c.as_str(db)) == first_param.as_deref(),
                name,
                callable.type_vars.as_ref(),
                params.iter(),
                Some(Type::new(&callable.result_type)),
            )
        }
        CallableParams::WithParamSpec(_, _) => todo!(),
        CallableParams::Any => format!(
            "def {name}(*Any, **Any) -> {}",
            callable.result_type.format_short(db)
        )
        .into(),
    }
}
