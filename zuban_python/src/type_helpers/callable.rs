use super::function::{format_pretty_function_like, format_pretty_function_with_params};
use super::Class;
use crate::arguments::Arguments;
use crate::database::{CallableContent, CallableParams, Database, DbType, FormatStyle};
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
            &calculated_type_vars,
            self.defined_in.as_ref(),
            &mut || {
                self.defined_in
                    .map(|c| c.as_db_type(i_s.db))
                    .unwrap_or(DbType::Self_)
            },
        )
    }
}

pub fn format_pretty_callable(format_data: &FormatData, callable: &CallableContent) -> Box<str> {
    let db = format_data.db;
    let not_reveal_type = format_data.style != FormatStyle::MypyRevealType;
    let name = callable
        .name
        .and_then(|s| not_reveal_type.then(|| s.as_str(db)))
        .unwrap_or("");
    match &callable.params {
        CallableParams::Simple(params) => {
            let first_param = params
                .iter()
                .next()
                .and_then(|p| p.param_specific.maybe_positional_db_type())
                .map(|t| t.format(format_data));
            format_pretty_function_like(
                format_data,
                None,
                callable.class_name.map(|c| c.as_str(db)) == first_param.as_deref()
                    && not_reveal_type,
                name,
                callable.type_vars.as_ref(),
                params.iter(),
                Some(Type::new(&callable.result_type)),
            )
        }
        CallableParams::WithParamSpec(pre_types, usage) => {
            if !pre_types.is_empty() {
                todo!()
            }
            let spec = usage.param_spec.name(db);
            format_pretty_function_with_params(
                format_data,
                None,
                callable.type_vars.as_ref(),
                Some(Type::new(&callable.result_type)),
                name,
                &format!("*{spec}.args, **{spec}.kwargs"),
            )
        }
        CallableParams::Any => format!(
            "def {name}(*Any, **Any) -> {}",
            callable.result_type.format(format_data)
        )
        .into(),
    }
}
