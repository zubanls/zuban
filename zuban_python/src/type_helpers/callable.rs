use super::Class;
use crate::{
    arguments::Args,
    database::Database,
    diagnostics::IssueType,
    inference_state::InferenceState,
    inferred::Inferred,
    matching::{calculate_callable_type_vars_and_return, OnTypeError, ResultContext},
    type_::{CallableContent, Type},
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
        self.content.name.as_ref().map(|n| {
            let name = n.as_str(db);
            match self.content.class_name {
                Some(c) => format!("\"{}\" of \"{}\"", name, c.as_str(db)),
                None => format!("\"{name}\""),
            }
        })
    }

    pub(crate) fn execute<'db>(
        &self,
        i_s: &InferenceState<'db, '_>,
        args: &dyn Args<'db>,
        on_type_error: OnTypeError,
        result_context: &mut ResultContext,
    ) -> Inferred {
        self.execute_internal(i_s, args, false, on_type_error, result_context)
    }

    pub(crate) fn execute_internal<'db>(
        &self,
        i_s: &InferenceState<'db, '_>,
        args: &dyn Args<'db>,
        skip_first_argument: bool,
        on_type_error: OnTypeError,
        result_context: &mut ResultContext,
    ) -> Inferred {
        let return_type = &self.content.return_type;
        if result_context.expect_not_none(i_s) && matches!(&return_type, Type::None) {
            args.add_issue(
                i_s,
                IssueType::DoesNotReturnAValue(
                    self.diagnostic_string(i_s.db)
                        .unwrap_or_else(|| "Function".into())
                        .into(),
                ),
            );
            return Inferred::new_any_from_error();
        }
        let calculated_type_vars = calculate_callable_type_vars_and_return(
            i_s,
            *self,
            args.iter(),
            |issue| args.add_issue(i_s, issue),
            skip_first_argument,
            result_context,
            Some(on_type_error),
        );
        calculated_type_vars.as_return_type(i_s, &return_type, self.defined_in.as_ref(), &|| {
            self.defined_in
                .map(|c| c.as_type(i_s.db))
                .unwrap_or(Type::Self_)
        })
    }
}
