use super::{Class, LookupResult, OnTypeError, Value, ValueKind};
use crate::arguments::Arguments;
use crate::base_description;
use crate::database::{CallableContent, DbType};
use crate::debug;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::matching::{calculate_callable_type_vars_and_return, FormatData, ResultContext, Type};

#[derive(Debug, Copy, Clone)]
pub struct Callable<'a> {
    db_type: &'a DbType,
    pub content: &'a CallableContent,
}

impl<'a> Callable<'a> {
    pub fn new(db_type: &'a DbType, content: &'a CallableContent) -> Self {
        Self { db_type, content }
    }

    pub(super) fn execute_internal<'db>(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        on_type_error: OnTypeError<'db, '_>,
        class: Option<&Class>,
        result_context: &mut ResultContext,
    ) -> Inferred {
        let calculated_type_vars = calculate_callable_type_vars_and_return(
            i_s,
            class,
            self.content,
            args,
            result_context,
            on_type_error,
        );
        let g_o = Type::new(&self.content.result_type);
        g_o.execute_and_resolve_type_vars(i_s, None, &calculated_type_vars)
    }
}

impl<'db, 'a> Value<'db, 'a> for Callable<'a> {
    fn kind(&self) -> ValueKind {
        ValueKind::Object
    }

    fn name(&self) -> &str {
        "Callable"
    }

    fn lookup_internal(&self, i_s: &mut InferenceState, name: &str) -> LookupResult {
        debug!("TODO callable lookups");
        LookupResult::None
    }

    fn as_type(&self, i_s: &mut InferenceState<'db, '_>) -> Type<'a> {
        Type::new(self.db_type)
    }

    fn execute(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError<'db, '_>,
    ) -> Inferred {
        self.execute_internal(i_s, args, on_type_error, None, result_context)
    }

    fn description(&self, i_s: &mut InferenceState) -> String {
        base_description!(self) + &self.content.format(&FormatData::new_short(i_s.db))
    }
}
