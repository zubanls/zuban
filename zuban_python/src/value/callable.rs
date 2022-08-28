use super::{LookupResult, OnTypeError, Value, ValueKind};
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

impl<'db, 'a> Callable<'a> {
    pub fn new(db_type: &'a DbType, content: &'a CallableContent) -> Self {
        Self { db_type, content }
    }
}

impl<'db, 'a> Value<'db, 'a> for Callable<'a> {
    fn kind(&self) -> ValueKind {
        ValueKind::Object
    }

    fn name(&self) -> &'db str {
        "Callable"
    }

    fn lookup_internal(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> LookupResult<'db> {
        debug!("TODO callable lookups");
        LookupResult::None
    }

    fn as_type(&self, i_s: &mut InferenceState<'db, '_>) -> Type<'db, 'a> {
        Type::new(self.db_type)
    }

    fn execute(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        result_context: ResultContext<'db, '_>,
        on_type_error: OnTypeError<'db, '_>,
    ) -> Inferred<'db> {
        let calculated_type_vars = calculate_callable_type_vars_and_return(
            i_s,
            self.content,
            args,
            result_context,
            on_type_error,
        );
        let g_o = Type::new(&self.content.result_type);
        g_o.execute_and_resolve_type_vars(i_s, None, &calculated_type_vars)
    }

    fn description(&self, i_s: &mut InferenceState) -> String {
        base_description!(self) + &self.content.format(&FormatData::new_short(i_s.db))
    }
}
