use super::{Instance, LookupResult, OnTypeError, Value, ValueKind};
use crate::arguments::{Arguments, CombinedArguments, KnownArguments};
use crate::database::MroIndex;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::matching::{ResultContext, Type};

#[derive(Debug)]
pub struct BoundMethod<'db, 'a> {
    instance: &'a Instance<'db, 'a>,
    function: &'a dyn Value<'db, 'a>,
    mro_index: MroIndex,
}

impl<'db, 'a> BoundMethod<'db, 'a> {
    pub fn new(
        instance: &'a Instance<'db, 'a>,
        mro_index: MroIndex,
        function: &'a dyn Value<'db, 'a>,
    ) -> Self {
        Self {
            instance,
            mro_index,
            function,
        }
    }
}

impl<'db, 'a, 'b> Value<'db, 'b> for BoundMethod<'db, 'a> {
    fn kind(&self) -> ValueKind {
        self.function.kind()
    }

    fn name(&self) -> &'db str {
        self.function.name()
    }

    fn lookup_internal(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> LookupResult<'db> {
        self.function.lookup_internal(i_s, name)
    }

    fn execute(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        result_context: ResultContext<'db, '_>,
        on_type_error: OnTypeError<'db, '_>,
    ) -> Inferred<'db> {
        let instance_inf = self.instance.as_inferred(i_s);
        let instance_arg = KnownArguments::with_mro_index(&instance_inf, self.mro_index, None);
        let args = CombinedArguments::new(&instance_arg, args);
        let class = &self.instance.class;
        match self.function.as_function() {
            Some(f) => f.execute_internal(
                &mut i_s.with_class_context(class),
                &args,
                on_type_error,
                Some(class),
                result_context,
            ),
            // TODO this kind of loses access the class
            None => match self.function.as_overloaded_function() {
                Some(f) => f.execute_internal(
                    &mut i_s.with_class_context(class),
                    &args,
                    on_type_error,
                    Some(class),
                    result_context,
                ),
                None => todo!(), //self.function.execute(i_s, &args, on_type_error),
            },
        }
    }

    fn as_type(&self, i_s: &mut InferenceState<'db, '_>) -> Type<'db, 'b> {
        todo!("{self:?}")
    }
}
