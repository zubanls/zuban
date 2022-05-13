use super::{Instance, LookupResult, Value, ValueKind};
use crate::arguments::{Arguments, KnownArguments};
use crate::database::MroIndex;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;

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
    ) -> Inferred<'db> {
        let args =
            KnownArguments::with_mro_index(self.instance.as_inferred(), self.mro_index, args);
        self.function.execute(i_s, &args)
    }
}
