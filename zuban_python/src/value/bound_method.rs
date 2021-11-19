use super::{Value, ValueKind};
use crate::arguments::{Arguments, InstanceArguments};
use crate::database::AnyLink;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;

#[derive(Debug)]
pub struct BoundMethod<'db, 'a> {
    instance: &'a AnyLink,
    function: &'a dyn Value<'db>,
}

impl<'db, 'a> BoundMethod<'db, 'a> {
    pub fn new(instance: &'a AnyLink, function: &'a dyn Value<'db>) -> Self {
        Self { instance, function }
    }
}

impl<'db> Value<'db> for BoundMethod<'db, '_> {
    fn kind(&self) -> ValueKind {
        self.function.kind()
    }

    fn name(&self) -> &'db str {
        self.function.name()
    }

    fn lookup(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> Inferred<'db> {
        self.function.lookup(i_s, name)
    }

    fn execute(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
    ) -> Inferred<'db> {
        let inferred = Inferred::from_any_link(i_s.database, self.instance);
        // TODO wtf why is this annotation necessary
        let func: &dyn Value<'_> = self.function;
        inferred.run_on_value(i_s, &mut |i_s, value| {
            let instance = value.as_instance().unwrap();
            let args = InstanceArguments::new(instance, args);
            func.execute(i_s, &args)
        })
    }
}
