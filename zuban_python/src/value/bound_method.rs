use super::{Function, Value, ValueKind};
use crate::arguments::{Arguments, InstanceArguments};
use crate::database::AnyLink;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;

#[derive(Debug)]
pub struct BoundMethod<'db, 'a> {
    instance: &'a AnyLink,
    function: &'a Function<'db>,
}

impl<'db, 'a> BoundMethod<'db, 'a> {
    pub fn new(instance: &'a AnyLink, function: &'a Function<'db>) -> Self {
        Self { instance, function }
    }
}

impl<'db> Value<'db> for BoundMethod<'db, '_> {
    fn get_kind(&self) -> ValueKind {
        self.function.get_kind()
    }

    fn get_name(&self) -> &'db str {
        self.function.get_name()
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
        inferred.run_on_value(i_s, &mut |i_s, value| {
            let instance = value.as_instance().unwrap();
            let args = InstanceArguments::new(instance, args);
            self.function.execute(i_s, &args)
        })
    }
}
