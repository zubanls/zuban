use super::{Value, ValueKind};
use crate::arguments::{Arguments, InstanceArguments};
use crate::database::AnyLink;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;

#[derive(Debug)]
pub struct BoundMethod<'db, 'a> {
    instance: &'a AnyLink,
    function: &'a dyn Value<'db, 'a>,
}

impl<'db, 'a> BoundMethod<'db, 'a> {
    pub fn new(instance: &'a AnyLink, function: &'a dyn Value<'db, 'a>) -> Self {
        Self { instance, function }
    }
}

impl<'db, 'a, 'b> Value<'db, 'b> for BoundMethod<'db, 'a> {
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
        // TODO executing func.execute outside of the closure works, weird...
        // https://github.com/rust-lang/rust/issues/91942
        inferred.run_on_value(i_s, &mut |i_s, value| {
            let value: &dyn Value = unsafe { std::mem::transmute(value) };
            let instance = value.as_instance().unwrap();
            let args = InstanceArguments::new(instance, args);
            let func: &dyn Value = unsafe { std::mem::transmute(self.function) };
            func.execute(i_s, &args)
        })
    }
}
