use super::{Function, Value, ValueKind};
use crate::arguments::{Arguments, InstanceArguments, SimpleArguments};
use crate::database::BoundInstanceLink;
use crate::inference_state::InferenceState;
use crate::inferred::{use_instance, Inferred};

#[derive(Debug)]
pub struct BoundMethod<'db, 'a> {
    instance: &'a BoundInstanceLink,
    function: &'a Function<'db>,
}

impl<'db, 'a> BoundMethod<'db, 'a> {
    pub fn new(instance: &'a BoundInstanceLink, function: &'a Function<'db>) -> Self {
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
        let file = i_s.database.get_loaded_python_file(self.instance.node.file);
        let instance = use_instance(file, self.instance.node.node_index);
        let instance_link = instance.as_bound_instance_link(i_s);
        let args = InstanceArguments::new(instance_link.clone(), args);
        if let Some(execution) = &self.instance.execution {
            let init = Function::from_execution(i_s.database, &execution);
            let instance_args = SimpleArguments::from_execution(i_s.database, &execution);
            let instance_args = InstanceArguments::new(instance_link, &instance_args);
            self.function
                .execute(&mut i_s.with_func_and_args(&init, &instance_args), &args)
        } else {
            self.function
                .execute(&mut i_s.with_annotation_instance(), &args)
        }
    }
}
