use crate::arguments::{Arguments, SimpleArguments};
use crate::database::{Database, Execution};
use crate::value::Function;

pub struct InferenceState<'db, 'a> {
    pub database: &'db Database,
    pub current_execution: Option<(&'a Function<'db, 'a>, &'a dyn Arguments<'db>)>,
}

impl<'db, 'a> InferenceState<'db, 'a> {
    pub fn new(database: &'db Database) -> Self {
        Self {
            database,
            current_execution: None,
        }
    }

    pub fn with_func_and_args(
        &self,
        func: &'a Function<'db, 'a>,
        args: &'a dyn Arguments<'db>,
    ) -> Self {
        Self {
            database: self.database,
            current_execution: Some((func, args)),
        }
    }

    pub fn with_annotation_instance(&self) -> Self {
        Self {
            database: self.database,
            current_execution: None,
        }
    }

    pub fn run_with_execution<T>(
        &self,
        execution: &Execution,
        callable: impl FnOnce(&mut InferenceState<'db, '_>) -> T,
    ) -> T {
        // TODO this is unused?!
        let func = Function::from_execution(self.database, execution, None);
        let args = SimpleArguments::from_execution(self.database, execution);
        callable(&mut self.with_func_and_args(&func, &args))
    }

    pub fn args_as_execution(&self) -> Option<Execution> {
        self.current_execution
            .map(|(func, args)| args.as_execution(func))
    }
}
