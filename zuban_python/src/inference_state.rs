use crate::arguments::Arguments;
use crate::database::{Database, Execution};
use crate::inferred::{Inferred, NodeReference};
use crate::value::Function;

pub struct InferenceState<'db, 'a> {
    pub database: &'db Database,
    current_execution: Option<(&'a Function<'db, 'a>, &'a Arguments<'db>)>,
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
        args: &'a Arguments<'db>,
    ) -> Self {
        Self {
            database: self.database,
            current_execution: Some((func, args)),
        }
    }

    pub fn run_with_execution<T>(
        &self,
        execution: &Execution,
        callable: impl FnOnce(&mut InferenceState<'db, '_>) -> T,
    ) -> T {
        let func = Function::from_execution(self.database, execution);
        let args = Arguments::from_execution(self.database, execution);
        callable(&mut InferenceState::with_func_and_args(self, &func, &args))
    }

    pub fn infer_param(&mut self, definition: &NodeReference<'db>) -> Inferred<'db> {
        if let Some((function, args)) = self.current_execution {
            function.infer_param(self, definition.node.index, args)
        } else {
            todo!()
        }
    }

    pub fn args_as_execution(&self) -> Option<Execution> {
        self.current_execution
            .map(|(func, args)| args.as_execution(func))
    }
}
