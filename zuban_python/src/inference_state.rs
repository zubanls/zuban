use crate::arguments::{Arguments, SimpleArguments};
use crate::database::{Database, Execution};
use crate::value::{Class, Function};

pub enum Context {
    Diagnostics,
    Inference,
}

pub struct InferenceState<'db, 'a> {
    pub database: &'db Database,
    pub current_execution: Option<(&'a Function<'db, 'a>, &'a dyn Arguments<'db>)>,
    pub current_class: Option<&'a Class<'db, 'a>>,
    pub context: Context,
}

impl<'db, 'a> InferenceState<'db, 'a> {
    pub fn new(database: &'db Database) -> Self {
        Self {
            database,
            current_execution: None,
            current_class: None,
            context: Context::Inference,
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
            current_class: func.class,
            context: Context::Inference,
        }
    }

    pub fn with_diagnostic_func_and_args(
        &self,
        func: &'a Function<'db, 'a>,
        args: &'a dyn Arguments<'db>,
    ) -> Self {
        Self {
            database: self.database,
            current_execution: Some((func, args)),
            current_class: func.class,
            context: Context::Diagnostics,
        }
    }

    pub fn with_annotation_instance(&self) -> Self {
        Self {
            database: self.database,
            current_execution: None,
            current_class: None,
            context: Context::Inference,
        }
    }

    pub fn with_class_context(&self, current_class: &'a Class<'db, 'a>) -> Self {
        Self {
            database: self.database,
            current_execution: self.current_execution,
            current_class: Some(current_class),
            context: Context::Inference,
        }
    }

    pub fn with_diagnostic_class_context(&self, current_class: &'a Class<'db, 'a>) -> Self {
        Self {
            database: self.database,
            current_execution: self.current_execution,
            current_class: Some(current_class),
            context: Context::Diagnostics,
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
            .and_then(|(func, args)| args.as_execution(func))
    }
}
