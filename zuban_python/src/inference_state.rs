use crate::arguments::{Arguments, SimpleArguments};
use crate::database::{Database, Execution};
use crate::value::{Class, Function};

#[derive(Debug)]
pub enum Context<'db, 'a> {
    None,
    DiagnosticClass(&'a Class<'db, 'a>),
    Class(&'a Class<'db, 'a>),
}

pub struct InferenceState<'db, 'a> {
    pub db: &'db Database,
    pub current_execution: Option<(&'a Function<'db, 'a>, &'a dyn Arguments<'db>)>,
    pub context: Context<'db, 'a>,
}

impl<'db, 'a> InferenceState<'db, 'a> {
    pub fn new(db: &'db Database) -> Self {
        Self {
            db,
            current_execution: None,
            context: Context::None,
        }
    }

    pub fn with_func_and_args(
        &self,
        func: &'a Function<'db, 'a>,
        args: &'a dyn Arguments<'db>,
    ) -> Self {
        Self {
            db: self.db,
            current_execution: Some((func, args)),
            context: func
                .class
                .as_ref()
                .map(Context::Class)
                .unwrap_or(Context::None),
        }
    }

    pub fn with_diagnostic_func_and_args(
        &self,
        func: &'a Function<'db, 'a>,
        args: &'a dyn Arguments<'db>,
    ) -> Self {
        Self {
            db: self.db,
            current_execution: Some((func, args)),
            context: func
                .class
                .as_ref()
                .map(Context::DiagnosticClass)
                .unwrap_or(Context::None),
        }
    }

    pub fn with_annotation_instance(&self) -> Self {
        Self {
            db: self.db,
            current_execution: None,
            context: Context::None,
        }
    }

    pub fn with_class_context(&self, current_class: &'a Class<'db, 'a>) -> Self {
        Self {
            db: self.db,
            current_execution: self.current_execution,
            context: Context::Class(current_class),
        }
    }

    pub fn with_diagnostic_class_context(&self, current_class: &'a Class<'db, 'a>) -> Self {
        Self {
            db: self.db,
            current_execution: self.current_execution,
            context: Context::DiagnosticClass(current_class),
        }
    }

    pub fn current_class(&self) -> Option<&'a Class<'db, 'a>> {
        match &self.context {
            Context::DiagnosticClass(c) | Context::Class(c) => Some(c),
            _ => None,
        }
    }

    pub fn is_diagnostic(&self) -> bool {
        matches!(self.context, Context::DiagnosticClass(_))
    }

    pub fn run_with_execution<T>(
        &self,
        execution: &Execution,
        callable: impl FnOnce(&mut InferenceState<'db, '_>) -> T,
    ) -> T {
        // TODO this is unused?!
        let func = Function::from_execution(self.db, execution, None);
        let args = SimpleArguments::from_execution(self.db, execution);
        callable(&mut self.with_func_and_args(&func, &args))
    }

    pub fn args_as_execution(&self) -> Option<Execution> {
        self.current_execution
            .and_then(|(func, args)| args.as_execution(func))
    }
}
