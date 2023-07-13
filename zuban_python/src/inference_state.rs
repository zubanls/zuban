use std::cell::Cell;

use crate::arguments::Arguments;
use crate::database::{CallableContent, Database};
use crate::type_helpers::{Class, Function};

#[derive(Debug, Copy, Clone)]
enum Context<'db, 'a> {
    None,
    DiagnosticClass(&'a Class<'a>),
    Class(&'a Class<'a>),
    DiagnosticExecution(&'a Function<'a, 'a>, &'a dyn Arguments<'db>),
    Execution(&'a Function<'a, 'a>, &'a dyn Arguments<'db>),
    LambdaCallable(&'a CallableContent),
}

#[derive(Clone, Copy, Debug)]
enum Mode<'a> {
    Normal,
    OverloadCheck { had_error: &'a Cell<bool> },
}

#[derive(Clone, Copy, Debug)]
pub struct InferenceState<'db, 'a> {
    pub db: &'db Database,
    context: Context<'db, 'a>,
    mode: Mode<'a>,
}

impl<'db, 'a> InferenceState<'db, 'a> {
    pub fn new(db: &'db Database) -> Self {
        Self {
            db,
            context: Context::None,
            mode: Mode::Normal,
        }
    }

    pub fn with_func_and_args(
        &self,
        func: &'a Function<'a, 'a>,
        args: &'a dyn Arguments<'db>,
    ) -> Self {
        Self {
            db: self.db,
            context: Context::Execution(func, args),
            mode: self.mode,
        }
    }

    pub fn with_diagnostic_func_and_args(
        &self,
        func: &'a Function<'a, 'a>,
        args: &'a dyn Arguments<'db>,
    ) -> Self {
        Self {
            db: self.db,
            context: Context::DiagnosticExecution(func, args),
            mode: self.mode,
        }
    }

    pub fn with_simplified_annotation_instance(&self) -> Self {
        Self {
            db: self.db,
            context: Context::None,
            mode: self.mode,
        }
    }

    pub fn with_class_context(&self, current_class: &'a Class<'a>) -> Self {
        Self {
            db: self.db,
            context: Context::Class(current_class),
            mode: self.mode,
        }
    }

    pub fn with_diagnostic_class_context(&self, current_class: &'a Class<'a>) -> Self {
        Self {
            db: self.db,
            context: Context::DiagnosticClass(current_class),
            mode: self.mode,
        }
    }

    pub fn with_lambda_callable(&self, callable: &'a CallableContent) -> Self {
        Self {
            db: self.db,
            context: Context::LambdaCallable(callable),
            mode: self.mode,
        }
    }

    pub fn use_mode_of(&self, other: &Self) -> Self {
        let mut new = *self;
        new.mode = other.mode;
        new
    }

    pub fn do_overload_check<T>(
        &self,
        mut callable: impl FnMut(&InferenceState<'db, '_>) -> T,
    ) -> (T, bool) {
        let had_error = &Cell::new(false);
        let i_s = &InferenceState {
            db: self.db,
            context: self.context,
            mode: Mode::OverloadCheck { had_error },
        };
        let result = callable(i_s);
        (result, had_error.get())
    }

    pub fn is_checking_overload(&self) -> bool {
        matches!(self.mode, Mode::OverloadCheck { .. })
    }

    pub fn current_function(&self) -> Option<&'a Function<'a, 'a>> {
        match &self.context {
            Context::DiagnosticExecution(func, _) | Context::Execution(func, _) => Some(func),
            _ => None,
        }
    }

    pub fn current_execution(&self) -> Option<(&'a Function<'a, 'a>, &'a dyn Arguments<'db>)> {
        match &self.context {
            Context::DiagnosticExecution(f, a) | Context::Execution(f, a) => Some((f, *a)),
            _ => None,
        }
    }

    pub fn current_class(&self) -> Option<&'a Class<'a>> {
        match &self.context {
            Context::DiagnosticClass(c) | Context::Class(c) => Some(c),
            Context::DiagnosticExecution(func, _) | Context::Execution(func, _) => {
                func.class.as_ref()
            }
            _ => None,
        }
    }

    pub fn current_lambda_callable(&self) -> Option<&'a CallableContent> {
        match &self.context {
            Context::LambdaCallable(c) => Some(c),
            _ => None,
        }
    }

    pub fn is_diagnostic(&self) -> bool {
        matches!(
            self.context,
            Context::DiagnosticClass(_) | Context::DiagnosticExecution(..)
        )
    }

    pub fn should_add_issue(&self) -> bool {
        match self.mode {
            Mode::OverloadCheck { had_error } => {
                had_error.set(true);
                false
            }
            Mode::Normal => true,
        }
    }
}
