use std::borrow::Cow;

use crate::arguments::{Arguments, SimpleArguments};
use crate::database::{
    CallableParam, CallableParams, Database, Execution, ParamSpecUsage, TypeVarLikeUsage,
};
use crate::matching::Generic;
use crate::value::{Class, Function};

#[derive(Debug, Copy, Clone)]
pub enum Context<'db, 'a> {
    None,
    DiagnosticClass(&'a Class<'a>),
    Class(&'a Class<'a>),
    DiagnosticExecution(&'a Function<'a>, &'a dyn Arguments<'db>),
    Execution(&'a Function<'a>, &'a dyn Arguments<'db>),
}

#[derive(Clone, Debug)]
pub struct InferenceState<'db, 'a> {
    pub db: &'db Database,
    pub context: Context<'db, 'a>,
}

impl<'db, 'a> InferenceState<'db, 'a> {
    pub fn new(db: &'db Database) -> Self {
        Self {
            db,
            context: Context::None,
        }
    }

    pub fn with_context(&self, context: Context<'db, 'a>) -> Self {
        Self {
            db: self.db,
            context,
        }
    }

    pub fn with_func_and_args(&self, func: &'a Function<'a>, args: &'a dyn Arguments<'db>) -> Self {
        Self {
            db: self.db,
            context: Context::Execution(func, args),
        }
    }

    pub fn with_diagnostic_func_and_args(
        &self,
        func: &'a Function<'a>,
        args: &'a dyn Arguments<'db>,
    ) -> Self {
        Self {
            db: self.db,
            context: Context::DiagnosticExecution(func, args),
        }
    }

    pub fn with_annotation_instance(&self) -> Self {
        Self {
            db: self.db,
            context: Context::None,
        }
    }

    pub fn with_class_context(&self, current_class: &'a Class<'a>) -> Self {
        Self {
            db: self.db,
            context: Context::Class(current_class),
        }
    }

    pub fn with_diagnostic_class_context(&self, current_class: &'a Class<'a>) -> Self {
        Self {
            db: self.db,
            context: Context::DiagnosticClass(current_class),
        }
    }

    pub fn current_function(&self) -> Option<&'a Function<'a>> {
        match &self.context {
            Context::DiagnosticExecution(func, _) | Context::Execution(func, _) => Some(func),
            _ => None,
        }
    }

    pub fn current_execution(&self) -> Option<(&'a Function<'a>, &'a dyn Arguments<'db>)> {
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

    pub fn is_diagnostic(&self) -> bool {
        matches!(
            self.context,
            Context::DiagnosticClass(_) | Context::DiagnosticExecution(..)
        )
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
        self.current_execution()
            .and_then(|(func, args)| args.as_execution(func))
    }

    pub fn remap_param_spec(
        &mut self,
        mut pre_params: Vec<CallableParam>,
        usage: &ParamSpecUsage,
    ) -> CallableParams {
        let into_types = |v| todo!();
        match self.context {
            Context::Class(c) => match c
                .generics()
                .nth_usage(self, &TypeVarLikeUsage::ParamSpec(Cow::Borrowed(usage)))
            {
                Generic::CallableParams(p) => match p.into_owned() {
                    CallableParams::Any => CallableParams::Any,
                    CallableParams::Simple(params) => {
                        pre_params.extend(params.into_vec());
                        CallableParams::Simple(pre_params.into_boxed_slice())
                    }
                    CallableParams::WithParamSpec(pre, p) => {
                        let types = pre.into_vec();
                        CallableParams::WithParamSpec(into_types(types), p)
                    }
                },
                _ => unreachable!(),
            },
            _ => {
                let types = vec![];
                CallableParams::WithParamSpec(into_types(types), usage.clone())
            }
        }
    }
}
