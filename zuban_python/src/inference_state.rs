use std::cell::Cell;

use crate::{
    arguments::Args,
    database::{Database, ParentScope},
    file::TypeVarCallbackReturn,
    type_::{CallableContent, TypeVarLike},
    type_helpers::{Class, Function},
    TypeCheckerFlags,
};

#[derive(Debug, Copy, Clone)]
enum Context<'db, 'a> {
    None,
    DiagnosticClass(&'a Class<'a>),
    Class(&'a Class<'a>),
    DiagnosticExecution(&'a Function<'a, 'a>, &'a dyn Args<'db>),
    Execution(&'a Function<'a, 'a>, &'a dyn Args<'db>),
    LambdaCallable(&'a CallableContent),
}

#[derive(Clone, Copy, Debug)]
enum Mode<'a> {
    Normal,
    EnumMemberCalculation,
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

    pub(crate) fn with_func_and_args(
        &self,
        func: &'a Function<'a, 'a>,
        args: &'a dyn Args<'db>,
    ) -> Self {
        Self {
            db: self.db,
            context: Context::Execution(func, args),
            mode: self.mode,
        }
    }

    pub(crate) fn with_diagnostic_func_and_args(
        &self,
        func: &'a Function<'a, 'a>,
        args: &'a dyn Args<'db>,
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

    pub fn with_enum_calculation_mode(&self) -> Self {
        let mut new = *self;
        new.mode = Mode::EnumMemberCalculation;
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

    pub fn is_calculating_enum_members(&self) -> bool {
        matches!(self.mode, Mode::EnumMemberCalculation)
    }

    pub fn current_function(&self) -> Option<&'a Function<'a, 'a>> {
        match &self.context {
            Context::DiagnosticExecution(func, _) | Context::Execution(func, _) => Some(func),
            _ => None,
        }
    }

    pub(crate) fn current_execution(&self) -> Option<(&'a Function<'a, 'a>, &'a dyn Args<'db>)> {
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

    pub fn find_parent_type_var(&self, searched: &TypeVarLike) -> Option<TypeVarCallbackReturn> {
        if let Some(class) = self.current_class() {
            for (index, type_var) in class.type_vars(self).iter().enumerate() {
                if type_var == searched {
                    return Some(TypeVarCallbackReturn::TypeVarLike(
                        type_var.as_type_var_like_usage(index.into(), class.node_ref.as_link()),
                    ));
                }
            }
        }
        if let Some(func) = self.current_function() {
            for (index, type_var) in func.type_vars(self).iter().enumerate() {
                if type_var == searched {
                    return Some(TypeVarCallbackReturn::TypeVarLike(
                        type_var.as_type_var_like_usage(index.into(), func.node_ref.as_link()),
                    ));
                }
            }
        }
        None
    }

    pub fn parent_scope(&self) -> ParentScope {
        if let Some(func) = self.current_function() {
            ParentScope::Function(func.node_ref.node_index)
        } else if let Some(class) = self.current_class() {
            ParentScope::Class(class.node_ref.node_index)
        } else {
            ParentScope::Module
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
            _ => true,
        }
    }

    pub fn flags(&self) -> &TypeCheckerFlags {
        // TODO this is not implemented properly with context, yet.
        &self.db.project.flags
    }
}
