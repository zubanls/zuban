use std::cell::Cell;

use vfs::FileIndex;

use crate::{
    database::{Database, ParentScope, PointLink},
    file::{ClassNodeRef, PythonFile, TypeVarCallbackReturn},
    node_ref::NodeRef,
    type_::{CallableContent, TypeVarLike},
    type_helpers::{Class, Function},
    TypeCheckerFlags,
};

#[derive(Debug, Copy, Clone)]
enum Context<'a> {
    None,
    File(&'a PythonFile),
    Class(&'a Class<'a>),
    Function(&'a Function<'a, 'a>),
    LambdaCallable {
        callable: &'a CallableContent,
        parent_context: &'a Context<'a>,
    },
}

impl<'a> Context<'a> {
    fn current_class(&self, db: &'a Database) -> Option<Class<'a>> {
        match self {
            Context::Class(c) => Some(**c),
            Context::Function(func) => func.parent_class(db),
            Context::LambdaCallable { parent_context, .. } => parent_context.current_class(db),
            Context::File(_) | Context::None => None,
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum Mode<'a> {
    Normal,
    EnumMemberCalculation,
    AvoidErrors { had_error: &'a Cell<bool> },
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct InferenceState<'db, 'a> {
    pub db: &'db Database,
    context: Context<'a>,
    pub mode: Mode<'a>,
}

impl<'db, 'a> InferenceState<'db, 'a> {
    pub fn new_in_unknown_file(db: &'db Database) -> Self {
        Self {
            db,
            context: Context::None,
            mode: Mode::Normal,
        }
    }

    pub fn new(db: &'db Database, file: &'a PythonFile) -> Self {
        Self {
            db,
            context: Context::File(file),
            mode: Mode::Normal,
        }
    }

    pub fn run_with_parent_scope<T>(
        db: &'db Database,
        file_index: FileIndex,
        parent_scope: ParentScope,
        callback: impl FnOnce(InferenceState) -> T,
    ) -> T {
        let class;
        let func;
        let context = match parent_scope {
            ParentScope::Module => Context::None,
            ParentScope::Function(func_index) => {
                func = Function::new_with_unknown_parent(
                    db,
                    NodeRef::from_link(db, PointLink::new(file_index, func_index)),
                );
                Context::Function(&func)
            }
            ParentScope::Class(class_index) => {
                class = Class::with_self_generics(
                    db,
                    ClassNodeRef::from_link(db, PointLink::new(file_index, class_index)),
                );
                Context::Class(&class)
            }
        };
        callback(InferenceState {
            db,
            context,
            mode: Mode::Normal,
        })
    }

    pub(crate) fn with_func_and_args(&self, func: &'a Function<'a, 'a>) -> Self {
        Self {
            db: self.db,
            context: Context::Function(func),
            mode: self.mode,
        }
    }

    pub(crate) fn with_diagnostic_func_and_args(&self, func: &'a Function<'a, 'a>) -> Self {
        Self {
            db: self.db,
            context: Context::Function(func),
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

    pub fn without_context(&self) -> Self {
        self.with_simplified_annotation_instance()
    }

    pub fn with_class_context(&self, current_class: &'a Class<'a>) -> Self {
        Self {
            db: self.db,
            context: Context::Class(current_class),
            mode: self.mode,
        }
    }

    pub fn with_lambda_callable<'x: 'a>(
        &'x self,
        callable: &'x CallableContent,
    ) -> InferenceState<'db, 'x> {
        Self {
            db: self.db,
            context: Context::LambdaCallable {
                callable,
                parent_context: &self.context,
            },
            mode: self.mode,
        }
    }

    pub fn with_mode<'b: 'a>(&self, mode: Mode<'b>) -> InferenceState<'db, 'a> {
        let mut new = *self;
        new.mode = mode;
        new
    }

    pub fn with_enum_calculation_mode(&self) -> Self {
        let mut new = *self;
        new.mode = Mode::EnumMemberCalculation;
        new
    }

    pub(crate) fn avoid_errors_within<T>(
        &self,
        mut callable: impl FnMut(&InferenceState<'db, '_>) -> T,
    ) -> (T, bool) {
        let had_error = &Cell::new(false);
        let i_s = &InferenceState {
            db: self.db,
            context: self.context,
            mode: Mode::AvoidErrors { had_error },
        };
        let result = callable(i_s);
        (result, had_error.get())
    }

    pub(crate) fn is_calculating_enum_members(&self) -> bool {
        matches!(self.mode, Mode::EnumMemberCalculation)
    }

    pub(crate) fn current_function(&self) -> Option<&'a Function<'a, 'a>> {
        match &self.context {
            Context::Function(func) => Some(func),
            _ => None,
        }
    }

    pub(crate) fn current_class(&self) -> Option<Class<'a>>
    where
        'db: 'a,
    {
        self.context.current_class(self.db)
    }

    pub fn current_lambda_callable(&self) -> Option<&'a CallableContent> {
        match &self.context {
            Context::LambdaCallable { callable, .. } => Some(callable),
            _ => None,
        }
    }

    pub fn in_class_scope(&self) -> Option<&'a Class<'a>> {
        match self.context {
            Context::Class(c) => Some(c),
            _ => None,
        }
    }

    pub fn in_module_context(&self) -> bool {
        matches!(self.context, Context::None)
    }

    pub(crate) fn find_parent_type_var(
        &self,
        searched: &TypeVarLike,
    ) -> Option<TypeVarCallbackReturn> {
        if let Some(func) = self.current_function() {
            if let Some(usage) =
                func.find_type_var_like_including_ancestors(self.db, searched, false)
            {
                return Some(usage);
            }
        }
        if let Some(class) = self.in_class_scope() {
            if let Some(usage) =
                class.find_type_var_like_including_ancestors(self.db, searched, false)
            {
                return Some(usage);
            }
        }
        None
    }

    pub fn as_parent_scope(&self) -> ParentScope {
        if let Some(func) = self.current_function() {
            ParentScope::Function(func.node_ref.node_index)
        } else if let Some(class) = self.current_class() {
            ParentScope::Class(class.node_ref.node_index)
        } else {
            ParentScope::Module
        }
    }

    pub fn should_add_issue(&self) -> bool {
        match self.mode {
            Mode::AvoidErrors { had_error } => {
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
