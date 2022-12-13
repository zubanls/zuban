use std::borrow::Cow;

use super::{
    Callable, Function, Instance, LookupResult, OnTypeError, OverloadedFunction, Value, ValueKind,
};
use crate::arguments::{Arguments, CombinedArguments, KnownArguments};
use crate::database::{CallableContent, CallableParams, MroIndex};
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::matching::{ResultContext, Type};

#[derive(Debug)]
pub enum BoundMethodFunction<'a> {
    Function(Function<'a>),
    Overload(OverloadedFunction<'a>),
    Callable(Callable<'a>),
}

impl<'db: 'a, 'a> BoundMethodFunction<'a> {
    fn as_value(&self) -> &dyn Value<'db, 'a> {
        match self {
            Self::Function(f) => f,
            Self::Overload(f) => f,
            Self::Callable(c) => c,
        }
    }
}

#[derive(Debug)]
pub struct BoundMethod<'a, 'b> {
    instance: &'b Instance<'a>,
    function: BoundMethodFunction<'a>,
    mro_index: MroIndex,
}

impl<'a, 'b> BoundMethod<'a, 'b> {
    pub fn new(
        instance: &'b Instance<'a>,
        mro_index: MroIndex,
        function: BoundMethodFunction<'a>,
    ) -> Self {
        Self {
            instance,
            mro_index,
            function,
        }
    }
}

impl<'db: 'a, 'a> Value<'db, 'a> for BoundMethod<'a, '_> {
    fn kind(&self) -> ValueKind {
        self.function.as_value().kind()
    }

    fn name(&self) -> &str {
        self.function.as_value().name()
    }

    fn lookup_internal(&self, i_s: &mut InferenceState, name: &str) -> LookupResult {
        self.function.as_value().lookup_internal(i_s, name)
    }

    fn execute(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError<'db, '_>,
    ) -> Inferred {
        let instance_inf = self.instance.as_inferred(i_s);
        let instance_arg = KnownArguments::with_mro_index(&instance_inf, self.mro_index, None);
        let args = CombinedArguments::new(&instance_arg, args);
        let class = &self.instance.class;
        match &self.function {
            BoundMethodFunction::Function(f) => f.execute_internal(
                &mut i_s.with_class_context(class),
                &args,
                on_type_error,
                Some(class),
                result_context,
            ),
            BoundMethodFunction::Overload(f) => f.execute_internal(
                &mut i_s.with_class_context(class),
                &args,
                on_type_error,
                Some(class),
                result_context,
            ),
            BoundMethodFunction::Callable(f) => f.execute_internal(
                &mut i_s.with_class_context(class),
                &args,
                on_type_error,
                Some(class),
                result_context,
            ),
        }
    }

    fn maybe_callable_content(
        &self,
        i_s: &mut InferenceState<'db, '_>,
    ) -> Option<Cow<'a, CallableContent>> {
        let mut callable_content = match &self.function {
            BoundMethodFunction::Function(f) => f.maybe_callable_content(i_s).unwrap().into_owned(),
            BoundMethodFunction::Overload(f) => return None,
            BoundMethodFunction::Callable(c) => c.content.clone(),
        };
        match &mut callable_content.params {
            CallableParams::Simple(params) => {
                todo!()
            }
            CallableParams::WithParamSpec(pre_types, spec) => {
                todo!()
            }
            CallableParams::Any => (),
        }
        Some(Cow::Owned(callable_content))
    }

    fn as_type(&self, i_s: &mut InferenceState<'db, '_>) -> Type<'a> {
        Type::owned(match &self.function {
            BoundMethodFunction::Function(f) => f.as_db_type(i_s, true),
            BoundMethodFunction::Overload(f) => f.as_type(i_s).into_db_type(i_s),
            BoundMethodFunction::Callable(c) => return c.as_type(i_s),
        })
    }
}
