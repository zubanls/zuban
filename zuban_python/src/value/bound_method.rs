use super::{
    Callable, Function, Instance, LookupResult, OnTypeError, OverloadedFunction, Value, ValueKind,
};
use crate::arguments::{Arguments, CombinedArguments, KnownArguments};
use crate::database::MroIndex;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::matching::{ResultContext, Type};

#[derive(Debug)]
pub enum BoundMethodFunction<'db, 'a> {
    Function(Function<'db, 'a>),
    Overload(OverloadedFunction<'db, 'a>),
    Callable(Callable<'a>),
}

impl<'db, 'a> BoundMethodFunction<'db, 'a> {
    fn as_value(&self) -> &dyn Value<'db, 'a> {
        match self {
            Self::Function(f) => f,
            Self::Overload(f) => f,
            Self::Callable(c) => c,
        }
    }
}

#[derive(Debug)]
pub struct BoundMethod<'db, 'a, 'b> {
    instance: &'b Instance<'db, 'b>,
    function: BoundMethodFunction<'db, 'a>,
    mro_index: MroIndex,
}

impl<'db, 'a, 'b> BoundMethod<'db, 'a, 'b> {
    pub fn new(
        instance: &'b Instance<'db, 'b>,
        mro_index: MroIndex,
        function: BoundMethodFunction<'db, 'a>,
    ) -> Self {
        Self {
            instance,
            mro_index,
            function,
        }
    }
}

impl<'db> Value<'db, '_> for BoundMethod<'db, '_, '_> {
    fn kind(&self) -> ValueKind {
        self.function.as_value().kind()
    }

    fn name(&self) -> &'db str {
        self.function.as_value().name()
    }

    fn lookup_internal(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> LookupResult {
        self.function.as_value().lookup_internal(i_s, name)
    }

    fn execute(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        result_context: ResultContext<'db, '_>,
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

    fn as_type(&self, i_s: &mut InferenceState<'db, '_>) -> Type<'db, 'static> {
        Type::owned(match &self.function {
            BoundMethodFunction::Function(f) => f.as_db_type(i_s, true),
            BoundMethodFunction::Overload(f) => todo!(),
            BoundMethodFunction::Callable(c) => todo!(),
        })
    }
}
