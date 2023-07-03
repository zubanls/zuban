use std::rc::Rc;

use super::{Callable, FirstParamProperties, Function, Instance, OverloadedFunction};
use crate::arguments::{Arguments, CombinedArguments, KnownArguments};
use crate::database::{CallableParams, DbType, MroIndex};
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::matching::{OnTypeError, ResultContext, Type};

#[derive(Debug)]
pub enum BoundMethodFunction<'a> {
    Function(Function<'a, 'a>),
    Overload(OverloadedFunction<'a>),
    Callable(Callable<'a>),
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

    pub fn execute<'db>(
        &self,
        i_s: &InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError<'db, '_>,
    ) -> Inferred {
        let instance_inf = self.instance.as_inferred(i_s);
        let instance_arg =
            KnownArguments::new_self(&instance_inf, self.mro_index, args.as_node_ref());
        let args = CombinedArguments::new(&instance_arg, args);
        let class = &self.instance.class;
        match &self.function {
            BoundMethodFunction::Function(f) => f.execute_internal(
                &i_s.with_class_context(class),
                &args,
                on_type_error,
                Some(class),
                result_context,
            ),
            BoundMethodFunction::Overload(f) => f.execute_internal(
                &i_s.with_class_context(class),
                &args,
                on_type_error,
                Some(class),
                result_context,
            ),
            BoundMethodFunction::Callable(f) => f.execute_internal(
                &i_s.with_class_context(class),
                &args,
                on_type_error,
                Some(class),
                result_context,
            ),
        }
    }

    pub fn as_type<'db: 'a>(&self, i_s: &InferenceState<'db, '_>) -> Type<'a> {
        let t = match &self.function {
            BoundMethodFunction::Function(f) => {
                f.as_db_type(i_s, FirstParamProperties::Skip(self.instance))
            }
            BoundMethodFunction::Overload(f) => {
                f.as_db_type(i_s, FirstParamProperties::Skip(self.instance))
            }
            BoundMethodFunction::Callable(c) => {
                DbType::Callable(match &c.content.params {
                    CallableParams::Simple(params) => {
                        let mut vec = params.to_vec();
                        // The first argument in a class param is not relevant if we execute descriptors.
                        vec.remove(0);
                        let mut c = c.content.clone();
                        c.params = CallableParams::Simple(Rc::from(vec));
                        Rc::new(c)
                    }
                    CallableParams::WithParamSpec(_, _) => todo!(),
                    // TODO probably we have to fix generics from classes here.
                    CallableParams::Any => return Type::new(c.db_type),
                })
            }
        };
        // TODO performance: it may be questionable that we allocate here again.
        Type::owned(t)
    }
}
