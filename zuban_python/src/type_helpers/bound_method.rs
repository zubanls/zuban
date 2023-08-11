use std::rc::Rc;

use super::{Callable, FirstParamProperties, Function, Instance, OverloadedFunction};
use crate::arguments::{Arguments, CombinedArguments, KnownArguments};
use crate::database::DbType;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::matching::{replace_class_type_vars_in_callable, OnTypeError, ResultContext, Type};

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
}

impl<'a, 'b> BoundMethod<'a, 'b> {
    pub fn new(instance: &'b Instance<'a>, function: BoundMethodFunction<'a>) -> Self {
        Self { instance, function }
    }

    pub fn execute<'db>(
        &self,
        i_s: &InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError<'db, '_>,
    ) -> Inferred {
        let instance_inf = self.instance.as_inferred(i_s);
        let instance_arg = KnownArguments::new_bound(&instance_inf, args.as_node_ref());
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
            BoundMethodFunction::Callable(f) => f.execute(
                &i_s.with_class_context(class),
                &args,
                on_type_error,
                result_context,
            ),
        }
    }

    pub fn as_type<'db: 'a>(&self, i_s: &InferenceState<'db, '_>) -> Type<'a> {
        let t = match &self.function {
            BoundMethodFunction::Function(f) => f.as_db_type(
                i_s,
                FirstParamProperties::Skip {
                    to_self_instance: &|| self.instance.class.as_db_type(i_s.db),
                },
            ),
            BoundMethodFunction::Overload(f) => {
                f.as_db_type(i_s, Some(&mut || self.instance.class.as_db_type(i_s.db)))
            }
            BoundMethodFunction::Callable(c) => {
                let callable = c
                    .content
                    .remove_first_param()
                    .expect("Bound methods should always contain first params");
                DbType::Callable(Rc::new({
                    replace_class_type_vars_in_callable(
                        i_s.db,
                        &callable,
                        c.defined_in.as_ref(),
                        &mut || self.instance.class.as_db_type(i_s.db),
                    )
                }))
            }
        };
        // TODO performance: it may be questionable that we allocate here again.
        Type::owned(t)
    }
}
