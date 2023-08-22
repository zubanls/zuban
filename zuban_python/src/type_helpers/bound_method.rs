use super::{FirstParamProperties, Function, OverloadedFunction};
use crate::arguments::{Arguments, CombinedArguments, KnownArguments};
use crate::database::DbType;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::matching::{OnTypeError, ResultContext, Type};

#[derive(Debug)]
pub enum BoundMethodFunction<'a> {
    Function(Function<'a, 'a>),
    Overload(OverloadedFunction<'a>),
}

#[derive(Debug)]
pub struct BoundMethod<'a, 'b> {
    instance: &'b DbType,
    function: BoundMethodFunction<'a>,
}

impl<'a, 'b> BoundMethod<'a, 'b> {
    pub fn new(instance: &'b DbType, function: BoundMethodFunction<'a>) -> Self {
        Self { instance, function }
    }

    pub fn execute<'db>(
        &self,
        i_s: &InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError<'db, '_>,
    ) -> Inferred {
        let instance_inf = Inferred::from_type(self.instance.clone());
        let instance_arg = KnownArguments::new_bound(&instance_inf, args.as_node_ref());
        let args = CombinedArguments::new(&instance_arg, args);
        match &self.function {
            BoundMethodFunction::Function(f) => f.execute_internal(
                i_s,
                &args,
                on_type_error,
                &|| self.instance.clone(),
                result_context,
            ),
            BoundMethodFunction::Overload(f) => {
                f.execute(i_s, &args, result_context, on_type_error)
            }
        }
    }

    pub fn as_type<'db: 'a>(&self, i_s: &InferenceState<'db, '_>) -> Type<'a> {
        let t = match &self.function {
            BoundMethodFunction::Function(f) => f.as_db_type(
                i_s,
                FirstParamProperties::Skip {
                    to_self_instance: &|| self.instance.clone(),
                },
            ),
            BoundMethodFunction::Overload(f) => f.as_db_type(i_s, Some(&|| self.instance.clone())),
        };
        // TODO performance: it may be questionable that we allocate here again.
        Type::owned(t)
    }
}
