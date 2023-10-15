use super::{FirstParamProperties, Function, OverloadedFunction};
use crate::arguments::Arguments;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::matching::{OnTypeError, ResultContext};
use crate::type_::Type;

#[derive(Debug)]
pub enum BoundMethodFunction<'a> {
    Function(Function<'a, 'a>),
    Overload(OverloadedFunction<'a>),
}

#[derive(Debug)]
pub struct BoundMethod<'a, 'b> {
    instance: &'b Type,
    function: BoundMethodFunction<'a>,
}

impl<'a, 'b> BoundMethod<'a, 'b> {
    pub fn new(instance: &'b Type, function: BoundMethodFunction<'a>) -> Self {
        Self { instance, function }
    }

    pub fn execute<'db>(
        &self,
        i_s: &InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError<'db, '_>,
    ) -> Inferred {
        match &self.function {
            BoundMethodFunction::Function(f) => f.execute_internal(
                i_s,
                args,
                true,
                on_type_error,
                &|| self.instance.clone(),
                result_context,
            ),
            BoundMethodFunction::Overload(f) => {
                f.execute_internal(i_s, args, true, result_context, on_type_error)
            }
        }
    }

    pub fn as_type<'db: 'a>(&self, i_s: &InferenceState<'db, '_>) -> Type {
        // TODO performance: it may be questionable that we allocate here again.
        match &self.function {
            BoundMethodFunction::Function(f) => f.as_db_type(
                i_s,
                FirstParamProperties::Skip {
                    to_self_instance: &|| self.instance.clone(),
                },
            ),
            BoundMethodFunction::Overload(f) => f.as_type(i_s, Some(&|| self.instance.clone())),
        }
    }
}
