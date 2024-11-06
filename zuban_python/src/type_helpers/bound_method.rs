use super::{FirstParamProperties, Function, OverloadedFunction};
use crate::{
    arguments::Args,
    inference_state::InferenceState,
    inferred::Inferred,
    matching::{OnTypeError, ResultContext},
    type_::Type,
};

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

    pub(crate) fn execute<'db>(
        &self,
        i_s: &InferenceState<'db, '_>,
        args: &dyn Args<'db>,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError,
    ) -> Inferred {
        match &self.function {
            BoundMethodFunction::Function(f) => f.execute_internal(
                i_s,
                args,
                true,
                on_type_error,
                &|| Some(self.instance.clone()),
                result_context,
            ),
            BoundMethodFunction::Overload(f) => {
                f.execute_internal(i_s, args, true, result_context, on_type_error, &|| {
                    Some(self.instance.clone())
                })
            }
        }
    }

    pub fn as_type<'db: 'a>(&self, i_s: &InferenceState<'db, '_>) -> Type {
        match &self.function {
            BoundMethodFunction::Function(f) => f.as_type(
                i_s,
                FirstParamProperties::Skip {
                    to_self_instance: &|| self.instance.clone(),
                },
            ),
            BoundMethodFunction::Overload(f) => f.as_type(i_s, Some(&|| self.instance.clone())),
        }
    }
}
