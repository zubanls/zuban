use super::{
    Callable, Function, Instance, LookupResult, OnTypeError, OverloadedFunction, Value, ValueKind,
};
use crate::arguments::{Arguments, CombinedArguments, KnownArguments};
use crate::database::{CallableContent, DbType, MroIndex};
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::matching::{
    replace_class_type_vars, CalculatedTypeVarLike, Matcher, ResultContext, Type,
};

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

    fn calculate_if_first_annotation(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        instance: &Instance,
    ) -> Option<DbType> {
        match self {
            Self::Function(f) => {
                f.type_vars(i_s).and_then(|type_vars| {
                    f.iter_params()
                        .next()
                        .unwrap()
                        .annotation(i_s)
                        .map(|first| {
                            let mut calculated = vec![];
                            calculated.resize_with(type_vars.len(), Default::default);
                            let mut matcher = Matcher::new_reverse_function_matcher(
                                *f,
                                Some(type_vars),
                                &mut calculated,
                            );
                            let instance_t = instance.as_type(i_s);
                            matcher.match_reverse(|m| first.is_sub_type_of(i_s, m, &instance_t));
                            let mut t = f.as_db_type(i_s, true);
                            let DbType::Callable(callable_content) = &mut t else {
                            unreachable!();
                        };
                            let mut old_type_vars =
                                std::mem::replace(&mut callable_content.type_vars, None)
                                    .unwrap()
                                    .into_vec();
                            for (i, c) in calculated.iter().rev().enumerate() {
                                if c.calculated() {
                                    old_type_vars.remove(i);
                                }
                            }
                            let t = t.replace_type_var_likes_and_self(
                                i_s.db,
                                &mut |usage| {
                                    if usage.in_definition() == f.node_ref.as_link() {
                                        let index = usage.index().as_usize();
                                        let c = &calculated[index];
                                        if c.calculated() {
                                            return (*c)
                                                .clone()
                                                .into_generic_item(i_s.db, &type_vars[index]);
                                        }
                                    }
                                    usage.into_generic_item()
                                },
                                &mut || DbType::Self_,
                            );
                            // TODO this should not be run separately, we do two replacements here.
                            replace_class_type_vars(i_s, &t, &instance.class)
                        })
                })
            }
            Self::Overload(f) => None, // TODO
            Self::Callable(c) => None, // TODO
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
        if let Some(t) = self
            .function
            .calculate_if_first_annotation(i_s, self.instance)
        {
            let DbType::Callable(c) = &t else {
                unreachable!();
            };
            return Callable::new(&t, c).execute(i_s, args, result_context, on_type_error);
        }
        let instance_inf = self.instance.as_inferred(i_s);
        let instance_arg =
            KnownArguments::with_mro_index(&instance_inf, self.mro_index, args.as_node_ref());
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

    fn as_type(&self, i_s: &mut InferenceState<'db, '_>) -> Type<'a> {
        let t = match &self.function {
            BoundMethodFunction::Function(f) => f.as_db_type(i_s, true),
            BoundMethodFunction::Overload(f) => f.as_db_type(i_s, true),
            BoundMethodFunction::Callable(c) => return c.as_type(i_s),
        };
        if let Some(t) = self
            .function
            .calculate_if_first_annotation(i_s, self.instance)
        {
            return Type::owned(t);
        }
        // TODO performance: it may be questionable that we allocate here again.
        Type::owned(replace_class_type_vars(i_s, &t, &self.instance.class))
    }
}
