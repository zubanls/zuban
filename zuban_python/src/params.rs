use parsa_python_ast::{Param as ASTParam, ParamType};

use crate::arguments::{Argument, ArgumentIterator};
use crate::database::CallableParam;
use crate::generics::Type;
use crate::inference_state::InferenceState;
use crate::value::{Function, ParamWithArgument};

pub trait Param<'x>: Copy {
    fn has_default(&self) -> bool;
    fn name(&self) -> Option<&str>;
    fn annotation_type<'db>(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        function: Option<&Function<'db, '_>>,
    ) -> Option<Type<'db, 'x>>;
    fn param_type(&self) -> ParamType;
}

impl<'x> Param<'x> for ASTParam<'x> {
    fn has_default(&self) -> bool {
        self.default().is_some()
    }

    fn name(&self) -> Option<&str> {
        Some(self.name_definition().as_code())
    }

    fn annotation_type<'db>(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        function: Option<&Function<'db, '_>>,
    ) -> Option<Type<'db, 'x>> {
        self.annotation().map(|annotation| {
            function
                .unwrap()
                .node_ref
                .file
                .inference(i_s)
                .use_cached_annotation_type(annotation)
        })
    }

    fn param_type(&self) -> ParamType {
        self.type_()
    }
}

impl<'x> Param<'x> for &'x CallableParam {
    fn has_default(&self) -> bool {
        false
    }

    fn name(&self) -> Option<&str> {
        None
    }

    fn annotation_type<'db>(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        function: Option<&Function<'db, '_>>,
    ) -> Option<Type<'db, 'x>> {
        Some(Type::from_db_type(i_s.db, &self.db_type))
    }

    fn param_type(&self) -> ParamType {
        self.param_type
    }
}

pub struct InferrableParamIterator2<'db, 'a, I, P> {
    pub arguments: std::iter::Peekable<ArgumentIterator<'db, 'a>>,
    params: I,
    pub unused_keyword_arguments: Vec<Argument<'db, 'a>>,
    current_starred_param: Option<P>,
    current_double_starred_param: Option<P>,
    pub too_many_positional_arguments: bool,
}

impl<'db, 'a, I, P> InferrableParamIterator2<'db, 'a, I, P> {
    pub fn new(params: I, arguments: std::iter::Peekable<ArgumentIterator<'db, 'a>>) -> Self {
        Self {
            arguments,
            params,
            unused_keyword_arguments: vec![],
            current_starred_param: None,
            current_double_starred_param: None,
            too_many_positional_arguments: false,
        }
    }

    pub fn has_unused_keyword_arguments(&mut self) -> bool {
        !self.unused_keyword_arguments.is_empty()
    }
}

impl<'db, 'a, 'x, I: Iterator<Item = P>, P: Param<'x>> Iterator
    for InferrableParamIterator2<'db, 'a, I, P>
{
    type Item = InferrableParam2<'db, 'a, P>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(param) = self.current_starred_param {
            if let Some(argument) = self.arguments.next_if(|arg| !arg.is_keyword_argument()) {
                return Some(InferrableParam2 {
                    param,
                    argument: Some(argument),
                });
            } else {
                self.current_starred_param = None;
            }
        }
        if let Some(param) = self.current_double_starred_param {
            if let Some(argument) = self.arguments.next_if(|arg| arg.is_keyword_argument()) {
                return Some(InferrableParam2 {
                    param,
                    argument: Some(argument),
                });
            } else {
                self.current_double_starred_param = None;
            }
        }
        self.params.next().and_then(|param| {
            for (i, unused) in self.unused_keyword_arguments.iter().enumerate() {
                match unused {
                    Argument::Keyword(name, reference) => {
                        if Some(*name) == param.name() {
                            return Some(InferrableParam2 {
                                param,
                                argument: Some(self.unused_keyword_arguments.remove(i)),
                            });
                        }
                    }
                    _ => unreachable!(),
                }
            }
            let mut argument = None;
            match param.param_type() {
                ParamType::PositionalOrKeyword => {
                    for arg in &mut self.arguments {
                        match arg {
                            Argument::Keyword(name, reference) => {
                                if Some(name) == param.name() {
                                    argument = Some(arg);
                                    break;
                                } else {
                                    self.unused_keyword_arguments.push(arg);
                                }
                            }
                            _ => {
                                argument = Some(arg);
                                break;
                            }
                        }
                    }
                }
                ParamType::KeywordOnly => {
                    for arg in &mut self.arguments {
                        match arg {
                            Argument::Keyword(name, reference) => {
                                if Some(name) == param.name() {
                                    argument = Some(arg);
                                    break;
                                } else {
                                    self.unused_keyword_arguments.push(arg);
                                }
                            }
                            _ => self.too_many_positional_arguments = true,
                        }
                    }
                }
                ParamType::PositionalOnly => {
                    argument = self.arguments.next();
                    if let Some(arg) = argument {
                        match arg {
                            Argument::Positional(_, _) => (),
                            Argument::Keyword(_, _) => {
                                self.unused_keyword_arguments.push(arg);
                                argument = None;
                            }
                            _ => todo!(),
                        }
                    }
                }
                ParamType::Starred => {
                    self.current_starred_param = Some(param);
                    return self.next();
                }
                ParamType::DoubleStarred => {
                    self.current_double_starred_param = Some(param);
                    return self.next();
                }
            }
            Some(InferrableParam2 { param, argument })
        })
    }
}

#[derive(Debug)]
pub struct InferrableParam2<'db, 'a, P> {
    pub param: P,
    pub argument: Option<Argument<'db, 'a>>,
}

impl<'db, 'a, P> ParamWithArgument<'db, 'a> for InferrableParam2<'db, 'a, P> {
    fn argument_index(&self) -> String {
        self.argument.as_ref().unwrap().index()
    }
}
