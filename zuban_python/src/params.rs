use parsa_python_ast::{Param as ASTParam, ParamType};

use crate::arguments::{Argument, ArgumentIterator};
use crate::database::CallableParam;
use crate::generics::Type;
use crate::inference_state::InferenceState;
use crate::value::{Function, ParamWithArgument};

pub trait Param<'db>: Copy {
    fn has_default(&self) -> bool;
    fn name(&self) -> &str;
    fn annotation_type(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        function: Option<&Function<'db, '_>>,
    ) -> Option<Type<'db, 'db>>;
    fn param_type(&self) -> ParamType;
}

impl<'db> Param<'db> for ASTParam<'db> {
    fn has_default(&self) -> bool {
        self.default().is_some()
    }

    fn name(&self) -> &str {
        self.name_definition().as_code()
    }

    fn annotation_type(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        function: Option<&Function<'db, '_>>,
    ) -> Option<Type<'db, 'db>> {
        self.annotation().map(|annotation| {
            function
                .unwrap()
                .reference
                .file
                .inference(i_s)
                .use_cached_annotation_type(annotation)
        })
    }

    fn param_type(&self) -> ParamType {
        self.type_()
    }
}

impl<'db> Param<'db> for &'db CallableParam {
    fn has_default(&self) -> bool {
        false
    }

    fn name(&self) -> &str {
        todo!()
    }

    fn annotation_type(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        function: Option<&Function<'db, '_>>,
    ) -> Option<Type<'db, 'db>> {
        Some(Type::from_db_type(i_s.db, &self.db_type))
    }

    fn param_type(&self) -> ParamType {
        self.param_type
    }
}

pub struct InferrableParamIterator2<'db, 'a, I, P> {
    arguments: std::iter::Peekable<ArgumentIterator<'db, 'a>>,
    params: I,
    pub unused_keyword_arguments: Vec<Argument<'db, 'a>>,
    current_starred_param: Option<P>,
    current_double_starred_param: Option<P>,
}

impl<'db, 'a, I, P> InferrableParamIterator2<'db, 'a, I, P> {
    pub fn new(params: I, arguments: std::iter::Peekable<ArgumentIterator<'db, 'a>>) -> Self {
        Self {
            arguments,
            params,
            unused_keyword_arguments: vec![],
            current_starred_param: None,
            current_double_starred_param: None,
        }
    }

    pub fn has_unused_argument(&mut self) -> bool {
        self.arguments.next().is_some()
    }

    pub fn has_unused_keyword_arguments(&mut self) -> bool {
        !self.unused_keyword_arguments.is_empty()
    }
}

impl<'db, 'a, I: Iterator<Item = P>, P: Param<'db>> Iterator
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
                        if *name == param.name() {
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
                                if name == param.name() {
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
                                if name == param.name() {
                                    argument = Some(arg);
                                    break;
                                } else {
                                    self.unused_keyword_arguments.push(arg);
                                }
                            }
                            _ => todo!(),
                        }
                    }
                }
                ParamType::PositionalOnly => todo!(),
                ParamType::Starred => {
                    self.current_starred_param = Some(param);
                    return self.next();
                }
                ParamType::DoubleStarred => todo!(),
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
