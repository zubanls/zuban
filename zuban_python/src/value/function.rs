use parsa_python_ast::{FunctionDef, NodeIndex, Param, ParamIterator, ReturnOrYield};
use std::fmt;

use super::{Value, ValueKind};
use crate::arguments::{Argument, ArgumentIterator, Arguments, SimpleArguments};
use crate::database::{Database, Execution, PointLink};
use crate::debug;
use crate::file::PythonFile;
use crate::file_state::File;
use crate::generics::{resolve_type_vars, FunctionTypeVarFinder};
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;

pub struct Function<'db> {
    file: &'db PythonFile,
    node_index: NodeIndex,
}

impl<'db> fmt::Debug for Function<'db> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("Inferred")
            .field("file", self.file)
            .field("node", &self.get_node())
            .finish()
    }
}

impl<'db> Function<'db> {
    pub fn new(file: &'db PythonFile, node_index: NodeIndex) -> Self {
        Self { file, node_index }
    }

    pub fn from_execution(database: &'db Database, execution: &Execution) -> Self {
        let f_func = database.get_loaded_python_file(execution.function.file);
        Function::new(f_func, execution.function.node_index)
    }

    fn get_node(&self) -> FunctionDef<'db> {
        FunctionDef::by_index(&self.file.tree, self.node_index)
    }

    pub fn iter_inferrable_params<'a>(
        &self,
        args: &'a dyn Arguments<'db>,
    ) -> InferrableParamIterator<'db, 'a> {
        InferrableParamIterator::new(self.get_node().params().iter(), args.iter_arguments())
    }

    pub fn infer_param(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        param_name_index: NodeIndex,
        args: &dyn Arguments<'db>,
    ) -> Inferred<'db> {
        let func_node = FunctionDef::from_param_name_index(&self.file.tree, param_name_index);
        let temporary_args;
        let temporary_func;
        let (check_args, func) = if func_node.index() == self.node_index {
            (args, self)
        } else {
            let mut execution = args.get_outer_execution();
            loop {
                let exec = execution.unwrap();
                if func_node.index() == exec.function.node_index {
                    // TODO this could be an instance as well
                    temporary_args = SimpleArguments::from_execution(i_s.database, exec);
                    temporary_func = Function::from_execution(i_s.database, exec);
                    break (&temporary_args as &dyn Arguments, &temporary_func);
                }
                execution = exec.in_.as_deref();
            }
        };
        for param in func.iter_inferrable_params(check_args) {
            if param.is_at(param_name_index) {
                return param.infer(i_s);
            }
        }
        unreachable!("{:?}", param_name_index);
    }

    fn execute_without_annotation(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
    ) -> Inferred<'db> {
        if self.is_generator() {
            todo!("Maybe not check here, because this could be precalculated and cached");
        }
        let mut inner_i_s = i_s.with_func_and_args(self, args);
        for return_or_yield in self.iter_return_or_yield() {
            match return_or_yield {
                ReturnOrYield::Return(ret) =>
                // TODO multiple returns, this is an early exit
                {
                    return self
                        .file
                        .get_inference(&mut inner_i_s)
                        .infer_star_expressions(ret.star_expressions())
                        .resolve_function_return(&mut inner_i_s)
                }
                ReturnOrYield::Yield(yield_expr) => unreachable!(),
            }
        }
        todo!("Should just return None or maybe NoReturn?");
    }

    fn iter_return_or_yield(&self) -> ReturnOrYieldIterator<'db> {
        let def_point = self.file.points.get(self.node_index + 1);
        let first_return_or_yield = def_point.get_node_index();
        ReturnOrYieldIterator {
            file: self.file,
            next_node_index: first_return_or_yield,
        }
    }

    fn is_generator(&self) -> bool {
        for return_or_yield in self.iter_return_or_yield() {
            if let ReturnOrYield::Yield(_) = return_or_yield {
                return true;
            }
        }
        false
    }

    pub fn as_point_link(&self) -> PointLink {
        PointLink::new(self.file.get_file_index(), self.node_index)
    }
}

impl<'db> Value<'db> for Function<'db> {
    fn get_kind(&self) -> ValueKind {
        ValueKind::Function
    }

    fn get_name(&self) -> &'db str {
        let func = FunctionDef::by_index(&self.file.tree, self.node_index);
        func.name().as_str()
    }

    fn lookup(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> Inferred<'db> {
        todo!()
    }

    fn execute(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
    ) -> Inferred<'db> {
        if let Some(return_annotation) = self.get_node().annotation() {
            let expr = return_annotation.expression();
            if let Some(inferred) = resolve_type_vars(
                i_s,
                self.file,
                expr,
                &mut FunctionTypeVarFinder::new(self.file, self, args),
            ) {
                inferred
            } else {
                self.file
                    .get_inference(i_s)
                    .infer_annotation_expression(expr)
            }
        } else {
            self.execute_without_annotation(i_s, args)
        }
    }
}

struct ReturnOrYieldIterator<'db> {
    file: &'db PythonFile,
    next_node_index: NodeIndex,
}

impl<'db> Iterator for ReturnOrYieldIterator<'db> {
    type Item = ReturnOrYield<'db>;
    fn next(&mut self) -> Option<Self::Item> {
        if self.next_node_index == 0 {
            None
        } else {
            let point = self.file.points.get(self.next_node_index);
            let index = self.next_node_index;
            self.next_node_index = point.get_node_index();
            Some(ReturnOrYield::by_index(&self.file.tree, index - 1))
        }
    }
}

pub struct InferrableParamIterator<'db, 'a> {
    arguments: ArgumentIterator<'db, 'a>,
    params: ParamIterator<'db>,
    unused_keyword_arguments: Vec<Argument<'db, 'a>>,
}

impl<'db, 'a> InferrableParamIterator<'db, 'a> {
    fn new(params: ParamIterator<'db>, arguments: ArgumentIterator<'db, 'a>) -> Self {
        InferrableParamIterator {
            arguments,
            params,
            unused_keyword_arguments: vec![],
        }
    }

    fn get_next_argument(&mut self, param: &Param<'db>) -> Option<Argument<'db, 'a>> {
        for (i, unused) in self.unused_keyword_arguments.iter().enumerate() {
            match unused {
                Argument::Keyword(name, reference) => {
                    if name == &param.name_definition().name().as_str() {
                        return Some(self.unused_keyword_arguments.remove(i));
                    }
                }
                _ => unreachable!(),
            }
        }
        for argument in &mut self.arguments {
            // TODO check param type here and make sure that it makes sense.
            match argument {
                Argument::Keyword(name, reference) => {
                    todo!()
                }
                _ => return Some(argument),
            }
        }
        None
    }
}

impl<'db, 'a> Iterator for InferrableParamIterator<'db, 'a> {
    type Item = InferrableParam<'db, 'a>;

    fn next(&mut self) -> Option<Self::Item> {
        self.params.next().map(|param| {
            let argument = self.get_next_argument(&param);
            InferrableParam { param, argument }
        })
    }
}

pub struct InferrableParam<'db, 'a> {
    pub param: Param<'db>,
    pub argument: Option<Argument<'db, 'a>>,
}

impl<'db, 'a> InferrableParam<'db, 'a> {
    pub fn infer(self, i_s: &mut InferenceState<'db, '_>) -> Inferred<'db> {
        debug!(
            "Infer param {}",
            self.param.name_definition().name().as_str()
        );
        self.argument
            .map(|a| a.infer(i_s))
            .unwrap_or_else(|| todo!())
    }

    fn is_at(&self, index: NodeIndex) -> bool {
        self.param.name_definition().name().index() == index
    }
}
