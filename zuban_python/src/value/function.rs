use parsa_python::{
    NodeIndex, NonterminalType, PyNode,
    PyNodeType::{Nonterminal, Terminal},
    TerminalType,
};
use parsa_python_ast::{FunctionDef, Param, ParamIterator, StarExpressions};
use std::fmt;

use super::{Value, ValueKind};
use crate::arguments::{Argument, ArgumentIterator, Arguments, SimpleArguments};
use crate::database::{Database, Execution, Locality, Point, PointLink, Specific};
use crate::debug;
use crate::file::PythonFile;
use crate::file_state::File;
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

    fn iter_inferrable_params(
        &self,
        args: &dyn Arguments<'db>,
    ) -> impl Iterator<Item = InferrableParam<'db>> {
        InferrableParamIterator::new(self.get_node().iter_params(), args.iter_arguments())
    }

    pub fn infer_param(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        param_name_index: NodeIndex,
        args: &dyn Arguments<'db>,
    ) -> Inferred<'db> {
        let func_node = self
            .file
            .tree
            .get_node_by_index(param_name_index)
            .get_parent_until(&[Nonterminal(NonterminalType::function_def)])
            .unwrap();
        let temporary_args;
        let temporary_func;
        let (check_args, func) = if func_node.index == self.node_index {
            (args, self)
        } else {
            let mut execution = args.get_outer_execution();
            loop {
                let exec = execution.unwrap();
                if func_node.index == exec.function.node_index {
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
        for node in self.iter_return_or_yield() {
            debug_assert_eq!(node.get_type(), Nonterminal(NonterminalType::return_stmt));
            // TODO multiple returns, this is an early exit
            return self
                .file
                .get_inference(&mut inner_i_s)
                .infer_star_expressions(StarExpressions::new(node.get_nth_child(1)))
                .resolve_function_return(&mut inner_i_s);
        }
        todo!("Should just return None or maybe NoReturn?");
    }

    fn iter_return_or_yield(&self) -> ReturnOrYieldIterator<'db> {
        let def_point = self.file.get_point(self.node_index + 1);
        let first_return_or_yield = def_point.get_node_index();
        ReturnOrYieldIterator {
            file: self.file,
            next_node_index: first_return_or_yield,
        }
    }

    fn is_generator(&self) -> bool {
        for node in self.iter_return_or_yield() {
            if node.is_type(Nonterminal(NonterminalType::yield_expr)) {
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
        let func_node = self.file.tree.get_node_by_index(self.node_index);
        func_node.get_nth_child(1).get_nth_child(0).get_code()
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
                expr.0,
                &mut FunctionTypeVarFinder::new(self.file, self, args),
            ) {
                inferred
            } else {
                let inferred = self.file.get_inference(i_s).infer_expression(expr.0);
                inferred.run_on_value(i_s, &|i_s, v| {
                    // TODO locality is wrong!!!!!1
                    let point = if v.get_kind() == ValueKind::Class {
                        Point::new_simple_language_specific(
                            Specific::AnnotationInstance,
                            Locality::Stmt,
                        )
                    } else {
                        Point::new_missing_or_unknown(self.file.get_file_index(), Locality::Stmt);
                        todo!();
                    };
                    Inferred::new_and_save(self.file, return_annotation.0, point)
                })
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
    type Item = PyNode<'db>;
    fn next(&mut self) -> Option<Self::Item> {
        if self.next_node_index == 0 {
            None
        } else {
            let result = self.file.tree.get_node_by_index(self.next_node_index - 1);
            let point = self.file.get_point(self.next_node_index);
            self.next_node_index = point.get_node_index();
            Some(result)
        }
    }
}

fn resolve_type_vars<'db, 'a>(
    i_s: &mut InferenceState<'db, '_>,
    file: &'db PythonFile,
    node: PyNode<'db>,
    type_var_finder: &mut impl TypeVarFinder<'db, 'a>,
) -> Option<Inferred<'db>> {
    //let type_var = Ty
    let inferred = file.get_inference(i_s).infer_expression(node);
    if inferred.is_type_var(i_s) {
        type_var_finder
            .lookup(i_s, node.get_code())
            .or_else(|| todo!())
    } else {
        if !node.is_leaf() {
            for node in node.iter_children() {
                if node.is_type(Terminal(TerminalType::Name)) {
                    if let Some(resolved_type_var) =
                        resolve_type_vars(i_s, file, node, type_var_finder)
                    {
                        todo!()
                    }
                }
            }
        }
        None
    }
}

trait TypeVarFinder<'db, 'a> {
    fn lookup(&mut self, i_s: &mut InferenceState<'db, '_>, name: &str) -> Option<Inferred<'db>>;
}

struct FunctionTypeVarFinder<'db, 'a> {
    file: &'db PythonFile,
    function: &'a Function<'db>,
    args: &'a dyn Arguments<'db>,
    calculated_type_vars: Option<Vec<(&'db str, Inferred<'db>)>>,
}

impl<'db, 'a> TypeVarFinder<'db, 'a> for FunctionTypeVarFinder<'db, 'a> {
    fn lookup(&mut self, i_s: &mut InferenceState<'db, '_>, name: &str) -> Option<Inferred<'db>> {
        if let Some(type_vars) = &self.calculated_type_vars {
            for (type_var, result) in type_vars {
                if *type_var == name {
                    return Some(result.clone());
                }
            }
            None
        } else {
            self.calculate_type_vars(i_s);
            self.lookup(i_s, name)
        }
    }
}

impl<'db, 'a> FunctionTypeVarFinder<'db, 'a> {
    fn new(
        file: &'db PythonFile,
        function: &'a Function<'db>,
        args: &'a dyn Arguments<'db>,
    ) -> Self {
        Self {
            file,
            function,
            args,
            calculated_type_vars: None,
        }
    }

    fn calculate_type_vars(&mut self, i_s: &mut InferenceState<'db, '_>) {
        let mut calculated_type_vars = vec![];
        for p in self.function.iter_inferrable_params(self.args) {
            if let Some(annotation) = p.param.annotation() {
                // TODO we should only check names, not expressions
                let name = annotation.0;
                if !calculated_type_vars
                    .iter()
                    .any(|(n, _)| *n == name.get_code())
                {
                    let inferred = self.file.get_inference(i_s).infer_expression(name);
                    if inferred.is_type_var(i_s) {
                        calculated_type_vars.push((name.get_code(), p.infer(i_s)));
                    } else {
                        todo!()
                    }
                }
            }
        }
        self.calculated_type_vars = Some(calculated_type_vars);
    }
}

struct InferrableParamIterator<'db> {
    arguments: ArgumentIterator<'db>,
    params: ParamIterator<'db>,
    unused_keyword_arguments: Vec<Argument<'db>>,
}

impl<'db> InferrableParamIterator<'db> {
    fn new(params: ParamIterator<'db>, arguments: ArgumentIterator<'db>) -> Self {
        InferrableParamIterator {
            arguments,
            params,
            unused_keyword_arguments: vec![],
        }
    }

    fn get_next_argument(&mut self, param: &Param<'db>) -> Option<Argument<'db>> {
        for (i, unused) in self.unused_keyword_arguments.iter().enumerate() {
            match unused {
                Argument::KeywordArgument(name, reference) => {
                    if name == &param.name().as_str() {
                        return Some(self.unused_keyword_arguments.remove(i));
                    }
                }
                _ => unreachable!(),
            }
        }
        for argument in &mut self.arguments {
            // TODO check param type here and make sure that it makes sense.
            match argument {
                Argument::KeywordArgument(name, reference) => {
                    todo!()
                }
                _ => return Some(argument),
            }
        }
        None
    }
}

impl<'db> Iterator for InferrableParamIterator<'db> {
    type Item = InferrableParam<'db>;

    fn next(&mut self) -> Option<Self::Item> {
        self.params.next().map(|param| {
            let argument = self.get_next_argument(&param);
            InferrableParam { param, argument }
        })
    }
}

struct InferrableParam<'db> {
    param: Param<'db>,
    argument: Option<Argument<'db>>,
}

impl<'db> InferrableParam<'db> {
    fn infer(self, i_s: &mut InferenceState<'db, '_>) -> Inferred<'db> {
        debug!("Infer param {}", self.param.name().as_str());
        self.argument
            .map(|a| a.infer(i_s))
            .unwrap_or_else(|| todo!())
    }

    fn is_at(&self, index: NodeIndex) -> bool {
        self.param.name().index() == index
    }
}
