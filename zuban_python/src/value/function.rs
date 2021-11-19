use parsa_python_ast::{Expression, FunctionDef, NodeIndex, Param, ParamIterator, ReturnOrYield};
use std::fmt;

use super::{Value, ValueKind};
use crate::arguments::{Argument, ArgumentIterator, Arguments, SimpleArguments};
use crate::database::{
    ComplexPoint, Database, Execution, Locality, Overload, Point, PointLink, Specific,
};
use crate::debug;
use crate::file::PythonFile;
use crate::generics::{search_type_vars, TypeVarMatcher};
use crate::inference_state::InferenceState;
use crate::inferred::{Inferrable, Inferred, NodeReference};

pub struct Function<'db> {
    pub reference: NodeReference<'db>,
}

impl<'db> fmt::Debug for Function<'db> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("Function")
            .field("file", self.reference.file)
            .field("node", &self.node())
            .finish()
    }
}

impl<'db> Function<'db> {
    // Functions use the following points:
    // - "def" to redirect to the first return/yield
    // - "(" to redirect to save calculated type vars
    pub fn new(reference: NodeReference<'db>) -> Self {
        Self { reference }
    }

    pub fn from_execution(database: &'db Database, execution: &Execution) -> Self {
        let f_func = database.loaded_python_file(execution.function.file);
        Function::new(NodeReference {
            file: f_func,
            node_index: execution.function.node_index,
        })
    }

    fn node(&self) -> FunctionDef<'db> {
        FunctionDef::by_index(&self.reference.file.tree, self.reference.node_index)
    }

    pub fn iter_inferrable_params<'a>(
        &self,
        args: &'a dyn Arguments<'db>,
        skip_first_param: bool,
    ) -> InferrableParamIterator<'db, 'a> {
        let mut params = self.node().params().iter();
        if skip_first_param {
            params.next();
        }
        InferrableParamIterator::new(params, args.iter_arguments())
    }

    pub fn infer_param(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        param_name_index: NodeIndex,
        args: &dyn Arguments<'db>,
    ) -> Inferred<'db> {
        let func_node =
            FunctionDef::from_param_name_index(&self.reference.file.tree, param_name_index);
        let temporary_args;
        let temporary_func;
        let (check_args, func) = if func_node.index() == self.reference.node_index {
            (args, self)
        } else {
            let mut execution = args.outer_execution();
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
        for param in func.iter_inferrable_params(check_args, false) {
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
                        .reference
                        .file
                        .inference(&mut inner_i_s)
                        .infer_star_expressions(ret.star_expressions())
                        .resolve_function_return(&mut inner_i_s)
                }
                ReturnOrYield::Yield(yield_expr) => unreachable!(),
            }
        }
        todo!("Should just return None or maybe NoReturn?");
    }

    fn iter_return_or_yield(&self) -> ReturnOrYieldIterator<'db> {
        let def_point = self
            .reference
            .file
            .points
            .get(self.reference.node_index + 1);
        let first_return_or_yield = def_point.node_index();
        ReturnOrYieldIterator {
            file: self.reference.file,
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

    pub fn calculated_type_vars(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
    ) -> Option<&'db [PointLink]> {
        // To save the generics (which happens mostly not really), just use the def keyword's
        // storage.
        // + 1 for def; + 2 for name + 1 for (
        let type_var_reference = self.reference.add_to_node_index(4);
        if type_var_reference.point().calculated() {
            if let Some(complex) = type_var_reference.complex() {
                match complex {
                    ComplexPoint::FunctionTypeVars(vars) => return Some(vars),
                    _ => unreachable!(),
                }
            }
            return None;
        }
        let class_infos = args.class_of_method(i_s).map(|c| c.class_infos(i_s));
        let mut found_type_vars = vec![];
        let func_node = self.node();
        let mut add = |n: NodeIndex, type_var_link: PointLink| {
            if let Some(class_infos) = class_infos {
                if let Some(index) = class_infos.find_type_var_index(type_var_link) {
                    // Overwrite with a better type var definition.
                    self.reference.file.points.set(
                        n,
                        Point::new_numbered_type_var(Specific::ClassTypeVar, index, Locality::Stmt),
                    );
                    return None;
                }
            }
            Some(Specific::FunctionTypeVar)
        };
        for param in func_node.params().iter() {
            if let Some(annotation) = param.annotation() {
                search_type_vars(
                    i_s,
                    self.reference.file,
                    &annotation.expression(),
                    &mut add,
                    &mut found_type_vars,
                );
            }
        }
        if let Some(return_annot) = func_node.annotation() {
            search_type_vars(
                i_s,
                self.reference.file,
                &return_annot.expression(),
                &mut add,
                &mut found_type_vars,
            );
        }
        match found_type_vars.len() {
            0 => type_var_reference.set_point(Point::new_node_analysis(Locality::Stmt)),
            _ => type_var_reference.insert_complex(ComplexPoint::FunctionTypeVars(
                found_type_vars.into_boxed_slice(),
            )),
        }
        debug_assert!(type_var_reference.point().calculated());
        self.calculated_type_vars(i_s, args)
    }
}

impl<'db> Value<'db> for Function<'db> {
    fn kind(&self) -> ValueKind {
        ValueKind::Function
    }

    fn name(&self) -> &'db str {
        let func = FunctionDef::by_index(&self.reference.file.tree, self.reference.node_index);
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
        if let Some(return_annotation) = self.node().annotation() {
            let i_s = &mut i_s.with_annotation_instance();
            let func_type_vars = self.calculated_type_vars(i_s, args);
            let expr = return_annotation.expression();
            if contains_type_vars(self.reference.file, &expr) {
                let inferred = self.reference.file.inference(i_s).infer_expression(expr);
                let class = args.class_of_method(i_s);
                debug!(
                    "Inferring generics for {}{}",
                    format!(
                        "{}.",
                        class
                            .map(|c| c.as_str(i_s))
                            .unwrap_or_else(|| "".to_owned())
                    ),
                    self.name()
                );

                let finder = func_type_vars
                    .map(|t| TypeVarMatcher::new(self, args, false, t, Specific::FunctionTypeVar));
                inferred
                    .maybe_numbered_type_var()
                    .map(|point| match point.specific() {
                        Specific::ClassTypeVar => class
                            .unwrap()
                            .generics
                            .nth(i_s, point.type_var_index())
                            .unwrap(),
                        Specific::FunctionTypeVar => {
                            finder.unwrap().nth(i_s, point.type_var_index())
                        }
                        _ => unreachable!(),
                    })
                    .unwrap_or(inferred)
            } else {
                self.reference
                    .file
                    .inference(i_s)
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
            self.next_node_index = point.node_index();
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
        Self {
            arguments,
            params,
            unused_keyword_arguments: vec![],
        }
    }

    fn next_argument(&mut self, param: &Param<'db>) -> Option<Argument<'db, 'a>> {
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
            let argument = self.next_argument(&param);
            InferrableParam { param, argument }
        })
    }
}

#[derive(Debug)]
pub struct InferrableParam<'db, 'a> {
    pub param: Param<'db>,
    pub argument: Option<Argument<'db, 'a>>,
}

impl<'db> InferrableParam<'db, '_> {
    fn is_at(&self, index: NodeIndex) -> bool {
        self.param.name_definition().name().index() == index
    }
}

impl<'db> Inferrable<'db> for InferrableParam<'db, '_> {
    fn infer(&self, i_s: &mut InferenceState<'db, '_>) -> Inferred<'db> {
        debug!(
            "Infer param {}",
            self.param.name_definition().name().as_str()
        );
        self.argument
            .as_ref()
            .map(|a| a.infer(i_s))
            .unwrap_or_else(|| todo!())
    }
}

#[inline]
fn contains_type_vars(file: &PythonFile, expr: &Expression) -> bool {
    for n in expr.search_names() {
        if matches!(
            file.points.get(n.index()).maybe_specific(),
            Some(Specific::ClassTypeVar | Specific::FunctionTypeVar)
        ) {
            return true;
        }
    }
    false
}

#[derive(Debug)]
pub struct OverloadedFunction<'db> {
    reference: NodeReference<'db>,
    overload: &'db Overload,
}

impl<'db> OverloadedFunction<'db> {
    pub fn new(reference: NodeReference<'db>, overload: &'db Overload) -> Self {
        Self {
            reference,
            overload,
        }
    }
}

impl<'db> Value<'db> for OverloadedFunction<'db> {
    fn kind(&self) -> ValueKind {
        ValueKind::Function
    }

    fn name(&self) -> &'db str {
        //let func = FunctionDef::by_index(&self.reference.file.tree, self.reference.node_index);
        //func.name().as_str()
        todo!()
    }

    fn lookup(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> Inferred<'db> {
        todo!()
    }

    fn execute(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
    ) -> Inferred<'db> {
        for link in self.overload.functions.iter() {
            let function = Function::new(NodeReference::from_link(i_s.database, *link));
            let func_type_vars = function.calculated_type_vars(i_s, args);
            let no_type_vars = vec![];
            let mut finder = func_type_vars
                .map(|t| TypeVarMatcher::new(&function, args, false, t, Specific::FunctionTypeVar))
                .unwrap_or_else(|| {
                    TypeVarMatcher::new(
                        &function,
                        args,
                        false,
                        &no_type_vars,
                        Specific::FunctionTypeVar,
                    )
                });
            if finder.matches_signature(i_s) {
                return function.execute(i_s, args);
            }
        }
        todo!()
    }
}
