use parsa_python_ast::{
    Expression, FunctionDef, NameParent, NodeIndex, Param, ParamIterator, ReturnOrYield,
};
use std::fmt;

use super::{Value, ValueKind};
use crate::arguments::{Argument, ArgumentIterator, Arguments, SimpleArguments};
use crate::database::{
    ClassInfos, ComplexPoint, Database, Execution, Locality, Point, PointLink, PointType, Specific,
    TypeVarIndex,
};
use crate::debug;
use crate::file::PythonFile;
use crate::file_state::File;
use crate::generics::{resolve_type_vars, FunctionTypeVarFinder};
use crate::inference_state::InferenceState;
use crate::inferred::{Inferrable, Inferred};

pub struct Function<'db> {
    pub file: &'db PythonFile,
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
    // Functions use the following points:
    // - "def" to redirect to the first return/yield
    // - "(" to redirect to save calculated type vars
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
        skip_first_param: bool,
    ) -> InferrableParamIterator<'db, 'a> {
        let mut params = self.get_node().params().iter();
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

    fn class_infos(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
    ) -> Option<&'db ClassInfos> {
        // TODO getting the class this way is a bad idea.
        if let Some(p) = self.iter_inferrable_params(args, false).next() {
            if let Some(Argument::PositionalFirst(instance)) = p.argument {
                return Some(instance.class(i_s).get_class_infos(i_s));
            }
        }
        None
    }

    fn get_calculated_type_vars(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
    ) -> Option<&'db [PointLink]> {
        // To save the generics (which happens mostly not really), just use the def keyword's
        // storage.
        // + 1 for def; + 2 for name + 1 for (
        let def_node_index = self.node_index + 4;
        let p = self.file.points.get(def_node_index);
        if p.is_calculated() {
            if p.get_type() == PointType::Complex {
                if let ComplexPoint::FunctionTypeVars(vars) =
                    self.file.complex_points.get(p.get_complex_index())
                {
                    return Some(vars);
                }
            }
            return None;
        }
        let class_infos = self.class_infos(i_s, args);
        let mut found_type_vars = vec![];
        let func_node = self.get_node();
        for param in func_node.params().iter() {
            if let Some(annotation) = param.annotation() {
                self.search_type_vars(
                    i_s,
                    &annotation.expression(),
                    class_infos,
                    &mut found_type_vars,
                );
            }
        }
        if let Some(return_annot) = func_node.annotation() {
            self.search_type_vars(
                i_s,
                &return_annot.expression(),
                class_infos,
                &mut found_type_vars,
            );
        }
        match found_type_vars.len() {
            0 => self
                .file
                .points
                .set(def_node_index, Point::new_node_analysis(Locality::Stmt)),
            _ => self.file.complex_points.insert(
                &self.file.points,
                def_node_index,
                ComplexPoint::FunctionTypeVars(found_type_vars.into_boxed_slice()),
            ),
        }
        debug_assert!(self.file.points.get(def_node_index).is_calculated());
        self.get_calculated_type_vars(i_s, args)
    }

    fn search_type_vars(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        expression: &Expression<'db>,
        class_infos: Option<&'db ClassInfos>,
        found_type_vars: &mut Vec<PointLink>,
    ) {
        for n in expression.search_names() {
            if matches!(n.parent(), NameParent::Atom) {
                let inferred = self.file.get_inference(i_s).infer_name_reference(n);
                if let Some(definition) = inferred.maybe_type_var(i_s) {
                    let link = definition.as_link();
                    if let Some(class_infos) = class_infos {
                        if let Some(index) = class_infos.find_type_var_index(link) {
                            // Overwrite with a better type var definition.
                            self.file
                                .points
                                .set(n.index(), Point::new_class_type_var(index, Locality::Stmt));
                            continue;
                        }
                    }

                    let i = found_type_vars.iter().position(|&r| r == link);
                    if i.is_none() {
                        found_type_vars.push(link);
                    };
                    let i = i.unwrap_or_else(|| found_type_vars.len() - 1);
                    self.file.points.set(
                        n.index(),
                        Point::new_function_type_var(TypeVarIndex::new(i), Locality::Stmt),
                    );
                }
            }
        }
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
            let i_s = &mut i_s.with_annotation_instance();
            let func_type_vars = self.get_calculated_type_vars(i_s, args);
            let expr = return_annotation.expression();
            if contains_type_vars(self.file, &expr) {
                let inferred = self.file.get_inference(i_s).infer_expression(expr);
                let mut class = None;
                if let Some(p) = self.iter_inferrable_params(args, false).next() {
                    if let Some(Argument::PositionalFirst(instance)) = p.argument {
                        class = Some(instance.class(i_s));
                    }
                }
                // TODO use t
                let mut finder =
                    func_type_vars.map(|t| FunctionTypeVarFinder::new(self, args, false, None));
                inferred.replace_type_vars(i_s, class.as_ref(), finder.as_mut())
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
        Self {
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
