use parsa::Node;
use parsa::NodeIndex;
use parsa_python::{
    NonterminalType, PyNode,
    PyNodeType::{Nonterminal, Terminal},
    SiblingIterator, TerminalType,
};

use super::{Value, ValueKind};
use crate::arguments::{Argument, ArgumentIterator, ArgumentType, Arguments};
use crate::database::{Database, Locality, Point, PointLink, Specific};
use crate::debug;
use crate::file::PythonFile;
use crate::file_state::File;
use crate::inferred::Inferred;

#[derive(Debug)]
pub struct Function<'a> {
    file: &'a PythonFile,
    node_index: NodeIndex,
}

impl<'a> Function<'a> {
    pub fn new(file: &'a PythonFile, node_index: NodeIndex) -> Self {
        Self { file, node_index }
    }

    fn get_node(&self) -> PyNode<'a> {
        self.file.tree.get_node_by_index(self.node_index)
    }

    fn iter_params(&self) -> ParamIterator<'a> {
        // function_def: "def" name_definition function_def_parameters ...
        // function_def_parameters: "(" [parameters] ")"
        let params = self.get_node().get_nth_child(2).get_nth_child(1);
        if params.is_type(Nonterminal(NonterminalType::parameters)) {
            let positional_only = params
                .iter_children()
                .any(|n| n.is_leaf() && n.get_code() == "/");
            ParamIterator::Iterator(params.iter_children(), positional_only)
        } else {
            ParamIterator::Finished
        }
    }

    fn iter_inferrable_params(
        &self,
        args: &Arguments<'a>,
    ) -> impl Iterator<Item = InferrableParam<'a>> {
        InferrableParamIterator::new(self.iter_params(), args.iter_arguments())
    }

    pub fn infer_param(
        &self,
        database: &'a Database,
        param_name_index: NodeIndex,
        args: &Arguments<'a>,
    ) -> Inferred<'a> {
        for param in self.iter_inferrable_params(args) {
            if param.is_at(param_name_index) {
                return param.infer(database);
            }
        }
        unreachable!("{:?}", param_name_index)
    }

    fn execute_without_annotation(
        &self,
        database: &'a Database,
        args: &Arguments<'a>,
    ) -> Inferred<'a> {
        if self.is_generator() {
            todo!("Maybe not check here, because this could be precalculated and cached");
        }
        for node in self.iter_return_or_yield() {
            debug_assert_eq!(node.get_type(), Nonterminal(NonterminalType::return_stmt));
            // TODO multiple returns, this is an early exit
            return self
                .file
                .get_inference(database)
                .infer_star_expressions(node.get_nth_child(1))
                .resolve_closure_and_params(self, args);
        }
        todo!("Should just return None or maybe NoReturn?");
    }

    fn iter_return_or_yield(&self) -> ReturnOrYieldIterator<'a> {
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

    pub fn to_point_link(&self) -> PointLink {
        PointLink::new(self.file.get_file_index(), self.node_index)
    }
}

impl<'a> Value<'a> for Function<'a> {
    fn get_kind(&self) -> ValueKind {
        ValueKind::Function
    }

    fn get_name(&self) -> &'a str {
        let func_node = self.file.tree.get_node_by_index(self.node_index);
        func_node.get_nth_child(1).get_nth_child(0).get_code()
    }

    fn lookup(&self, database: &'a Database, name: &str) -> Inferred<'a> {
        todo!()
    }

    fn execute(&self, database: &'a Database, args: &Arguments<'a>) -> Inferred<'a> {
        let return_annotation = self.get_node().get_nth_child(3);
        // Is an annotation
        if return_annotation.is_type(Nonterminal(NonterminalType::return_annotation)) {
            let expr = return_annotation.get_nth_child(1);
            if let Some(inferred) = resolve_type_vars(
                database,
                self.file,
                expr,
                &mut FunctionTypeVarFinder::new(database, self.file, self, args),
            ) {
                inferred
            } else {
                let inferred = self.file.infer_expression(database, expr);
                inferred.run_on_value(|v| {
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
                    Inferred::new_and_save(database, self.file, return_annotation, point)
                })
            }
        } else {
            self.execute_without_annotation(database, args)
        }
    }
}

struct ReturnOrYieldIterator<'a> {
    file: &'a PythonFile,
    next_node_index: NodeIndex,
}

impl<'a> Iterator for ReturnOrYieldIterator<'a> {
    type Item = PyNode<'a>;
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

enum ParamIterator<'a> {
    Iterator(SiblingIterator<'a>, bool),
    Finished,
}

impl<'a> Iterator for ParamIterator<'a> {
    type Item = Param<'a>;
    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Iterator(iterator, positional_only) => {
                for node in iterator {
                    use NonterminalType::*;
                    use ParamType::*;
                    if node.is_type(Nonterminal(param_no_default))
                        || node.is_type(Nonterminal(param_with_default))
                    {
                        return Some(Self::Item::new(
                            &mut node.iter_children(),
                            if *positional_only {
                                PositionalOnly
                            } else {
                                PositionalOrKeyword
                            },
                        ));
                    } else if node.is_type(Nonterminal(star_etc)) {
                        *self = Self::Iterator(node.iter_children(), false);
                        return self.next();
                    } else if node.is_type(Nonterminal(param_maybe_default)) {
                        debug_assert!(!*positional_only);
                        return Some(Self::Item::new(&mut node.iter_children(), KeywordOnly));
                    } else if node.is_type(Nonterminal(starred_param)) {
                        return Some(Self::Item::new(
                            &mut node.iter_children().skip(1),
                            MultiArgs,
                        ));
                    } else if node.is_type(Nonterminal(double_starred_param)) {
                        return Some(Self::Item::new(
                            &mut node.iter_children().skip(1),
                            MultiKwargs,
                        ));
                    }
                }
                None
            }
            Self::Finished => None,
        }
    }
}

struct Param<'a> {
    typ: ParamType,
    name_node: PyNode<'a>,
    annotation_node: Option<PyNode<'a>>,
    default_node: Option<PyNode<'a>>,
}

impl<'a> Param<'a> {
    fn new(param_children: &mut impl Iterator<Item = PyNode<'a>>, typ: ParamType) -> Self {
        let name_node = param_children.next().unwrap();
        debug_assert_eq!(
            name_node.get_type(),
            Nonterminal(NonterminalType::name_definition)
        );
        let annotation_node = param_children
            .next()
            .map(|n: PyNode<'a>| n.get_nth_child(1));
        param_children.next();
        let default_node = param_children.next();
        Self {
            typ,
            name_node: name_node.get_nth_child(0),
            annotation_node,
            default_node,
        }
    }

    fn get_name(&self) -> &'a str {
        self.name_node.get_code()
    }
}

enum ParamType {
    PositionalOnly,
    PositionalOrKeyword,
    MultiArgs,
    MultiKwargs,
    KeywordOnly,
}

fn resolve_type_vars<'a>(
    database: &'a Database,
    file: &'a PythonFile,
    node: PyNode<'a>,
    type_var_finder: &mut impl TypeVarFinder<'a>,
) -> Option<Inferred<'a>> {
    //let type_var = Ty
    let inferred = file.infer_expression(database, node);
    if inferred.is_type_var() {
        type_var_finder.lookup(node.get_code()).or_else(|| todo!())
    } else {
        if !node.is_leaf() {
            for node in node.iter_children() {
                if node.is_type(Terminal(TerminalType::Name)) {
                    if let Some(resolved_type_var) =
                        resolve_type_vars(database, file, node, type_var_finder)
                    {
                        todo!()
                    }
                }
            }
        }
        None
    }
}

trait TypeVarFinder<'a> {
    fn lookup(&mut self, name: &str) -> Option<Inferred<'a>>;
}

struct FunctionTypeVarFinder<'a, 'b> {
    database: &'a Database,
    file: &'a PythonFile,
    function: &'b Function<'a>,
    args: &'b Arguments<'a>,
    calculated_type_vars: Option<Vec<(&'a str, Inferred<'a>)>>,
}

impl<'a, 'b> TypeVarFinder<'a> for FunctionTypeVarFinder<'a, 'b> {
    fn lookup(&mut self, name: &str) -> Option<Inferred<'a>> {
        if let Some(type_vars) = &self.calculated_type_vars {
            for (type_var, result) in type_vars {
                if *type_var == name {
                    return Some(result.clone());
                }
            }
            None
        } else {
            self.calculate_type_vars();
            self.lookup(name)
        }
    }
}

impl<'a, 'b> FunctionTypeVarFinder<'a, 'b> {
    fn new(
        database: &'a Database,
        file: &'a PythonFile,
        function: &'b Function<'a>,
        args: &'b Arguments<'a>,
    ) -> Self {
        Self {
            database,
            file,
            function,
            args,
            calculated_type_vars: None,
        }
    }

    fn calculate_type_vars(&mut self) {
        let mut calculated_type_vars = vec![];
        for p in self.function.iter_inferrable_params(self.args) {
            if let Some(annotation) = p.param.annotation_node {
                // TODO we should only check names, not expressions
                let name = annotation;
                if !calculated_type_vars
                    .iter()
                    .any(|(n, _)| *n == name.get_code())
                {
                    let inferred = self.file.infer_expression(self.database, name);
                    if inferred.is_type_var() {
                        calculated_type_vars.push((name.get_code(), p.infer(self.database)));
                    } else {
                        todo!()
                    }
                }
            }
        }
        self.calculated_type_vars = Some(calculated_type_vars);
    }
}

struct InferrableParamIterator<'a> {
    arguments: ArgumentIterator<'a>,
    params: ParamIterator<'a>,
    unused_keyword_arguments: Vec<Argument<'a>>,
}

impl<'a> InferrableParamIterator<'a> {
    fn new(params: ParamIterator<'a>, arguments: ArgumentIterator<'a>) -> Self {
        InferrableParamIterator {
            arguments,
            params,
            unused_keyword_arguments: vec![],
        }
    }

    fn get_next_argument(&mut self, param: &Param<'a>) -> Option<Argument<'a>> {
        for (i, unused) in self.unused_keyword_arguments.iter().enumerate() {
            match unused.typ {
                ArgumentType::KeywordArgument(name) => {
                    if name == param.get_name() {
                        return Some(self.unused_keyword_arguments.remove(i));
                    }
                }
                ArgumentType::Argument => unreachable!(),
            }
        }
        for argument in &mut self.arguments {
            // TODO check param type here and make sure that it makes sense.
            match argument.typ {
                ArgumentType::KeywordArgument(name) => {
                    todo!()
                }
                ArgumentType::Argument => return Some(argument),
            }
        }
        None
    }
}

impl<'a> Iterator for InferrableParamIterator<'a> {
    type Item = InferrableParam<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        self.params.next().map(|param| {
            let argument = self.get_next_argument(&param);
            InferrableParam { param, argument }
        })
    }
}

struct InferrableParam<'a> {
    param: Param<'a>,
    argument: Option<Argument<'a>>,
}

impl<'a> InferrableParam<'a> {
    fn infer(self, database: &'a Database) -> Inferred<'a> {
        debug!("Infer param {}", self.param.get_name());
        self.argument
            .map(|a| a.infer(database))
            .unwrap_or_else(|| todo!())
    }

    fn is_at(&self, index: NodeIndex) -> bool {
        self.param.name_node.index == index
    }
}
