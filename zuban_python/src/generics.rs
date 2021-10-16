use parsa_python_ast::Expression;

use crate::arguments::{Argument, Arguments};
use crate::file::PythonFile;
use crate::getitem::SliceType;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::value::Function;

pub trait TypeVarFinder<'db, 'a> {
    fn lookup(&mut self, i_s: &mut InferenceState<'db, '_>, name: &str) -> Option<Inferred<'db>>;
}

pub fn resolve_type_vars<'db, 'a>(
    i_s: &mut InferenceState<'db, '_>,
    file: &'db PythonFile,
    expr: Expression<'db>,
    type_var_finder: &mut impl TypeVarFinder<'db, 'a>,
) -> Option<Inferred<'db>> {
    let mut i_s = i_s.with_annotation_instance();
    let inferred = file.get_inference(&mut i_s).infer_expression(expr);
    if inferred.is_type_var(&mut i_s) {
        type_var_finder
            .lookup(&mut i_s, expr.get_legacy_node().get_code())
            .or_else(|| todo!())
    } else {
        /*
        if !node.is_leaf() {
            for node in node.iter_children() {
                if node.is_type(Terminal(TerminalType::Name)) {
                    if let Some(resolved_type_var) =
                        resolve_type_vars(&mut i_s, file, node, type_var_finder)
                    {
                        todo!()
                    }
                }
            }
        }
        */
        None
    }
}

pub trait Generics<'db>: std::fmt::Debug {
    fn get_nth(&self, i_s: &mut InferenceState<'db, '_>, n: usize) -> Option<Inferred<'db>>;
}

#[derive(Debug)]
pub struct ExpectNoGenerics();

impl<'db> Generics<'db> for ExpectNoGenerics {
    fn get_nth(&self, i_s: &mut InferenceState<'db, '_>, n: usize) -> Option<Inferred<'db>> {
        unreachable!("Should not even ask for generics")
    }
}

#[derive(Debug)]
pub struct NoGenerics();

impl<'db> Generics<'db> for NoGenerics {
    fn get_nth(&self, i_s: &mut InferenceState<'db, '_>, n: usize) -> Option<Inferred<'db>> {
        None
    }
}

#[derive(Debug)]
pub struct CalculableGenerics<'db, 'a> {
    init: &'a Function<'db>,
}

impl<'db, 'a> CalculableGenerics<'db, 'a> {
    pub fn new(init: &'a Function<'db>) -> Self {
        Self { init }
    }
}

impl<'db> Generics<'db> for CalculableGenerics<'db, '_> {
    fn get_nth(&self, i_s: &mut InferenceState<'db, '_>, n: usize) -> Option<Inferred<'db>> {
        todo!()
    }
}

#[derive(Debug)]
pub struct AnnotationGenerics<'db> {
    slice_type: SliceType<'db>,
}

impl<'db> AnnotationGenerics<'db> {
    pub fn new(slice_type: SliceType<'db>) -> Self {
        Self { slice_type }
    }
}

impl<'db> Generics<'db> for AnnotationGenerics<'db> {
    fn get_nth(&self, i_s: &mut InferenceState<'db, '_>, n: usize) -> Option<Inferred<'db>> {
        match self.slice_type {
            SliceType::Simple(simple) => {
                if n == 0 {
                    Some(simple.infer_annotation(i_s))
                } else {
                    None
                }
            }
            SliceType::Slices(slices) => {
                // This is an error, the annotation List[foo:bar] makes no sense.
                dbg!(slices);
                todo!()
            }
            SliceType::Slice(slice) => {
                // This is an error, the annotation List[foo:bar] makes no sense.
                None
            }
        }
    }
}

pub struct FunctionTypeVarFinder<'db, 'a> {
    file: &'db PythonFile,
    function: &'a Function<'db>,
    args: &'a dyn Arguments<'db>,
    calculated_type_vars: Option<Vec<(&'db str, Inferred<'db>)>>,
}

impl<'db, 'a> TypeVarFinder<'db, 'a> for FunctionTypeVarFinder<'db, 'a> {
    fn lookup(&mut self, i_s: &mut InferenceState<'db, '_>, name: &str) -> Option<Inferred<'db>> {
        if let Some(type_vars) = &self.calculated_type_vars {
            if let Some(p) = self.function.iter_inferrable_params(self.args).next() {
                if let Some(Argument::PositionalInstance(instance)) = p.argument {
                    if let Some(inf) = instance.lookup_type_var(i_s, name) {
                        return Some(inf);
                    }
                }
            }
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
    pub fn new(
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
                let name = annotation.expression().get_legacy_node();
                if !calculated_type_vars
                    .iter()
                    .any(|(n, _)| *n == name.get_code())
                {
                    let inferred = self
                        .file
                        .get_inference(i_s)
                        .infer_expression(annotation.expression());
                    if inferred.is_type_var(i_s) {
                        calculated_type_vars.push((name.get_code(), p.infer(i_s)));
                    } else {
                        // TODO stuff like List[T]
                    }
                }
            }
        }
        self.calculated_type_vars = Some(calculated_type_vars);
    }
}
