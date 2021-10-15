use parsa_python_ast::Expression;

use crate::file::PythonFile;
use crate::getitem::SliceType;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;

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
pub struct CalculableGenerics();

impl<'db> Generics<'db> for CalculableGenerics {
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
