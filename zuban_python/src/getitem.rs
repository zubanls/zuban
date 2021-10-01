use parsa_python_ast::{
    NamedExpression, Slice as ASTSlice, SliceType as ASTSliceType, Slices as ASTSlices,
};

use crate::file::PythonFile;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;

pub enum SliceType<'db> {
    Simple(Simple<'db>),
    Slice(Slice<'db>),
    Slices(Slices<'db>),
}

impl<'db> SliceType<'db> {
    pub fn new(file: &'db PythonFile, type_: ASTSliceType<'db>) -> Self {
        match type_ {
            ASTSliceType::NamedExpression(named_expr) => Self::Simple(Simple { file, named_expr }),
            ASTSliceType::Slice(slice) => Self::Slice(Slice { file, slice }),
            ASTSliceType::Slices(slices) => Self::Slices(Slices { file, slices }),
        }
    }
}

pub struct Simple<'db> {
    file: &'db PythonFile,
    named_expr: NamedExpression<'db>,
}

impl<'db> Simple<'db> {
    pub fn infer(&self, i_s: &mut InferenceState<'db, '_>) -> Inferred<'db> {
        self.file
            .get_inference(i_s)
            .infer_named_expression(self.named_expr.0)
    }
}

pub struct Slice<'db> {
    file: &'db PythonFile,
    slice: ASTSlice<'db>,
}

pub struct Slices<'db> {
    file: &'db PythonFile,
    slices: ASTSlices<'db>,
}
