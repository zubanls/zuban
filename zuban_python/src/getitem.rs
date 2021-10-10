use parsa_python_ast::{
    NamedExpression, NodeIndex, Slice as ASTSlice, SliceType as ASTSliceType, Slices as ASTSlices,
};

use crate::arguments::{ArgumentIterator, Arguments, ArgumentsType};
use crate::database::Execution;
use crate::file::PythonFile;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::value::Function;

#[derive(Debug, Copy, Clone)]
pub enum SliceType<'db> {
    Simple(Simple<'db>),
    Slice(Slice<'db>),
    Slices(Slices<'db>),
}

impl<'db> SliceType<'db> {
    pub fn new(file: &'db PythonFile, primary_index: NodeIndex, type_: ASTSliceType<'db>) -> Self {
        match type_ {
            ASTSliceType::NamedExpression(named_expr) => Self::Simple(Simple {
                file,
                primary_index,
                named_expr,
            }),
            ASTSliceType::Slice(slice) => Self::Slice(Slice { file, slice }),
            ASTSliceType::Slices(slices) => Self::Slices(Slices { file, slices }),
        }
    }
}

impl<'db> SliceType<'db> {
    pub fn as_args<'a>(&'a self) -> SliceArguments<'db, 'a> {
        SliceArguments(self)
    }
}

#[derive(Debug, Copy, Clone)]
pub struct Simple<'db> {
    pub file: &'db PythonFile,
    pub primary_index: NodeIndex,
    named_expr: NamedExpression<'db>,
}

impl<'db> Simple<'db> {
    pub fn infer(&self, i_s: &mut InferenceState<'db, '_>) -> Inferred<'db> {
        self.file
            .get_inference(i_s)
            .infer_named_expression(self.named_expr)
    }
}

#[derive(Debug, Copy, Clone)]
pub struct Slice<'db> {
    file: &'db PythonFile,
    slice: ASTSlice<'db>,
}

#[derive(Debug, Copy, Clone)]
pub struct Slices<'db> {
    file: &'db PythonFile,
    slices: ASTSlices<'db>,
}

#[derive(Debug)]
pub struct SliceArguments<'db, 'a>(&'a SliceType<'db>);

impl<'db> Arguments<'db> for SliceArguments<'db, '_> {
    fn iter_arguments(&self) -> ArgumentIterator<'db> {
        ArgumentIterator::SliceType(*self.0)
    }

    fn get_outer_execution(&self) -> Option<&Execution> {
        todo!()
    }

    fn as_execution(&self, function: &Function) -> Execution {
        /*
        Execution::new(
            function.as_point_link(),
            PointLink::new(self.file.get_file_index(), self.primary_node.index()),
            self.in_,
        )
        */
        todo!()
    }

    fn get_type(&self) -> ArgumentsType<'db> {
        /*
        match {
            ArgumentsType::Normal(self.file, self.primary_node)
        }
        */
        todo!()
    }
}
