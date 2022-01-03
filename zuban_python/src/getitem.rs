use parsa_python_ast::{
    NamedExpression, NodeIndex, Slice as ASTSlice, SliceContent, SliceIterator as ASTSliceIterator,
    SliceType as ASTSliceType, Slices as ASTSlices,
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
            ASTSliceType::Slice(slice) => Self::Slice(Slice {
                file,
                primary_index,
                slice,
            }),
            ASTSliceType::Slices(slices) => Self::Slices(Slices {
                file,
                primary_index,
                slices,
            }),
        }
    }

    pub fn file(&self) -> &'db PythonFile {
        match self {
            Self::Simple(simple) => simple.file,
            Self::Slice(slice) => slice.file,
            Self::Slices(slices) => slices.file,
        }
    }

    pub fn primary_index(&self) -> NodeIndex {
        match self {
            Self::Simple(simple) => simple.primary_index,
            Self::Slice(slice) => slice.primary_index,
            Self::Slices(slices) => slices.primary_index,
        }
    }

    pub fn as_args<'a>(&'a self) -> SliceArguments<'db, 'a> {
        SliceArguments(self)
    }
}

#[derive(Debug, Copy, Clone)]
pub struct Simple<'db> {
    pub file: &'db PythonFile,
    pub primary_index: NodeIndex,
    pub named_expr: NamedExpression<'db>,
}

impl<'db> Simple<'db> {
    pub fn infer(&self, i_s: &mut InferenceState<'db, '_>) -> Inferred<'db> {
        self.file
            .inference(i_s)
            .infer_named_expression(self.named_expr)
    }

    pub fn infer_annotation_class(&self, i_s: &mut InferenceState<'db, '_>) -> Inferred<'db> {
        self.file
            .inference(i_s)
            .infer_annotation_expression_class(self.named_expr.expression())
    }
}

#[derive(Debug, Copy, Clone)]
pub struct Slice<'db> {
    file: &'db PythonFile,
    primary_index: NodeIndex,
    slice: ASTSlice<'db>,
}

#[derive(Debug, Copy, Clone)]
pub struct Slices<'db> {
    file: &'db PythonFile,
    primary_index: NodeIndex,
    slices: ASTSlices<'db>,
}

impl<'db> Slices<'db> {
    pub fn iter(&self) -> SliceIterator<'db> {
        SliceIterator(self.file, self.primary_index, self.slices.iter())
    }
}

pub enum SliceOrSimple<'db> {
    Simple(Simple<'db>),
    Slice(Slice<'db>),
}

impl<'db> SliceOrSimple<'db> {
    pub fn infer_annotation_class(&self, i_s: &mut InferenceState<'db, '_>) -> Inferred<'db> {
        match self {
            Self::Simple(simple) => simple.infer_annotation_class(i_s),
            Self::Slice(slice) => todo!(),
        }
    }
}

pub struct SliceIterator<'db>(&'db PythonFile, NodeIndex, ASTSliceIterator<'db>);

impl<'db> Iterator for SliceIterator<'db> {
    type Item = SliceOrSimple<'db>;

    fn next(&mut self) -> Option<Self::Item> {
        // TODO it's actually a bad idea to pass primary_index here
        self.2.next().map(|content| match content {
            SliceContent::NamedExpression(n) => SliceOrSimple::Simple(Simple {
                file: self.0,
                primary_index: self.1,
                named_expr: n,
            }),
            SliceContent::Slice(s) => SliceOrSimple::Slice(Slice {
                file: self.0,
                primary_index: self.1,
                slice: s,
            }),
        })
    }
}

impl<'db> SliceIterator<'db> {}

#[derive(Debug)]
pub struct SliceArguments<'db, 'a>(&'a SliceType<'db>);

impl<'db> Arguments<'db> for SliceArguments<'db, '_> {
    fn iter_arguments(&self) -> ArgumentIterator<'db, '_> {
        ArgumentIterator::SliceType(*self.0)
    }

    fn outer_execution(&self) -> Option<&Execution> {
        todo!()
    }

    fn as_execution(&self, function: &Function) -> Execution {
        /*
        Execution::new(
            function.as_point_link(),
            PointLink::new(self.file.file_index(), self.primary_node.index()),
            self.in_,
        )
        */
        todo!()
    }

    fn type_(&self) -> ArgumentsType<'db> {
        /*
        match {
            ArgumentsType::Normal(self.file, self.primary_node)
        }
        */
        todo!()
    }
}
