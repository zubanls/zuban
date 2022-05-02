use parsa_python_ast::{
    NamedExpression, NodeIndex, Slice as ASTSlice, SliceContent, SliceIterator as ASTSliceIterator,
    SliceType as ASTSliceType, Slices as ASTSlices,
};

use crate::arguments::{ArgumentIterator, Arguments, ArgumentsType};
use crate::database::Execution;
use crate::file::PythonFile;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::node_ref::NodeRef;
use crate::value::Function;

#[derive(Debug, Copy, Clone)]
pub struct SliceType<'db> {
    pub file: &'db PythonFile,
    pub ast_node: ASTSliceType<'db>,
    pub primary_index: NodeIndex,
}

pub enum SliceTypeContent<'db> {
    Simple(Simple<'db>),
    Slice(Slice<'db>),
    Slices(Slices<'db>),
}

impl<'db> SliceType<'db> {
    pub fn new(
        file: &'db PythonFile,
        primary_index: NodeIndex,
        ast_node: ASTSliceType<'db>,
    ) -> Self {
        Self {
            file,
            ast_node,
            primary_index,
        }
    }

    pub fn as_node_ref(&self) -> NodeRef<'db> {
        NodeRef::new(self.file, self.primary_index)
    }

    pub fn as_args<'a>(&'a self) -> SliceArguments<'db, 'a> {
        SliceArguments(self)
    }

    pub fn unpack(&self) -> SliceTypeContent<'db> {
        match self.ast_node {
            ASTSliceType::NamedExpression(named_expr) => SliceTypeContent::Simple(Simple {
                file: self.file,
                named_expr,
            }),
            ASTSliceType::Slice(slice) => SliceTypeContent::Slice(Slice {
                file: self.file,
                slice,
            }),
            ASTSliceType::Slices(slices) => SliceTypeContent::Slices(Slices {
                file: self.file,
                slices,
            }),
        }
    }

    pub fn iter(&self) -> SliceTypeIterator<'db> {
        match self.unpack() {
            SliceTypeContent::Simple(s) => {
                SliceTypeIterator::SliceOrSimple(SliceOrSimple::Simple(s))
            }
            SliceTypeContent::Slice(s) => SliceTypeIterator::SliceOrSimple(SliceOrSimple::Slice(s)),
            SliceTypeContent::Slices(s) => SliceTypeIterator::SliceIterator(s.iter()),
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub struct Simple<'db> {
    pub file: &'db PythonFile,
    pub named_expr: NamedExpression<'db>,
}

impl<'db> Simple<'db> {
    pub fn infer(&self, i_s: &mut InferenceState<'db, '_>) -> Inferred<'db> {
        self.file
            .inference(i_s)
            .infer_named_expression(self.named_expr)
    }

    pub fn as_node_ref(&self) -> NodeRef<'db> {
        NodeRef::new(self.file, self.named_expr.index())
    }
}

#[derive(Debug, Copy, Clone)]
pub struct Slice<'db> {
    file: &'db PythonFile,
    slice: ASTSlice<'db>,
}

impl<'db> Slice<'db> {
    pub fn as_node_ref(&self) -> NodeRef<'db> {
        NodeRef::new(self.file, self.slice.index())
    }
}

#[derive(Debug, Copy, Clone)]
pub struct Slices<'db> {
    pub file: &'db PythonFile,
    slices: ASTSlices<'db>,
}

impl<'db> Slices<'db> {
    pub fn iter(&self) -> SliceIterator<'db> {
        SliceIterator(self.file, self.slices.iter())
    }
}

#[derive(Copy, Clone)]
pub enum SliceOrSimple<'db> {
    Simple(Simple<'db>),
    Slice(Slice<'db>),
}

impl<'db> SliceOrSimple<'db> {
    pub fn infer(&self, i_s: &mut InferenceState<'db, '_>) -> Inferred<'db> {
        match self {
            Self::Simple(simple) => simple.infer(i_s),
            Self::Slice(slice) => todo!(),
        }
    }

    pub fn as_node_ref(&self) -> NodeRef<'db> {
        match self {
            SliceOrSimple::Simple(simple) => simple.as_node_ref(),
            SliceOrSimple::Slice(slice) => slice.as_node_ref(),
        }
    }
}

pub struct SliceIterator<'db>(&'db PythonFile, ASTSliceIterator<'db>);

impl<'db> Iterator for SliceIterator<'db> {
    type Item = SliceOrSimple<'db>;

    fn next(&mut self) -> Option<Self::Item> {
        // TODO it's actually a bad idea to pass primary_index here
        self.1.next().map(|content| match content {
            SliceContent::NamedExpression(n) => SliceOrSimple::Simple(Simple {
                file: self.0,
                named_expr: n,
            }),
            SliceContent::Slice(s) => SliceOrSimple::Slice(Slice {
                file: self.0,
                slice: s,
            }),
        })
    }
}

pub enum SliceTypeIterator<'db> {
    SliceIterator(SliceIterator<'db>),
    SliceOrSimple(SliceOrSimple<'db>),
    Finished,
}

impl<'db> Iterator for SliceTypeIterator<'db> {
    type Item = SliceOrSimple<'db>;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::SliceIterator(s) => s.next(),
            Self::SliceOrSimple(_) => {
                let result = std::mem::replace(self, Self::Finished);
                if let Self::SliceOrSimple(s) = result {
                    Some(s)
                } else {
                    unreachable!()
                }
            }
            Self::Finished => None,
        }
    }
}

#[derive(Debug)]
pub struct SliceArguments<'db, 'a>(&'a SliceType<'db>);

impl<'db> Arguments<'db> for SliceArguments<'db, '_> {
    fn iter_arguments(&self) -> ArgumentIterator<'db, '_> {
        ArgumentIterator::SliceType(*self.0)
    }

    fn outer_execution(&self) -> Option<&Execution> {
        todo!()
    }

    fn as_execution(&self, function: &Function) -> Option<Execution> {
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

    fn node_reference(&self) -> NodeRef<'db> {
        self.0.as_node_ref()
    }
}
