use std::rc::Rc;

use parsa_python_ast::{
    NamedExpression, NodeIndex, Slice as ASTSlice, SliceContent, SliceIterator as ASTSliceIterator,
    SliceType as ASTSliceType, Slices as ASTSlices,
};

use crate::arguments::{ArgumentIterator, Arguments, ArgumentsType};
use crate::database::{Database, DbType, TupleContent, TypeOrTypeVarTuple};
use crate::debug;
use crate::file::PythonFile;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::matching::ResultContext;
use crate::node_ref::NodeRef;

#[derive(Debug, Copy, Clone)]
pub struct SliceType<'file> {
    pub file: &'file PythonFile,
    pub ast_node: ASTSliceType<'file>,
    node_index: NodeIndex,
}

pub enum SliceTypeContent<'file> {
    Simple(Simple<'file>),
    Slice(Slice<'file>),
    Slices(Slices<'file>),
}

impl<'db, 'file> SliceType<'file> {
    pub fn new(
        file: &'file PythonFile,
        node_index: NodeIndex,
        ast_node: ASTSliceType<'file>,
    ) -> Self {
        Self {
            file,
            ast_node,
            node_index,
        }
    }

    pub fn as_node_ref(&self) -> NodeRef<'file> {
        NodeRef::new(self.file, self.node_index)
    }

    pub fn as_args<'x>(&'x self, i_s: InferenceState<'db, 'x>) -> SliceArguments<'db, 'x> {
        SliceArguments {
            slice_type: self,
            i_s,
        }
    }

    pub fn unpack(&self) -> SliceTypeContent<'file> {
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

    pub fn iter(&self) -> SliceTypeIterator<'file> {
        match self.unpack() {
            SliceTypeContent::Simple(s) => {
                SliceTypeIterator::SliceOrSimple(SliceOrSimple::Simple(s))
            }
            SliceTypeContent::Slice(s) => SliceTypeIterator::SliceOrSimple(SliceOrSimple::Slice(s)),
            SliceTypeContent::Slices(s) => SliceTypeIterator::SliceIterator(s.iter()),
        }
    }

    pub(crate) fn infer(&self, i_s: &InferenceState) -> Inferred {
        match self.unpack() {
            SliceTypeContent::Simple(s) => s.infer(i_s, &mut ResultContext::Unknown),
            SliceTypeContent::Slice(s) => s.infer(i_s.db),
            SliceTypeContent::Slices(s) => s.infer(i_s),
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub struct Simple<'file> {
    pub file: &'file PythonFile,
    pub named_expr: NamedExpression<'file>,
}

impl<'file> Simple<'file> {
    pub fn infer(&self, i_s: &InferenceState, result_context: &mut ResultContext) -> Inferred {
        self.file
            .inference(i_s)
            .infer_named_expression_with_context(self.named_expr, result_context)
    }

    pub fn as_node_ref(&self) -> NodeRef<'file> {
        NodeRef::new(self.file, self.named_expr.index())
    }
}

#[derive(Debug, Copy, Clone)]
pub struct Slice<'file> {
    file: &'file PythonFile,
    slice: ASTSlice<'file>,
}

impl<'file> Slice<'file> {
    pub fn as_node_ref(&self) -> NodeRef<'file> {
        NodeRef::new(self.file, self.slice.index())
    }

    pub fn infer(&self, db: &Database) -> Inferred {
        Inferred::from_type(db.python_state.slice_db_type())
    }
}

#[derive(Debug, Copy, Clone)]
pub struct Slices<'file> {
    pub file: &'file PythonFile,
    slices: ASTSlices<'file>,
}

impl<'file> Slices<'file> {
    pub fn as_node_ref(&self) -> NodeRef<'file> {
        NodeRef::new(self.file, self.slices.index())
    }

    pub fn iter(&self) -> SliceIterator<'file> {
        SliceIterator(self.file, self.slices.iter())
    }

    pub fn infer(&self, i_s: &InferenceState) -> Inferred {
        let parts = self
            .iter()
            .map(|x| {
                TypeOrTypeVarTuple::Type(x.infer(i_s, &mut ResultContext::Unknown).as_db_type(i_s))
            })
            .collect();
        Inferred::from_type(DbType::Tuple(Rc::new(TupleContent::new_fixed_length(
            parts,
        ))))
    }
}

#[derive(Copy, Clone)]
pub enum SliceOrSimple<'file> {
    Simple(Simple<'file>),
    Slice(Slice<'file>),
}

impl<'file> SliceOrSimple<'file> {
    pub fn infer(&self, i_s: &InferenceState, result_context: &mut ResultContext) -> Inferred {
        match self {
            Self::Simple(simple) => simple.infer(i_s, result_context),
            Self::Slice(slice) => todo!(),
        }
    }

    pub fn as_node_ref(&self) -> NodeRef<'file> {
        match self {
            SliceOrSimple::Simple(simple) => simple.as_node_ref(),
            SliceOrSimple::Slice(slice) => slice.as_node_ref(),
        }
    }
}

pub struct SliceIterator<'file>(&'file PythonFile, ASTSliceIterator<'file>);

impl<'file> Iterator for SliceIterator<'file> {
    type Item = SliceOrSimple<'file>;

    fn next(&mut self) -> Option<Self::Item> {
        // TODO it's actually a bad idea to pass node_index here
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

pub enum SliceTypeIterator<'file> {
    SliceIterator(SliceIterator<'file>),
    SliceOrSimple(SliceOrSimple<'file>),
    Finished,
}

impl<'file> Iterator for SliceTypeIterator<'file> {
    type Item = SliceOrSimple<'file>;

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
pub struct SliceArguments<'db, 'a> {
    slice_type: &'a SliceType<'a>,
    i_s: InferenceState<'db, 'a>,
}

impl<'db> Arguments<'db> for SliceArguments<'db, '_> {
    fn iter(&self) -> ArgumentIterator<'db, '_> {
        ArgumentIterator::new_slice(*self.slice_type, self.i_s)
    }

    fn type_(&self) -> ArgumentsType {
        /*
        match {
            ArgumentsType::Normal(self.file, self.primary_node)
        }
        */
        todo!()
    }

    fn as_node_ref(&self) -> NodeRef {
        self.slice_type.as_node_ref()
    }

    fn reset_cache(&self) {
        debug!("TODO implement reset_cache for SliceArguments");
    }
}
