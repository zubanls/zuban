use parsa_python::{NonterminalType, PyNode, PyNodeType::Nonterminal};

use crate::file::PythonFile;
use crate::inference_state::InferenceState;
use crate::inferred::{Inferred, NodeReference};

pub enum SliceType<'db> {
    Simple(Simple<'db>),
    Slice(Slice<'db>),
    Slices(Slices<'db>),
}

impl<'db> SliceType<'db> {
    pub fn new(f: &'db PythonFile, node: PyNode<'db>) -> Self {
        use NonterminalType::*;
        if node.is_type(Nonterminal(named_expression)) {
            Self::Simple(Simple(NodeReference { file: f, node }))
        } else if node.is_type(Nonterminal(slice)) {
            Self::Slice(Slice(NodeReference { file: f, node }))
        } else {
            debug_assert_eq!(node.get_type(), Nonterminal(slices));
            Self::Slices(Slices(NodeReference { file: f, node }))
        }
    }
}

pub struct Simple<'db>(NodeReference<'db>);

impl<'db> Simple<'db> {
    pub fn infer(&self, i_s: &mut InferenceState<'db, '_>) -> Inferred<'db> {
        self.0
            .file
            .get_inference(i_s)
            .infer_named_expression(self.0.node)
    }
}

pub struct Slice<'db>(NodeReference<'db>);

pub struct Slices<'db>(NodeReference<'db>);
