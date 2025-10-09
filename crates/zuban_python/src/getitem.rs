use num_bigint::BigInt;
use parsa_python_cst::{
    NamedExpression, NodeIndex, Slice as CSTSlice, SliceContent, SliceIterator as CSTSliceIterator,
    SliceType as CSTSliceType, Slices as CSTSlices, StarredExpression,
};

use crate::{
    arguments::{ArgIterator, Args},
    database::{Database, PointsBackup},
    diagnostics::IssueKind,
    file::{PythonFile, infer_index},
    inference_state::{InferenceState, Mode},
    inferred::Inferred,
    matching::ResultContext,
    new_class,
    node_ref::NodeRef,
    type_::{Tuple, Type},
};

#[derive(Debug, Copy, Clone)]
pub(crate) struct SliceType<'file> {
    pub file: &'file PythonFile,
    pub cst_node: CSTSliceType<'file>,
    node_index: NodeIndex,
}

pub(crate) enum SliceTypeContent<'file> {
    Simple(Simple<'file>),
    Starred(Starred<'file>),
    Slice(Slice<'file>),
    Slices(Slices<'file>),
}

impl<'db, 'file> SliceType<'file> {
    pub fn new(
        file: &'file PythonFile,
        node_index: NodeIndex,
        cst_node: CSTSliceType<'file>,
    ) -> Self {
        Self {
            file,
            cst_node,
            node_index,
        }
    }

    pub fn to_db_lifetime(self, _: &'db Database) -> SliceType<'db> {
        // This should be safe, because all files are added to the database.
        unsafe { std::mem::transmute(self) }
    }

    pub fn as_node_ref(&self) -> NodeRef<'file> {
        NodeRef::new(self.file, self.node_index)
    }

    pub fn as_argument_node_ref(&self) -> NodeRef<'file> {
        NodeRef::new(self.file, self.cst_node.index())
    }

    pub fn as_args<'x>(&'x self, i_s: InferenceState<'db, 'x>) -> SliceArguments<'db, 'x> {
        SliceArguments {
            slice_type: self,
            i_s,
        }
    }

    pub fn unpack(&self) -> SliceTypeContent<'file> {
        match self.cst_node {
            CSTSliceType::NamedExpression(named_expr) => SliceTypeContent::Simple(Simple {
                file: self.file,
                named_expr,
            }),
            CSTSliceType::Slice(slice) => SliceTypeContent::Slice(Slice {
                file: self.file,
                slice,
            }),
            CSTSliceType::Slices(slices) => SliceTypeContent::Slices(Slices {
                file: self.file,
                slices,
            }),
            CSTSliceType::StarredExpression(starred_expr) => SliceTypeContent::Starred(Starred {
                file: self.file,
                starred_expr,
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
            SliceTypeContent::Starred(s) => {
                SliceTypeIterator::SliceOrSimple(SliceOrSimple::Starred(s))
            }
        }
    }

    pub(crate) fn infer(&self, i_s: &InferenceState) -> Inferred {
        self.infer_with_context(i_s, &mut ResultContext::Unknown)
    }

    pub(crate) fn infer_with_context(
        &self,
        i_s: &InferenceState,
        result_context: &mut ResultContext,
    ) -> Inferred {
        match self.unpack() {
            SliceTypeContent::Simple(s) => s.infer(i_s, result_context),
            SliceTypeContent::Slice(s) => s.infer(i_s),
            SliceTypeContent::Slices(s) => s.infer(i_s),
            SliceTypeContent::Starred(s) => s.infer(i_s),
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub(crate) struct Simple<'file> {
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
pub(crate) struct Starred<'file> {
    pub file: &'file PythonFile,
    pub starred_expr: StarredExpression<'file>,
}

impl<'file> Starred<'file> {
    pub fn as_node_ref(&self) -> NodeRef<'file> {
        NodeRef::new(self.file, self.starred_expr.index())
    }

    fn infer(&self, i_s: &InferenceState) -> Inferred {
        self.file
            .inference(i_s)
            .infer_expression(self.starred_expr.expression());
        Inferred::new_object(i_s.db)
    }
}

#[derive(Debug, Copy, Clone)]
pub(crate) struct Slice<'file> {
    file: &'file PythonFile,
    slice: CSTSlice<'file>,
}

impl<'file> Slice<'file> {
    pub fn as_node_ref(&self) -> NodeRef<'file> {
        NodeRef::new(self.file, self.slice.index())
    }

    pub fn infer(&self, i_s: &InferenceState) -> Inferred {
        let check = |maybe_expr| {
            if let Some(expr) = maybe_expr {
                let inf = self.file.inference(i_s).infer_expression(expr);
                let t = inf.as_cow_type(i_s);
                let supports_index = i_s.db.python_state.supports_index_type();
                if t.iter_with_unpacked_unions(i_s.db).any(|t| {
                    !t.is_simple_sub_type_of(i_s, &supports_index).bool()
                        && !t.is_simple_sub_type_of(i_s, &Type::None).bool()
                }) {
                    NodeRef::new(self.file, expr.index())
                        .add_issue(i_s, IssueKind::InvalidSliceIndex);
                    Type::ERROR
                } else {
                    t.into_owned()
                }
            } else {
                Type::None
            }
        };

        let (first, second, third) = self.slice.unpack();

        Inferred::from_type(new_class!(
            i_s.db.python_state.slice_link(),
            check(first),
            check(second),
            check(third),
        ))
    }

    pub fn callback_on_tuple_indexes(
        &self,
        i_s: &InferenceState,
        callback: impl Fn(Option<&BigInt>, Option<&BigInt>, &BigInt) -> Inferred,
    ) -> Option<Inferred> {
        let (first, second, third) = self.slice.unpack();
        let infer_third = |start_index: Option<&BigInt>, end_index: Option<&BigInt>| {
            if let Some(third) = third {
                // TODO index is not type checked :(
                infer_index(i_s, self.file, third, |step_index| {
                    Some(callback(start_index, end_index, step_index))
                })
            } else {
                // 1 is the default step size
                Some(callback(start_index, end_index, &1.into()))
            }
        };
        let infer_second = |start_index: Option<&BigInt>| {
            if let Some(second) = second {
                infer_index(i_s, self.file, second, |index| {
                    infer_third(start_index, Some(index))
                })
            } else {
                infer_third(start_index, None)
            }
        };
        if let Some(first) = first {
            infer_index(i_s, self.file, first, |index| infer_second(Some(index)))
        } else {
            infer_second(None)
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub(crate) struct Slices<'file> {
    pub file: &'file PythonFile,
    slices: CSTSlices<'file>,
}

impl<'file> Slices<'file> {
    pub fn iter(&self) -> SliceIterator<'file> {
        SliceIterator(self.file, self.slices.iter())
    }

    pub fn infer(&self, i_s: &InferenceState) -> Inferred {
        let parts = self
            .iter()
            .map(|x| x.infer(i_s, &mut ResultContext::Unknown).as_type(i_s))
            .collect();
        Inferred::from_type(Type::Tuple(Tuple::new_fixed_length(parts)))
    }
}

#[derive(Copy, Clone)]
pub(crate) enum SliceOrSimple<'file> {
    Simple(Simple<'file>),
    Slice(Slice<'file>),
    Starred(Starred<'file>),
}

impl<'file> SliceOrSimple<'file> {
    pub fn infer(&self, i_s: &InferenceState, result_context: &mut ResultContext) -> Inferred {
        match self {
            Self::Simple(simple) => simple.infer(i_s, result_context),
            Self::Slice(slice) => slice.infer(i_s),
            SliceOrSimple::Starred(starred) => starred.infer(i_s),
        }
    }

    pub fn as_node_ref(&self) -> NodeRef<'file> {
        match self {
            SliceOrSimple::Simple(simple) => simple.as_node_ref(),
            SliceOrSimple::Slice(slice) => slice.as_node_ref(),
            SliceOrSimple::Starred(starred) => starred.as_node_ref(),
        }
    }
}

#[derive(Clone)]
pub(crate) struct SliceIterator<'file>(&'file PythonFile, CSTSliceIterator<'file>);

impl<'file> Iterator for SliceIterator<'file> {
    type Item = SliceOrSimple<'file>;

    fn next(&mut self) -> Option<Self::Item> {
        // TODO it's actually a bad idea to pass node_index here
        self.1.next().map(|content| match content {
            SliceContent::NamedExpression(n) => SliceOrSimple::Simple(Simple {
                file: self.0,
                named_expr: n,
            }),
            SliceContent::StarredExpression(s) => SliceOrSimple::Starred(Starred {
                file: self.0,
                starred_expr: s,
            }),
            SliceContent::Slice(s) => SliceOrSimple::Slice(Slice {
                file: self.0,
                slice: s,
            }),
        })
    }
}

#[derive(Clone)]
pub(crate) enum SliceTypeIterator<'file> {
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
pub(crate) struct SliceArguments<'db, 'a> {
    slice_type: &'a SliceType<'a>,
    i_s: InferenceState<'db, 'a>,
}

impl<'db> Args<'db> for SliceArguments<'db, '_> {
    fn iter<'x>(&'x self, mode: Mode<'x>) -> ArgIterator<'db, 'x> {
        ArgIterator::new_slice(*self.slice_type, self.i_s.with_mode(mode))
    }

    fn calculate_diagnostics_for_any_callable(&self) {
        self.slice_type.infer(&self.i_s);
    }

    fn as_node_ref_internal(&self) -> Option<NodeRef<'_>> {
        Some(self.slice_type.as_argument_node_ref())
    }

    fn points_backup(&self) -> Option<PointsBackup> {
        let end = self.slice_type.cst_node.last_leaf_index();
        Some(
            self.slice_type
                .file
                .points
                .backup(self.slice_type.node_index..end + 1),
        )
    }

    fn reset_points_from_backup(&self, backup: &Option<PointsBackup>) {
        self.slice_type
            .file
            .points
            .reset_from_backup(backup.as_ref().unwrap());
    }
}
