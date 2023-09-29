use std::rc::Rc;

use crate::database::{DbType, TupleContent, TupleTypeArguments, TypeOrTypeVarTuple};
use crate::debug;
use crate::diagnostics::IssueType;
use crate::file::infer_index;
use crate::getitem::{SliceType, SliceTypeContent};
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::matching::{IteratorContent, LookupResult, ResultContext};
use crate::node_ref::NodeRef;
use crate::type_helpers::Instance;

#[derive(Debug, Clone, Copy)]
pub struct Tuple<'a> {
    content: &'a Rc<TupleContent>,
}

impl<'a> Tuple<'a> {
    pub fn new(content: &'a Rc<TupleContent>) -> Self {
        Self { content }
    }

    pub fn iter(&self, i_s: &InferenceState, from: NodeRef) -> IteratorContent {
        match &self.content.args {
            Some(args @ TupleTypeArguments::FixedLength(ts)) => {
                if args.has_type_var_tuple().is_some() {
                    todo!()
                } else {
                    IteratorContent::new_tuple(ts.clone())
                }
            }
            Some(TupleTypeArguments::ArbitraryLength(t)) => {
                IteratorContent::Inferred(Inferred::from_type(t.as_ref().clone()))
            }
            None => todo!(),
        }
    }

    pub fn lookup(&self, i_s: &InferenceState, node_ref: NodeRef, name: &str) -> LookupResult {
        let tuple_cls = i_s.db.python_state.tuple_class(i_s.db, self.content);
        let tuple_instance = Instance::new(tuple_cls, None);
        for (mro_index, class_or_type) in tuple_cls.mro(i_s.db) {
            let (cls, lookup) = class_or_type.lookup_symbol(i_s, name);
            let result = lookup.and_then(|inf| {
                let Some(cls) = cls else {
                    unreachable!();
                };
                inf.bind_instance_descriptors(
                    i_s,
                    tuple_cls.as_db_type(i_s.db),
                    cls,
                    node_ref,
                    mro_index,
                )
            });
            match result {
                Some(LookupResult::None) => (),
                None => return LookupResult::None,
                Some(x) => return x,
            }
        }
        debug!("TODO tuple object lookups");
        LookupResult::None
    }

    pub fn get_item(
        &self,
        i_s: &InferenceState,
        slice_type: &SliceType,
        result_context: &mut ResultContext,
    ) -> Inferred {
        match &self.content.args {
            Some(args @ TupleTypeArguments::FixedLength(ts)) => match slice_type.unpack() {
                SliceTypeContent::Simple(simple) => {
                    if args.has_type_var_tuple().is_some() {
                        todo!()
                    }
                    infer_index(i_s, simple.file, simple.named_expr.expression(), |index| {
                        let index = if index < 0 {
                            let index = ts.len() as isize + index;
                            index.try_into().map_err(|_| todo!()).ok()?
                        } else {
                            index as usize
                        };
                        if let Some(t) = ts.as_ref().get(index) {
                            Some(match t {
                                TypeOrTypeVarTuple::Type(t) => {
                                    Inferred::execute_db_type(i_s, t.clone())
                                }
                                TypeOrTypeVarTuple::TypeVarTuple(t) => unreachable!(),
                            })
                        } else {
                            slice_type
                                .as_node_ref()
                                .add_issue(i_s, IssueType::TupleIndexOutOfRange);
                            None
                        }
                    })
                    .unwrap_or_else(Inferred::new_any)
                }
                SliceTypeContent::Slice(slice) => slice
                    .callback_on_tuple_indexes(i_s, ts, |start, end, step| {
                        Inferred::from_type(DbType::Tuple(Rc::new(TupleContent::new_fixed_length(
                            if step < 0 { todo!() } else { ts.clone() },
                        ))))
                    })
                    .unwrap_or_else(|| todo!()),
                SliceTypeContent::Slices(slices) => {
                    todo!()
                }
            },
            Some(TupleTypeArguments::ArbitraryLength(t)) => {
                Inferred::execute_db_type(i_s, t.as_ref().clone())
            }
            _ => Inferred::new_unknown(),
        }
    }
}
