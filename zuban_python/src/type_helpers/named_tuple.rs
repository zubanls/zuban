use std::rc::Rc;

use crate::database::{DbType, FormatStyle, NamedTuple, RecursiveAlias, TupleTypeArguments};
use crate::debug;
use crate::diagnostics::IssueType;
use crate::file::infer_index;
use crate::getitem::{SliceType, SliceTypeContent};
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::matching::{FormatData, Generics, IteratorContent, LookupResult, ResultContext, Type};
use crate::{database::Database, node_ref::NodeRef};

#[derive(Debug)]
pub struct NamedTupleValue<'a> {
    pub db: &'a Database,
    pub nt: &'a Rc<NamedTuple>,
}

impl<'a> NamedTupleValue<'a> {
    pub fn new(db: &'a Database, nt: &'a Rc<NamedTuple>) -> Self {
        Self { db, nt }
    }

    pub fn format_with_name(
        &self,
        format_data: &FormatData,
        name: &str,
        generics: Generics,
    ) -> Box<str> {
        if format_data.style != FormatStyle::MypyRevealType {
            return Box::from(name);
        }
        let params = self.nt.params();
        // We need to check recursions here, because for class definitions of named tuples can
        // recurse with their attributes.
        let rec = RecursiveAlias::new(self.nt.__new__.defined_at, None);
        if format_data.has_already_seen_recursive_alias(&rec) {
            return Box::from(name);
        }
        let format_data = &format_data.with_seen_recursive_alias(&rec);
        let types = params
            .iter()
            .map(|p| {
                let t = p.param_specific.expect_positional_db_type_as_ref();
                match generics {
                    Generics::NotDefinedYet | Generics::None => t.format(format_data),
                    _ => Type::new(t)
                        .replace_type_var_likes_and_self(
                            format_data.db,
                            &mut |usage| {
                                generics
                                    .nth_usage(format_data.db, &usage)
                                    .into_generic_item(format_data.db)
                            },
                            &mut || todo!(),
                        )
                        .format(format_data),
                }
            })
            .collect::<Vec<_>>()
            .join(", ");
        format!("tuple[{types}, fallback={name}]",).into()
    }

    pub fn iter(&self, i_s: &InferenceState<'a, '_>, from: NodeRef) -> IteratorContent<'a> {
        let TupleTypeArguments::FixedLength(t) = self.nt.as_tuple().args.as_ref().unwrap() else {
            unreachable!()
        };
        IteratorContent::FixedLengthTupleGenerics(t.iter())
    }

    pub fn lookup(
        &self,
        i_s: &InferenceState,
        node_ref: Option<NodeRef>,
        name: &str,
    ) -> LookupResult {
        for p in self.nt.params() {
            if name == p.name.unwrap().as_str(i_s.db) {
                return LookupResult::UnknownName(Inferred::from_type(
                    p.param_specific.expect_positional_db_type_as_ref().clone(),
                ));
            }
        }
        if name == "__new__" {
            return LookupResult::UnknownName(Inferred::from_type(DbType::Callable(
                self.nt.__new__.clone(),
            )));
        }
        debug!("TODO lookup of NamedTuple base classes");
        LookupResult::None
    }

    pub fn get_item(
        &self,
        i_s: &InferenceState,
        slice_type: &SliceType,
        result_context: &mut ResultContext,
    ) -> Inferred {
        match slice_type.unpack() {
            SliceTypeContent::Simple(simple) => infer_index(i_s, simple, |index| {
                if let Some(p) = self.nt.params().get(index) {
                    Some(Inferred::from_type(
                        p.param_specific.expect_positional_db_type_as_ref().clone(),
                    ))
                } else {
                    slice_type
                        .as_node_ref()
                        .add_issue(i_s, IssueType::TupleIndexOutOfRange);
                    None
                }
            }),
            SliceTypeContent::Slice(_) => todo!(),
            SliceTypeContent::Slices(_) => todo!(),
        }
    }
}
