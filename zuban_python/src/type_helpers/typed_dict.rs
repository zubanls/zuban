use std::rc::Rc;

use parsa_python_ast::{AtomContent, DictElement, ExpressionContent, ExpressionPart};

use crate::{
    arguments::{ArgumentKind, Arguments},
    database::{ComplexPoint, CustomBehavior, DbType, StringSlice, TypedDict, TypedDictMember},
    diagnostics::IssueType,
    file::{infer_string_index, TypeComputation, TypeComputationOrigin, TypeVarCallbackReturn},
    getitem::{SliceType, SliceTypeContent},
    inference_state::InferenceState,
    inferred::Inferred,
    matching::{FormatData, LookupKind, LookupResult, Matcher, OnTypeError, ResultContext, Type},
    node_ref::NodeRef,
};

use super::Instance;

pub struct TypedDictHelper<'a>(pub &'a Rc<TypedDict>);
impl<'a> TypedDictHelper<'a> {
    pub fn initialize<'db>(
        &self,
        i_s: &InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError<'db, '_>,
    ) -> Inferred {
        let mut iterator = args.iter();
        if let Some(first_arg) = iterator.next().filter(|arg| !arg.is_keyword_argument()) {
            if iterator.next().is_some() {
                todo!()
            }
            let t = Type::owned(DbType::TypedDict(self.0.clone()));
            first_arg.infer(i_s, &mut ResultContext::Known(&t));
        } else {
            args.as_node_ref()
                .file
                .inference(i_s)
                .check_typed_dict_call_with_context(&mut Matcher::default(), self.0.clone(), args);
        }
        Inferred::from_type(DbType::TypedDict(self.0.clone()))
    }

    pub fn get_item(
        &self,
        i_s: &InferenceState,
        slice_type: &SliceType,
        result_context: &mut ResultContext,
    ) -> Inferred {
        match slice_type.unpack() {
            SliceTypeContent::Simple(simple) => infer_string_index(
                i_s,
                simple,
                |name| {
                    Some({
                        if let Some(member) = self.0.find_member(i_s.db, name) {
                            Inferred::from_type(member.type_.clone())
                        } else {
                            Inferred::new_any()
                        }
                    })
                },
                || self.add_access_key_must_be_string_literal_issue(i_s, slice_type.as_node_ref()),
            ),
            SliceTypeContent::Slice(_) => todo!(),
            SliceTypeContent::Slices(_) => todo!(),
        }
    }

    pub fn lookup(
        &self,
        i_s: &InferenceState,
        from: NodeRef,
        name: &str,
        kind: LookupKind,
    ) -> LookupResult {
        LookupResult::UnknownName(Inferred::from_type(DbType::CustomBehavior(match name {
            "get" | "pop" => {
                let bound = Rc::new(DbType::TypedDict(self.0.clone()));
                CustomBehavior::new_method(typed_dict_get, Some(bound))
            }
            "__delitem__" => {
                let bound = Rc::new(DbType::TypedDict(self.0.clone()));
                CustomBehavior::new_method(typed_dict_delitem, Some(bound))
            }
            "update" => {
                let bound = Rc::new(DbType::TypedDict(self.0.clone()));
                CustomBehavior::new_method(typed_dict_update, Some(bound))
            }
            _ => {
                return Instance::new(i_s.db.python_state.typed_dict_class(), None)
                    .lookup(i_s, from, name, kind)
            }
        })))
    }

    pub fn add_access_key_must_be_string_literal_issue(
        &self,
        i_s: &InferenceState,
        node_ref: NodeRef,
    ) {
        node_ref.add_issue(
            i_s,
            IssueType::TypedDictAccessKeyMustBeStringLiteral {
                keys: self
                    .0
                    .members
                    .iter()
                    .map(|member| format!("\"{}\"", member.name.as_str(i_s.db)))
                    .collect::<Vec<String>>()
                    .join(", ")
                    .into(),
            },
        )
    }
}

pub fn new_typed_dict<'db>(i_s: &InferenceState<'db, '_>, args: &dyn Arguments<'db>) -> Inferred {
    new_typed_dict_internal(i_s, args).unwrap_or_else(|| Inferred::new_any())
}

fn new_typed_dict_internal<'db>(
    i_s: &InferenceState<'db, '_>,
    args: &dyn Arguments<'db>,
) -> Option<Inferred> {
    let mut iterator = args.iter();
    let Some(first_arg) = iterator.next() else {
        todo!()
    };
    let ArgumentKind::Positional { node_ref, .. } = first_arg.kind else {
        args.as_node_ref()
            .add_issue(i_s, IssueType::UnexpectedArgumentsToTypedDict);
        return None
    };
    let expr = node_ref.as_named_expression().expression();
    let Some(name) = StringSlice::from_string_in_expression(node_ref.file_index(), expr) else {
        node_ref.add_issue(i_s, IssueType::TypedDictFirstArgMustBeString);
        return None
    };

    if let Some(definition_name) = expr
        .maybe_single_string_literal()
        .unwrap()
        .in_simple_assignment()
    {
        let name = name.as_str(i_s.db);
        if name != definition_name.as_code() {
            node_ref.add_issue(
                i_s,
                IssueType::TypedDictNameMismatch {
                    string_name: Box::from(name),
                    variable_name: Box::from(definition_name.as_code()),
                },
            );
        }
    } else {
        todo!()
    }

    let Some(second_arg) = iterator.next() else {
        args.as_node_ref().add_issue(i_s, IssueType::TooFewArguments(" for TypedDict()".into()));
        return None
    };
    let ArgumentKind::Positional { node_ref: second_node_ref, .. } = second_arg.kind else {
        todo!()
    };
    let ExpressionContent::ExpressionPart(ExpressionPart::Atom(atom)) = second_node_ref.as_named_expression().expression().unpack() else {
        todo!()
    };
    let mut total = true;
    if let Some(next) = iterator.next() {
        match &next.kind {
            ArgumentKind::Keyword { key: "total", .. } => {
                total = infer_typed_dict_total_argument(
                    i_s,
                    next.infer(i_s, &mut ResultContext::ExpectLiteral),
                    next.as_node_ref(),
                )?;
            }
            ArgumentKind::Keyword { key, node_ref, .. } => {
                let s = format!(r#"Unexpected keyword argument "{key}" for "TypedDict""#);
                node_ref.add_issue(i_s, IssueType::ArgumentIssue(s.into()));
                return None;
            }
            _ => {
                args.as_node_ref()
                    .add_issue(i_s, IssueType::UnexpectedArgumentsToTypedDict);
                return None;
            }
        };
    }
    if iterator.next().is_some() {
        args.as_node_ref()
            .add_issue(i_s, IssueType::TooManyArguments(" for \"TODO()\"".into()));
        return None;
    }
    let dct_iterator = match atom.unpack() {
        AtomContent::Dict(dct) => dct.iter_elements(),
        _ => {
            second_node_ref.add_issue(i_s, IssueType::TypedDictSecondArgMustBeDict);
            return None;
        }
    };
    let args_node_ref = args.as_node_ref();
    let on_type_var = &mut |i_s: &InferenceState, _: &_, _, _| TypeVarCallbackReturn::NotFound;
    let mut inference = args_node_ref.file.inference(i_s);
    let mut comp = TypeComputation::new(
        &mut inference,
        args.as_node_ref().as_link(),
        on_type_var,
        TypeComputationOrigin::Constraint,
    );
    let mut members = vec![];
    for element in dct_iterator {
        match element {
            DictElement::KeyValue(key_value) => {
                let Some(name) = StringSlice::from_string_in_expression(args_node_ref.file_index(), key_value.key()) else {
                    NodeRef::new(args_node_ref.file, key_value.key().index())
                        .add_issue(i_s, IssueType::TypedDictInvalidFieldName);
                    return None
                };
                let (type_, has_default) = comp.compute_typed_dict_entry(key_value.value(), total);
                members.push(TypedDictMember {
                    type_,
                    required: !has_default,
                    name,
                });
                key_value.key();
            }
            DictElement::DictStarred(d) => {
                NodeRef::new(args_node_ref.file, d.index())
                    .add_issue(i_s, IssueType::TypedDictInvalidFieldName);
                return None;
            }
        };
    }

    let type_var_likes = comp.into_type_vars(|_, _| ());
    Some(Inferred::new_unsaved_complex(
        ComplexPoint::TypedDictDefinition(Rc::new(DbType::TypedDict(Rc::new(TypedDict {
            name,
            defined_at: args_node_ref.as_link(),
            type_var_likes,
            members: members.into(),
        })))),
    ))
}

pub fn infer_typed_dict_total_argument(
    i_s: &InferenceState,
    inf: Inferred,
    node_ref: NodeRef,
) -> Option<bool> {
    if let Some(total) = inf.maybe_bool_literal(i_s) {
        Some(total)
    } else {
        node_ref.add_issue(i_s, IssueType::TypedDictTotalMustBeTrueOrFalse);
        None
    }
}

fn method_with_fallback<'db>(
    i_s: &InferenceState<'db, '_>,
    args: &dyn Arguments<'db>,
    result_context: &mut ResultContext,
    on_type_error: OnTypeError<'db, '_>,
    td: &TypedDict,
    name: &str,
    handler: fn(
        i_s: &InferenceState<'db, '_>,
        td: &TypedDict,
        args: &dyn Arguments<'db>,
    ) -> Option<Inferred>,
) -> Inferred {
    handler(i_s, td, args).unwrap_or_else(|| {
        let inst = Instance::new(i_s.db.python_state.typed_dict_class(), None);
        inst.lookup(i_s, args.as_node_ref(), name, LookupKind::OnlyType)
            .into_inferred()
            .execute_with_details(i_s, args, result_context, on_type_error)
    })
}
pub fn typed_dict_get<'db>(
    i_s: &InferenceState<'db, '_>,
    args: &dyn Arguments<'db>,
    result_context: &mut ResultContext,
    on_type_error: OnTypeError<'db, '_>,
    bound: Option<&DbType>,
) -> Inferred {
    let DbType::TypedDict(td) = bound.unwrap() else {
        unreachable!();
    };
    method_with_fallback(
        i_s,
        args,
        result_context,
        on_type_error,
        td,
        "get",
        typed_dict_get_internal,
    )
}

fn typed_dict_get_internal<'db>(
    i_s: &InferenceState<'db, '_>,
    td: &TypedDict,
    args: &dyn Arguments<'db>,
) -> Option<Inferred> {
    let mut iterator = args.iter();
    let first_arg = iterator.next()?;
    let second_arg = iterator.next();
    if iterator.next().is_some() {
        return None;
    }
    let infer_default = |context| match second_arg {
        Some(second) => match &second.kind {
            ArgumentKind::Positional { .. } | ArgumentKind::Keyword { key: "default", .. } => {
                Some(second.infer(i_s, context).as_db_type(i_s))
            }
            _ => return None,
        },
        None => Some(DbType::None),
    };

    let inferred_name = first_arg.maybe_positional_arg(i_s, &mut ResultContext::ExpectLiteral)?;
    Some(Inferred::from_type(
        if let Some(name) = inferred_name.maybe_string_literal(i_s) {
            if let Some(member) = td.find_member(i_s.db, name.as_str(i_s.db)) {
                let t = &member.type_;
                let default = infer_default(&mut ResultContext::Known(&Type::new(&t)))?;
                t.clone().union(i_s.db, default)
            } else {
                infer_default(&mut ResultContext::Unknown)?;
                i_s.db.python_state.object_db_type()
            }
        } else {
            infer_default(&mut ResultContext::Unknown)?;
            i_s.db.python_state.object_db_type()
        },
    ))
}

pub fn typed_dict_delitem<'db>(
    i_s: &InferenceState<'db, '_>,
    args: &dyn Arguments<'db>,
    result_context: &mut ResultContext,
    on_type_error: OnTypeError<'db, '_>,
    bound: Option<&DbType>,
) -> Inferred {
    let DbType::TypedDict(td) = bound.unwrap() else {
        unreachable!();
    };
    method_with_fallback(
        i_s,
        args,
        result_context,
        on_type_error,
        td,
        "__delitem__",
        typed_dict_delitem_internal,
    )
}

fn typed_dict_delitem_internal<'db>(
    i_s: &InferenceState<'db, '_>,
    td: &TypedDict,
    args: &dyn Arguments<'db>,
) -> Option<Inferred> {
    let inf_key = args.maybe_single_positional_arg(i_s, &mut ResultContext::ExpectLiteral)?;

    if let Some(key) = inf_key.maybe_string_literal(i_s) {
        let key = key.as_str(i_s.db);
        if let Some(member) = td.find_member(i_s.db, key) {
            if member.required {
                args.as_node_ref().add_issue(
                    i_s,
                    IssueType::TypedDictKeyCannotBeDeleted {
                        typed_dict: td.format(&FormatData::new_short(i_s.db)).into(),
                        key: key.into(),
                    },
                );
            }
        } else {
            args.as_node_ref().add_issue(
                i_s,
                IssueType::TypedDictHasNoKey {
                    typed_dict: td.format(&FormatData::new_short(i_s.db)).into(),
                    key: key.into(),
                },
            );
        }
    } else {
        args.as_node_ref()
            .add_issue(i_s, IssueType::TypedDictKeysMustBeStringLiteral);
    }
    Some(Inferred::from_type(DbType::None))
}

pub fn typed_dict_update<'db>(
    i_s: &InferenceState<'db, '_>,
    args: &dyn Arguments<'db>,
    result_context: &mut ResultContext,
    on_type_error: OnTypeError<'db, '_>,
    bound: Option<&DbType>,
) -> Inferred {
    let DbType::TypedDict(td) = bound.unwrap() else {
        unreachable!();
    };
    method_with_fallback(
        i_s,
        args,
        result_context,
        on_type_error,
        td,
        "update",
        typed_dict_update_internal,
    )
}

fn typed_dict_update_internal<'db>(
    i_s: &InferenceState<'db, '_>,
    td: &TypedDict,
    args: &dyn Arguments<'db>,
) -> Option<Inferred> {
    todo!()
}
