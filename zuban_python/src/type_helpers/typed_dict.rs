use std::rc::Rc;

use parsa_python_ast::{AtomContent, DictElement, ExpressionContent, ExpressionPart};

use crate::{
    arguments::{ArgumentKind, Arguments},
    database::{
        CallableContent, CallableParam, CallableParams, ComplexPoint, DbType, FunctionKind,
        ParamSpecific, StringSlice, TypedDict,
    },
    diagnostics::IssueType,
    file::{infer_string_index, TypeComputation, TypeComputationOrigin, TypeVarCallbackReturn},
    getitem::{SliceType, SliceTypeContent},
    inference_state::InferenceState,
    inferred::Inferred,
    matching::ResultContext,
    node_ref::NodeRef,
};

pub struct TypedDictHelper<'a>(pub &'a Rc<TypedDict>);
impl<'a> TypedDictHelper<'a> {
    pub fn get_item(
        &self,
        i_s: &InferenceState,
        slice_type: &SliceType,
        result_context: &mut ResultContext,
    ) -> Inferred {
        match slice_type.unpack() {
            SliceTypeContent::Simple(simple) => infer_string_index(i_s, simple, |name| {
                for param in self.0.__new__().expect_simple_params().iter() {
                    if param.name.unwrap().as_str(i_s.db) == name {
                        return Some(Inferred::from_type(
                            param.param_specific.clone().expect_positional_db_type(),
                        ));
                    }
                }
                Some(Inferred::new_any())
            }),
            SliceTypeContent::Slice(_) => todo!(),
            SliceTypeContent::Slices(_) => todo!(),
        }
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
                if let Some(b) = next
                    .infer(i_s, &mut ResultContext::ExpectLiteral)
                    .maybe_bool_literal(i_s)
                {
                    total = b;
                } else {
                    next.as_node_ref()
                        .add_issue(i_s, IssueType::TypedDictTotalMustBeTrueOrFalse);
                    return None;
                }
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
        args.as_node_ref().add_issue(
            i_s,
            IssueType::TooManyArguments(" for \"NamedTuple()\"".into()),
        );
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
    let mut params = vec![];
    for element in dct_iterator {
        match element {
            DictElement::KeyValue(key_value) => {
                let Some(param_name) = StringSlice::from_string_in_expression(args_node_ref.file_index(), key_value.key()) else {
                    NodeRef::new(args_node_ref.file, key_value.key().index())
                        .add_issue(i_s, IssueType::TypedDictInvalidFieldName);
                    return None
                };
                let t = comp.compute_typed_dict_entry(key_value.value());
                params.push(CallableParam {
                    param_specific: ParamSpecific::PositionalOrKeyword(t),
                    has_default: !total,
                    name: Some(param_name),
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
    let callable = CallableContent {
        name: Some(name),
        class_name: None,
        defined_at: args_node_ref.as_link(),
        kind: FunctionKind::Function,
        type_vars: type_var_likes,
        params: CallableParams::Simple(Rc::from(params)),
        result_type: DbType::Self_,
    };
    Some(Inferred::new_unsaved_complex(
        ComplexPoint::TypedDictDefinition(Rc::new(DbType::TypedDict(Rc::new(TypedDict::new(
            name, callable,
        ))))),
    ))
}
