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
    new_typed_dict_internal(i_s, args).unwrap_or_else(|| todo!())
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
        first_arg.as_node_ref().add_issue(i_s, IssueType::UnexpectedArgumentsTo { name: "namedtuple" });
        return None
    };
    let expr = node_ref.as_named_expression().expression();
    let first = expr
        .maybe_single_string_literal()
        .map(|py_string| (node_ref, py_string));
    let Some(name) = StringSlice::from_string_in_expression(node_ref.file_index(), expr) else {
        todo!()
    };
    let Some(second_arg) = iterator.next() else {
        // TODO this is only done for namedtuple and not NamedTuple
        // Detected by execution of namedtuple
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
        if let ArgumentKind::Keyword { key: "total", .. } = &next.kind {
            total = next
                .infer(i_s, &mut ResultContext::ExpectLiteral)
                .maybe_bool_literal(i_s)
                .unwrap_or_else(|| todo!());
            // TODO
        } else {
            todo!()
        }
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
            todo!("{atom:?}")
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
        let DictElement::KeyValue(key_value) = element else {
            todo!()
        };
        let Some(param_name) = StringSlice::from_string_in_expression(args_node_ref.file_index(), key_value.key()) else {
            todo!()
        };
        let t = comp.compute_typed_dict_entry(key_value.value());
        params.push(CallableParam {
            param_specific: ParamSpecific::PositionalOrKeyword(t),
            has_default: !total,
            name: Some(param_name),
        });
        key_value.key();
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
