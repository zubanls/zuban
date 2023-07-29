use std::rc::Rc;

use parsa_python_ast::{
    AtomContent, CodeIndex, DictElement, Expression, ExpressionContent, ExpressionPart,
    StarLikeExpression, StarLikeExpressionIterator,
};

use crate::{
    arguments::{ArgumentKind, Arguments},
    database::{
        Database, DbString, DbType, Enum, EnumMember, EnumMemberDefinition, Literal, LiteralKind,
        PointLink, StringSlice,
    },
    diagnostics::IssueType,
    file::File,
    inference_state::InferenceState,
    inferred::Inferred,
    matching::{LookupResult, ResultContext},
    node_ref::NodeRef,
};

use super::{Class, Instance};

pub fn lookup_on_enum_class(
    i_s: &InferenceState,
    enum_: &Rc<Enum>,
    name: &str,
    result_context: &mut ResultContext,
) -> LookupResult {
    lookup_members_on_enum(i_s, enum_, name, result_context)
}

pub fn lookup_on_enum_instance(
    i_s: &InferenceState,
    from: Option<NodeRef>,
    enum_: &Rc<Enum>,
    name: &str,
    result_context: &mut ResultContext,
) -> LookupResult {
    if matches!(name, "value" | "_value_") {
        LookupResult::UnknownName(Inferred::gather_types_union(|add| {
            for member in enum_.members.iter() {
                add(i_s, infer_value_on_member(i_s, from, enum_, member.value))
            }
        }))
    } else {
        lookup_members_on_enum(i_s, enum_, name, result_context)
    }
}

fn infer_value_on_member(
    i_s: &InferenceState,
    from: Option<NodeRef>,
    enum_: &Enum,
    definition: Option<PointLink>,
) -> Inferred {
    match definition {
        // I'm not 100% sure why this is, but Mypy returns Any on all enums that have a __new__
        // defined.
        Some(link) if !enum_.has_customized_new(i_s) => {
            let node_ref = NodeRef::from_link(i_s.db, link);
            let inferred = if let Some(name) = node_ref.maybe_name() {
                node_ref.file.inference(i_s).infer_name(name)
            } else {
                let expr = node_ref.as_expression();
                node_ref.file.inference(i_s).infer_expression(expr);
                todo!();
            };
            match inferred.as_type(i_s).as_ref() {
                DbType::Class(c) if c.link == i_s.db.python_state.enum_auto_link() => {
                    Inferred::from_type(i_s.db.python_state.int_db_type())
                }
                _ => inferred,
            }
        }
        _ => Inferred::new_any(),
    }
}

pub fn lookup_on_enum_member_instance(
    i_s: &InferenceState,
    from: Option<NodeRef>,
    member: &EnumMember,
    name: &str,
) -> LookupResult {
    match name {
        "name" => LookupResult::UnknownName(Inferred::from_type(DbType::Literal(Literal::new(
            LiteralKind::String(DbString::RcStr(member.name(i_s.db).into())),
        )))),
        "value" | "_value_" => LookupResult::UnknownName(infer_value_on_member(
            i_s,
            from,
            &member.enum_,
            member.value(),
        )),
        "_ignore_" => LookupResult::None,
        _ => Instance::new(member.enum_.class(i_s.db), None).lookup(i_s, from, name),
    }
}

fn lookup_members_on_enum(
    i_s: &InferenceState,
    enum_: &Rc<Enum>,
    name: &str,
    result_context: &mut ResultContext,
) -> LookupResult {
    if name == "_ignore_" {
        return LookupResult::None;
    }
    match Enum::lookup(enum_, i_s.db, name) {
        Some(m) => LookupResult::UnknownName(Inferred::from_type(
            match result_context.is_literal_context(i_s) {
                true => DbType::EnumMember(m.clone()),
                false => DbType::Enum(enum_.clone()),
            },
        )),
        None => LookupResult::None,
    }
}

pub fn execute_functional_enum(
    i_s: &InferenceState,
    class: Class,
    args: &dyn Arguments,
    result_context: &mut ResultContext,
) -> Option<Inferred> {
    let mut name_infos = None;
    let mut fields_infos = None;
    for arg in args.iter() {
        match arg.kind {
            ArgumentKind::Positional { node_ref, .. } => {
                let expr = node_ref.as_named_expression().expression();
                if name_infos.is_none() {
                    name_infos = Some((node_ref, expr));
                } else if fields_infos.is_none() {
                    fields_infos = Some((node_ref, expr));
                }
                // All the other arguments are not relevant here and were checked by checking
                // EnumMeta.__call__.
            }
            ArgumentKind::Keyword {
                key,
                node_ref,
                expression,
                ..
            } => match key {
                "value" => name_infos = Some((node_ref, expression)),
                "names" => fields_infos = Some((node_ref, expression)),
                // Keyword names were checked by checking EnumMeta.__call__
                _ => (),
            },
            _ => {
                args.as_node_ref().add_issue(
                    i_s,
                    IssueType::EnumUnexpectedArguments {
                        name: class.name().into(),
                    },
                );
                return None;
            }
        }
    }
    let name_infos = name_infos.unwrap();
    let fields_infos = fields_infos.unwrap();

    let Some(name) = StringSlice::from_string_in_expression(name_infos.0.file_index(), name_infos.1) else {
        name_infos.0.add_issue(i_s, IssueType::EnumFirstArgMustBeString);
        return None
    };

    let members = gather_functional_enum_members(i_s, class, fields_infos.0, fields_infos.1)?;
    if members.len() == 0 {
        fields_infos.0.add_issue(
            i_s,
            IssueType::EnumNeedsAtLeastOneItem {
                name: class.name().into(),
            },
        );
        return None;
    }

    Some(Inferred::from_type(DbType::Type(Rc::new(DbType::Enum(
        Enum::new(
            name,
            class.node_ref.as_link(),
            members,
            class.has_customized_enum_new(i_s).into(),
        ),
    )))))
}

fn gather_functional_enum_members(
    i_s: &InferenceState,
    class: Class,
    node_ref: NodeRef,
    expression: Expression,
) -> Option<Box<[EnumMemberDefinition]>> {
    let ExpressionContent::ExpressionPart(ExpressionPart::Atom(atom)) = expression.unpack() else {
        node_ref.add_issue(i_s, IssueType::EnumInvalidSecondArgument);
        return None
    };

    let mut members = vec![];

    let get_tuple_like = |mut iterator: StarLikeExpressionIterator| -> Option<StringSlice> {
        let Some(first) = iterator.next() else {
            todo!()
        };
        let Some(second) = iterator.next() else {
            todo!()
        };
        if iterator.next().is_some() {
            return None;
        }
        let StarLikeExpression::NamedExpression(n) = first else {
            todo!()
        };
        StringSlice::from_string_in_expression(node_ref.file.file_index(), n.expression())
    };

    let mut add_from_iterator = |iterator| -> Option<()> {
        for element in iterator {
            let StarLikeExpression::NamedExpression(ne) = element else {
                todo!()
            };
            let ExpressionContent::ExpressionPart(ExpressionPart::Atom(atom)) = ne.expression().unpack() else {
                todo!()
            };
            let name = match atom.unpack() {
                AtomContent::List(list) => get_tuple_like(list.unpack())?,
                AtomContent::Tuple(tup) => get_tuple_like(tup.iter())?,
                _ => StringSlice::from_string_in_expression(
                    node_ref.file.file_index(),
                    ne.expression(),
                )?,
            };
            members.push(EnumMemberDefinition::new(name.into(), None))
        }
        return Some(());
    };

    let mut add_from_iterator_with_error = |iterator| -> Option<()> {
        if add_from_iterator(iterator).is_none() {
            NodeRef::new(node_ref.file, atom.index()).add_issue(
                i_s,
                IssueType::EnumWithTupleOrListExpectsStringPairs {
                    name: class.name().into(),
                },
            );
            None
        } else {
            Some(())
        }
    };
    match atom.unpack() {
        AtomContent::List(list) => {
            add_from_iterator_with_error(list.unpack())?;
        }
        AtomContent::Tuple(tup) => {
            add_from_iterator_with_error(tup.iter())?;
        }
        AtomContent::Strings(s) => {
            match DbString::from_python_string(node_ref.file_index(), s.as_python_string()) {
                Some(s) => split_enum_members(i_s.db, &mut members, &s),
                _ => todo!(),
            }
        }
        AtomContent::Dict(d) => {
            for element in d.iter_elements() {
                let DictElement::KeyValue(kv) = element else {
                    todo!("In test functional_enum_starred_dict_literal_errors")
                };
                let Some(name) = StringSlice::from_string_in_expression(
                    node_ref.file.file_index(),
                    kv.key(),
                ) else {
                    node_ref.add_issue(i_s, IssueType::EnumWithDictRequiresStringLiterals {
                        name: class.name().into(),
                    });
                    return None
                };
                members.push(EnumMemberDefinition::new(name.into(), None));
            }
        }
        _ => {
            let inf = node_ref
                .file
                .inference(i_s)
                .infer_atom(atom, &mut ResultContext::Unknown);
            if let DbType::Literal(literal) = inf.as_type(i_s).as_ref() {
                if let LiteralKind::String(s) = &literal.kind {
                    split_enum_members(i_s.db, &mut members, s);
                    return Some(members.into());
                }
            }
            node_ref.add_issue(i_s, IssueType::EnumInvalidSecondArgument);
            return None;
        }
    };
    Some(members.into())
}

fn split_enum_members(db: &Database, members: &mut Vec<EnumMemberDefinition>, s: &DbString) {
    let mut start = 0;
    for part in s.as_str(db).split(&[',', ' ']) {
        if part == "" {
            continue;
        }
        let name = match s {
            DbString::StringSlice(slice) => {
                let start = slice.start + start;
                StringSlice::new(slice.file_index, start, start + part.len() as CodeIndex).into()
            }
            DbString::RcStr(_) => DbString::RcStr(part.into()),
        };
        members.push(EnumMemberDefinition::new(name, None));
        start += part.len() as CodeIndex + 1;
    }
}
