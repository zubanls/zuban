use std::rc::Rc;

use parsa_python_ast::{
    AtomContent, CodeIndex, DictElement, ExpressionContent, ExpressionPart, StarLikeExpression,
    StarLikeExpressionIterator,
};

use crate::{
    arguments::{ArgumentKind, Arguments},
    database::{
        Database, DbString, DbType, Enum, EnumMember, EnumMemberDefinition, Literal, LiteralKind,
        PointLink, StringSlice,
    },
    debug,
    diagnostics::IssueType,
    file::File,
    inference_state::InferenceState,
    inferred::Inferred,
    matching::{LookupResult, ResultContext},
    node_ref::NodeRef,
};

use super::{Class, Instance};

pub fn lookup_on_enum_class(db: &Database, enum_: &Rc<Enum>, name: &str) -> LookupResult {
    lookup_members_on_enum(db, enum_, name)
}

pub fn lookup_on_enum_instance(
    i_s: &InferenceState,
    from: Option<NodeRef>,
    enum_: &Rc<Enum>,
    name: &str,
) -> LookupResult {
    if name == "value" {
        LookupResult::UnknownName(Inferred::gather_types_union(|add| {
            for member in enum_.members.iter() {
                add(i_s, infer_value_on_member(i_s, from, member.value))
            }
        }))
    } else {
        lookup_members_on_enum(i_s.db, enum_, name)
    }
}

fn infer_value_on_member(
    i_s: &InferenceState,
    from: Option<NodeRef>,
    definition: Option<PointLink>,
) -> Inferred {
    match definition {
        Some(link) => {
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
        None => Inferred::new_any(),
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
        "value" => LookupResult::UnknownName(infer_value_on_member(i_s, from, member.value())),
        "_ignore_" => LookupResult::None,
        _ => Instance::new(member.enum_.class(i_s.db), None).lookup(i_s, from, name),
    }
}

fn lookup_members_on_enum(db: &Database, enum_: &Rc<Enum>, name: &str) -> LookupResult {
    if name == "_ignore_" {
        return LookupResult::None;
    }
    match Enum::lookup(enum_, db, name) {
        Some(m) => LookupResult::UnknownName(Inferred::from_type(DbType::EnumMember(m.clone()))),
        None => LookupResult::None,
    }
}

pub fn execute_functional_enum(
    i_s: &InferenceState,
    class: Class,
    args: &dyn Arguments,
    result_context: &mut ResultContext,
) -> Option<Inferred> {
    let mut iterator = args.iter();
    let Some(name_arg) = iterator.next() else {
        todo!()
    };
    let Some(fields_arg) = iterator.next() else {
        todo!()
    };
    if iterator.next().is_some() {
        todo!()
    }

    let ArgumentKind::Positional { node_ref: name_node_ref, .. } = name_arg.kind else {
        todo!()
    };
    let Some(name) = StringSlice::from_string_in_expression(name_node_ref.file_index(), name_node_ref.as_named_expression().expression()) else {
        name_arg.as_node_ref().add_issue(i_s, IssueType::EnumFirstArgMustBeString);
        return None
    };

    let ArgumentKind::Positional { node_ref: fields_node_ref, .. } = fields_arg.kind else {
        todo!();
        return None
    };
    let members = gather_functional_enum_members(i_s, fields_node_ref);

    Some(Inferred::from_type(DbType::Type(Rc::new(DbType::Enum(
        Rc::new(Enum {
            name,
            class: class.node_ref.as_link(),
            members,
        }),
    )))))
}

fn gather_functional_enum_members(
    i_s: &InferenceState,
    node_ref: NodeRef,
) -> Box<[EnumMemberDefinition]> {
    let ExpressionContent::ExpressionPart(ExpressionPart::Atom(atom)) = node_ref.as_named_expression().expression().unpack() else {
        debug!("TODO enum creation param missing");
        return Default::default()
    };

    let mut members = vec![];

    let get_tuple_like = |mut iterator: StarLikeExpressionIterator| {
        let Some(first) = iterator.next() else {
            todo!()
        };
        let Some(second) = iterator.next() else {
            todo!()
        };
        let StarLikeExpression::NamedExpression(n) = first else {
            todo!()
        };
        StringSlice::from_string_in_expression(node_ref.file.file_index(), n.expression())
    };

    let mut add_from_iterator = |iterator| {
        for element in iterator {
            let StarLikeExpression::NamedExpression(ne) = element else {
                todo!()
            };
            let ExpressionContent::ExpressionPart(ExpressionPart::Atom(atom)) = ne.expression().unpack() else {
                todo!()
            };
            let name = match atom.unpack() {
                AtomContent::List(list) => get_tuple_like(list.unpack()),
                AtomContent::Tuple(tup) => get_tuple_like(tup.iter()),
                _ => StringSlice::from_string_in_expression(
                    node_ref.file.file_index(),
                    ne.expression(),
                ),
            };
            let Some(name) = name else {
                todo!("Add issue");
            };
            members.push(EnumMemberDefinition::new(name.into(), None))
        }
    };
    match atom.unpack() {
        AtomContent::List(list) => add_from_iterator(list.unpack()),
        AtomContent::Tuple(tup) => add_from_iterator(tup.iter()),
        AtomContent::Strings(s) => {
            match DbString::from_python_string(node_ref.file_index(), s.as_python_string()) {
                Some(s) => split_enum_members(i_s.db, &mut members, &s),
                _ => todo!(),
            }
        }
        AtomContent::Dict(d) => {
            for element in d.iter_elements() {
                let DictElement::KeyValue(kv) = element else {
                    todo!()
                };
                let Some(name) = StringSlice::from_string_in_expression(
                    node_ref.file.file_index(),
                    kv.key(),
                ) else {
                    todo!()
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
                    return members.into();
                }
            }
            todo!("{atom:?}")
        }
    };
    members.into()
}

fn split_enum_members(db: &Database, members: &mut Vec<EnumMemberDefinition>, s: &DbString) {
    let mut start = 0;
    for part in s.as_str(db).split(&[',', ' ']) {
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
