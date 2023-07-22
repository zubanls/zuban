use std::rc::Rc;

use parsa_python_ast::{
    AtomContent, CodeIndex, DictElement, ExpressionContent, ExpressionPart, StarLikeExpression,
};

use crate::{
    database::{Database, DbString, DbType, Enum, EnumMemberDefinition, LiteralKind, StringSlice},
    debug,
    file::File,
    inference_state::InferenceState,
    inferred::Inferred,
    matching::{LookupResult, ResultContext},
    node_ref::NodeRef,
};

pub fn lookup_on_enum(db: &Database, enum_: &Rc<Enum>, name: &str) -> LookupResult {
    if name == "_ignore_" {
        return LookupResult::None;
    }
    match Enum::lookup(enum_, db, name) {
        Some(m) => LookupResult::UnknownName(Inferred::from_type(DbType::EnumMember(m.clone()))),
        None => LookupResult::None,
    }
}

pub fn gather_functional_enum_members(
    i_s: &InferenceState,
    node_ref: NodeRef,
) -> Box<[EnumMemberDefinition]> {
    let ExpressionContent::ExpressionPart(ExpressionPart::Atom(atom)) = node_ref.as_named_expression().expression().unpack() else {
        debug!("TODO enum creation param missing");
        return Default::default()
    };

    let mut members = vec![];

    let mut add_from_iterator = |iterator| {
        for element in iterator {
            let StarLikeExpression::NamedExpression(ne) = element else {
                todo!()
            };
            let ExpressionContent::ExpressionPart(ExpressionPart::Atom(atom)) = ne.expression().unpack() else {
                todo!()
            };
            let name = match atom.unpack() {
                AtomContent::List(list) => todo!(),
                AtomContent::Tuple(tup) => {
                    let mut iterator = tup.iter();
                    let Some(first) = iterator.next() else {
                        todo!()
                    };
                    let Some(second) = iterator.next() else {
                        todo!()
                    };
                    let StarLikeExpression::NamedExpression(n) = first else {
                        todo!()
                    };
                    StringSlice::from_string_in_expression(
                        node_ref.file.file_index(),
                        n.expression(),
                    )
                }
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
