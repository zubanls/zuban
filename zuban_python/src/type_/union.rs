use std::{
    borrow::{Borrow, Cow},
    collections::HashMap,
    rc::Rc,
};

use super::{FormatStyle, LiteralKind, NeverCause, TupleArgs, TupleUnpack, Type, WithUnpack};
use crate::{
    database::Database, format_data::FormatData, inference_state::InferenceState, matching::Matcher,
};

impl Type {
    pub fn simplified_union(&self, i_s: &InferenceState, other: &Self) -> Self {
        // Check out how mypy does it:
        // https://github.com/python/mypy/blob/ff81a1c7abc91d9984fc73b9f2b9eab198001c8e/mypy/typeops.py#L413-L486
        let highest_union_format_index = self
            .highest_union_format_index()
            .max(other.highest_union_format_index());
        simplified_union_from_iterators_with_format_index(
            i_s,
            [(0, self.clone()), (1, other.clone())].into_iter(),
            highest_union_format_index,
            false,
        )
    }
}

impl TupleArgs {
    pub fn simplified_union(&self, i_s: &InferenceState, other: &Self) -> Self {
        if self == other {
            return self.clone();
        }
        match (self, other) {
            (TupleArgs::FixedLen(ts1), TupleArgs::FixedLen(ts2)) if ts1.len() == ts2.len() => {
                TupleArgs::FixedLen(
                    ts1.iter()
                        .zip(ts2.iter())
                        .map(|(t1, t2)| t1.simplified_union(i_s, t2))
                        .collect(),
                )
            }
            (TupleArgs::WithUnpack(w1), TupleArgs::WithUnpack(w2))
                if w1.before.len() == w2.before.len() && w1.after.len() == w2.after.len() =>
            {
                TupleArgs::WithUnpack(WithUnpack {
                    before: w1
                        .before
                        .iter()
                        .zip(w2.before.iter())
                        .map(|(t1, t2)| t1.simplified_union(i_s, t2))
                        .collect(),
                    unpack: match (&w1.unpack, &w2.unpack) {
                        (TupleUnpack::ArbitraryLen(t1), TupleUnpack::ArbitraryLen(t2)) => {
                            TupleUnpack::ArbitraryLen(t1.simplified_union(i_s, t2))
                        }
                        (TupleUnpack::TypeVarTuple(tvt1), TupleUnpack::TypeVarTuple(tvt2))
                            if tvt1 == tvt2 =>
                        {
                            TupleUnpack::TypeVarTuple(tvt1.clone())
                        }
                        _ => TupleUnpack::ArbitraryLen(i_s.db.python_state.object_type()),
                    },
                    after: w1
                        .after
                        .iter()
                        .zip(w2.after.iter())
                        .map(|(t1, t2)| t1.simplified_union(i_s, t2))
                        .collect(),
                })
            }
            (_, _) => TupleArgs::ArbitraryLen(Box::new(
                self.simplified_union_of_tuple_entries(i_s)
                    .simplified_union(i_s, &other.simplified_union_of_tuple_entries(i_s)),
            )),
        }
    }
}

pub fn simplified_union_from_iterators<'x, T: Borrow<Type>>(
    i_s: &InferenceState,
    types: impl Iterator<Item = T> + Clone,
) -> Type {
    let highest_union_format_index = types
        .clone()
        .map(|t| t.borrow().highest_union_format_index())
        .max()
        .unwrap_or(0);
    simplified_union_from_iterators_with_format_index(
        i_s,
        types.map(|t| t.borrow().clone()).enumerate(),
        highest_union_format_index,
        false,
    )
}

pub fn simplified_union_from_iterators_with_format_index(
    i_s: &InferenceState,
    types: impl Iterator<Item = (usize, Type)>,
    // We need this to make sure that the unions within the iterator can be properly ordered.
    highest_union_format_index: usize,
    format_as_optional: bool,
) -> Type {
    let multiply = highest_union_format_index + 1;
    let mut result = merge_simplified_union_type(
        i_s,
        types.into_iter().flat_map(|(format_index, t)| {
            t.into_iter_with_unpacked_unions(i_s.db, false)
                .map(move |entry| UnionEntry {
                    format_index: format_index * multiply + entry.format_index,
                    type_: entry.type_,
                })
        }),
        format_as_optional,
    );
    loop {
        match result {
            MergeSimplifiedUnionResult::Done(t) => return t,
            MergeSimplifiedUnionResult::NotDone(items) => {
                result = merge_simplified_union_type(i_s, items.into_iter(), format_as_optional)
            }
        }
    }
}

enum MergeSimplifiedUnionResult {
    NotDone(Vec<UnionEntry>),
    Done(Type),
}

fn merge_simplified_union_type(
    i_s: &InferenceState,
    types: impl Iterator<Item = UnionEntry>,
    format_as_optional: bool,
) -> MergeSimplifiedUnionResult {
    let mut new_types: Vec<UnionEntry> = vec![];
    let mut finished = true;
    let mut had_enum_member = false;
    let mut had_true = false;
    let mut had_false = false;
    'outer: for additional in types {
        if additional.type_.has_any(i_s) {
            if !new_types
                .iter()
                .any(|entry| entry.type_ == additional.type_)
            {
                new_types.push(additional)
            }
            continue;
        }
        if new_types
            .iter()
            .any(|entry| entry.type_ == additional.type_)
        {
            // Just do a quick check if the types are exactly the same. This might happen quite
            // often in simple cases and will probably be a minor speed boost and catch some
            // recursive types that we don't handle otherwise.
            continue;
        }
        match &additional.type_ {
            Type::RecursiveType(r1) if r1.generics.is_some() => {
                // Recursive aliases need special handling, because the normal subtype
                // checking will call this function again if generics are available to
                // cache the type.
            }
            additional_t => {
                for (i, current) in new_types.iter().enumerate() {
                    if current.type_.has_any(i_s) {
                        continue;
                    }
                    match &current.type_ {
                        Type::RecursiveType(r) if r.generics.is_some() => (),
                        t => {
                            if let Type::Class(c) = t {
                                if c.class(i_s.db).is_calculating_class_infos() {
                                    if additional_t == t {
                                        continue 'outer;
                                    } else {
                                        continue;
                                    }
                                }
                            }
                            if additional_t
                                .is_super_type_of(i_s, &mut Matcher::with_ignored_promotions(), t)
                                .bool()
                            {
                                new_types[i].type_ = additional.type_;
                                finished = false;
                                continue 'outer;
                            }
                            if t.is_super_type_of(
                                i_s,
                                &mut Matcher::with_ignored_promotions(),
                                additional_t,
                            )
                            .bool()
                            {
                                finished = false;
                                continue 'outer;
                            }
                        }
                    }
                }
                match additional_t {
                    Type::EnumMember(_) => had_enum_member = true,
                    Type::Literal(literal) => match &literal.kind {
                        LiteralKind::Bool(true) => had_true = true,
                        LiteralKind::Bool(false) => had_false = true,
                        _ => (),
                    },
                    _ => (),
                }
            }
        }
        new_types.push(additional);
    }
    if had_enum_member {
        // If all enum members are found in a union, just use an enum instance instead.
        try_contracting_enum_members(&mut new_types)
    }
    if had_false && had_true {
        contract_bool_literals(i_s.db, &mut new_types)
    }
    if finished {
        MergeSimplifiedUnionResult::Done(match new_types.len() {
            0 => Type::Never(NeverCause::Other),
            1 => new_types.into_iter().next().unwrap().type_,
            _ => {
                let mut union = UnionType {
                    format_as_optional,
                    entries: new_types.into(),
                };
                union.sort_for_priority();
                Type::Union(union)
            }
        })
    } else {
        MergeSimplifiedUnionResult::NotDone(new_types)
    }
}

fn try_contracting_enum_members(entries: &mut Vec<UnionEntry>) {
    let mut enum_counts = HashMap::new();
    for (i, e) in entries.iter().enumerate() {
        if let Type::EnumMember(member) = &e.type_ {
            enum_counts
                .entry(member.enum_.defined_at)
                .or_insert((member.clone(), 0))
                .1 += 1;
        }
    }
    entries.retain_mut(|entry| {
        if let Type::EnumMember(member) = &entry.type_ {
            for (first_member, count) in enum_counts.values() {
                if Rc::ptr_eq(&member.enum_, &first_member.enum_)
                    && first_member.enum_.members.len() <= *count
                {
                    debug_assert_eq!(first_member.enum_.members.len(), *count);
                    let should_retain = first_member.member_index == member.member_index;
                    if should_retain {
                        entry.type_ = Type::Enum(member.enum_.clone())
                    }
                    return should_retain;
                }
            }
        }
        true
    })
}

fn contract_bool_literals(db: &Database, entries: &mut Vec<UnionEntry>) {
    let mut first = true;
    entries.retain_mut(|entry| {
        if let Type::Literal(literal) = &entry.type_ {
            if matches!(&literal.kind, LiteralKind::Bool(_)) {
                if first {
                    first = false;
                    entry.type_ = db.python_state.bool_type();
                } else {
                    return false;
                }
            }
        }
        true
    })
}

#[derive(Debug, Clone, PartialEq)]
pub struct UnionEntry {
    pub type_: Type,
    pub format_index: usize,
}

#[derive(Debug, Clone, PartialEq)]
pub struct UnionType {
    pub entries: Box<[UnionEntry]>,
    pub format_as_optional: bool,
}

impl UnionType {
    pub fn new(entries: Vec<UnionEntry>) -> Self {
        debug_assert!(entries.len() > 1);
        Self {
            entries: entries.into_boxed_slice(),
            format_as_optional: false,
        }
    }

    pub fn from_types(types: Vec<Type>) -> Self {
        Self::new(
            types
                .into_iter()
                .enumerate()
                .map(|(format_index, type_)| UnionEntry {
                    format_index,
                    type_,
                })
                .collect(),
        )
    }

    pub fn iter(&self) -> impl Iterator<Item = &Type> {
        self.entries.iter().map(|u| &u.type_)
    }

    pub fn sort_for_priority(&mut self) {
        self.entries.sort_by_key(|t| match t.type_ {
            Type::Literal(_) | Type::EnumMember(_) => -1,
            Type::None => 2,
            Type::TypeVar(_) => 3,
            Type::Any(_) => 4,
            _ => t.type_.has_type_vars().into(),
        });
    }

    pub fn format(&self, format_data: &FormatData) -> Box<str> {
        let mut iterator = self.entries.iter();
        let mut sorted = match format_data.style {
            FormatStyle::MypyRevealType => String::new(),
            FormatStyle::Short => {
                // Fetch the literals in the front of the union and format them like Literal[1, 2]
                // instead of Literal[1] | Literal[2].
                let count = self
                    .iter()
                    .take_while(|t| matches!(t, Type::Literal(_) | Type::EnumMember(_)))
                    .count();
                if count > 1 {
                    let lit = format!(
                        "Literal[{}]",
                        iterator
                            .by_ref()
                            .take(count)
                            .map(|t| match &t.type_ {
                                Type::Literal(l) => l.format_inner(format_data.db),
                                Type::EnumMember(m) => Cow::Owned(m.format_inner(format_data)),
                                _ => unreachable!(),
                            })
                            .collect::<Vec<_>>()
                            .join(", ")
                    );
                    if count == self.entries.len() {
                        return lit.into();
                    } else {
                        lit + " | "
                    }
                } else {
                    String::new()
                }
            }
        };
        let format_as_optional =
            self.format_as_optional && format_data.style != FormatStyle::MypyRevealType;
        let mut unsorted = iterator
            .filter(|&e| (!format_as_optional || !matches!(e.type_, Type::None)))
            .map(|e| (e.format_index, e.type_.format(format_data)))
            .collect::<Vec<_>>();
        unsorted.sort_by_key(|(format_index, _)| *format_index);
        sorted += &unsorted
            .into_iter()
            .map(|(_, t)| t)
            .collect::<Vec<_>>()
            .join(" | ");
        if format_as_optional {
            format!("Optional[{sorted}]").into()
        } else {
            sorted.into()
        }
    }
}
