use std::borrow::Cow;

use crate::{
    inference_state::InferenceState,
    matching::{FormatData, Matcher},
};

use super::{FormatStyle, Type};

impl Type {
    pub fn simplified_union(&self, i_s: &InferenceState, other: &Self) -> Type {
        // Check out how mypy does it:
        // https://github.com/python/mypy/blob/ff81a1c7abc91d9984fc73b9f2b9eab198001c8e/mypy/typeops.py#L413-L486
        let highest_union_format_index = self
            .highest_union_format_index()
            .max(other.highest_union_format_index());
        simplified_union_from_iterators(
            i_s,
            [(0, self.clone()), (1, other.clone())].into_iter(),
            highest_union_format_index,
            false,
        )
    }
}

pub fn simplified_union_from_iterators(
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
            t.into_iter_with_unpacked_unions()
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
        match &additional.type_ {
            Type::RecursiveAlias(r1) if r1.generics.is_some() => {
                // Recursive aliases need special handling, because the normal subtype
                // checking will call this function again if generics are available to
                // cache the type. In that case we just avoid complex matching and use
                // a simple heuristic. This won't affect correctness, it might just
                // display a bigger union than necessary.
                for entry in new_types.iter() {
                    if let Type::RecursiveAlias(r2) = &entry.type_ {
                        if r1 == r2 {
                            continue 'outer;
                        }
                    }
                }
            }
            _ => {
                for (i, current) in new_types.iter().enumerate() {
                    if current.type_.has_any(i_s) {
                        continue;
                    }
                    match &current.type_ {
                        Type::RecursiveAlias(r) if r.generics.is_some() => (),
                        t => {
                            if let Type::Class(c) = t {
                                if c.class(i_s.db).is_calculating_class_infos() {
                                    if &additional.type_ == t {
                                        continue 'outer;
                                    } else {
                                        continue;
                                    }
                                }
                            }
                            if additional
                                .type_
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
                                &additional.type_,
                            )
                            .bool()
                            {
                                finished = false;
                                continue 'outer;
                            }
                        }
                    }
                }
            }
        }
        new_types.push(additional);
    }
    if finished {
        MergeSimplifiedUnionResult::Done(match new_types.len() {
            0 => Type::Never,
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
            _ => {
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
            .filter_map(|e| {
                (!format_as_optional || !matches!(e.type_, Type::None))
                    .then(|| (e.format_index, e.type_.format(format_data)))
            })
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
