use crate::{inference_state::InferenceState, matching::Matcher};

use super::{Type, UnionEntry, UnionType};

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
