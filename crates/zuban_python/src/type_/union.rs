use std::{
    borrow::{Borrow, Cow},
    collections::HashMap,
    hash::{Hash, Hasher},
    sync::Arc,
};

use utils::{FastHashMap, FastHashSet};

use super::{FormatStyle, Literal, LiteralKind, NeverCause, Type};
use crate::{
    database::Database, debug, format_data::FormatData, inference_state::InferenceState,
    inferred::Inferred, matching::Matcher, type_::AnyCause, utils::debug_indent,
};

impl Type {
    pub fn simplified_union(&self, i_s: &InferenceState, other: &Self) -> Self {
        debug!(
            "Simplify union for {} and {}",
            self.format_short(i_s.db),
            other.format_short(i_s.db)
        );
        let _indent = debug_indent();
        // Check out how mypy does it:
        // https://github.com/python/mypy/blob/ff81a1c7abc91d9984fc73b9f2b9eab198001c8e/mypy/typeops.py#L413-L486
        Type::simplified_union_from_iterators(i_s, [self, other].into_iter())
    }

    pub fn simplified_union_in_place(&mut self, i_s: &InferenceState, other: &Type) {
        *self =
            std::mem::replace(self, Self::Never(NeverCause::Other)).simplified_union(i_s, other);
    }

    pub fn owned_simplified_union_from_iterators<T: Borrow<Self>>(
        i_s: &InferenceState,
        types: impl IntoIterator<Item = T>,
    ) -> Self {
        let types: Vec<_> = types.into_iter().collect();
        Self::simplified_union_from_iterators(i_s, types.iter().map(|t| t.borrow()))
    }

    pub fn simplified_union_from_iterators<'x>(
        i_s: &InferenceState,
        types: impl Iterator<Item = &'x Type> + Clone,
    ) -> Self {
        merge_simplified_union_type(
            i_s,
            types.flat_map(|t| t.iter_with_unpacked_unions_without_unpacking_recursive_types()),
        )
    }

    pub fn make_optional(&mut self) {
        *self = std::mem::replace(self, Self::Never(NeverCause::Other)).union(Type::None);
    }

    pub fn union(self, other: Self) -> Self {
        let entries = match self {
            Self::Union(u1) => {
                let mut vec = u1.entries.to_vec();
                match other {
                    Self::Union(u2) => {
                        for o in u2.entries.iter() {
                            if !vec.contains(o) {
                                vec.push(o.clone());
                            }
                        }
                    }
                    Type::Never(_) => (), // `X | Never is always X`
                    _ => {
                        if !vec.iter().any(|t| *t == other) {
                            vec.push(other)
                        }
                    }
                };
                vec
            }
            Self::Never(_) => return other,
            _ => match other {
                Self::Union(u) => {
                    if u.iter().any(|t| t == &self) {
                        return Self::Union(u);
                    } else {
                        let mut vec = u.entries.to_vec();
                        vec.push(self);
                        vec
                    }
                }
                _ => {
                    if self == other || matches!(other, Type::Never(_)) {
                        return self;
                    } else {
                        vec![self, other]
                    }
                }
            },
        };
        Self::Union(UnionType::new(
            entries, true, // TODO should we calculate this?
        ))
    }
}

fn merge_simplified_union_type<'x>(
    i_s: &InferenceState,
    types: impl Iterator<Item = &'x Type>,
) -> Type {
    let mut new_types: Vec<Type> = vec![];
    let mut literal_values = FastHashMap::default();
    let mut had_enum_member = false;
    let mut had_true = false;
    let mut had_false = false;
    let mut literal_index = 0;
    'outer: for additional_t in types {
        if let Type::Literal(literal) = additional_t
            && !matches!(&literal.kind, LiteralKind::Bool(_))
        {
            // Handle literals separately, because otherwise simplifying unions can be extremely
            // slow.
            literal_values
                .entry(literal.value(i_s.db))
                .or_insert((new_types.len() + literal_index, additional_t));
            literal_index += 1;
            continue;
        }
        if additional_t.is_object(i_s.db) {
            return additional_t.clone();
        }
        if additional_t.has_any(i_s.db) {
            // Generics with unknown type params can probably simply be merged with other objects
            // of the same type.
            if let Type::Class(c1) = &additional_t
                && c1.generics.all_any_with_unknown_type_params()
                && new_types
                    .iter()
                    .any(|e| matches!(e, Type::Class(c2) if c1.link == c2.link))
            {
                continue;
            }
            if !new_types.iter().any(|entry| {
                // We cannot use normal unpacking of recursive types, because it that triggers
                // simplified unions again, due to unpacking of recursive types.
                entry.is_equal_type_without_unpacking_recursive_types(i_s.db, &additional_t)
            }) && !matches!(additional_t, Type::Any(AnyCause::UnknownTypeParam))
            {
                new_types.push(additional_t.clone())
            }
            continue;
        }
        if new_types.iter().any(|entry| entry == additional_t) {
            // Just do a quick check if the types are exactly the same. This might happen quite
            // often in simple cases and will probably be a minor speed boost and catch some
            // recursive types that we don't handle otherwise.
            continue;
        }
        let is_recursive_with_generics =
            |t: &_| matches!(t, Type::RecursiveType(r1) if r1.generics.is_some());
        // Recursive aliases need special handling, because the normal subtype
        // checking will call this function again if generics are available to
        // cache the type.
        if is_recursive_with_generics(&additional_t) {
            // Since we don't remove duplicate entries in the proper way we at least do a quick
            // equals and remove simple duplicates.
            if new_types.iter().any(|e| e == additional_t) {
                continue;
            }
        } else {
            for (i, current) in new_types.iter_mut().enumerate() {
                if current.has_any(i_s.db) {
                    if let Type::Class(c1) = current
                        && c1.generics.all_any_with_unknown_type_params()
                        && matches!(additional_t, Type::Class(c2) if c1.link == c2.link)
                    {
                        *current = additional_t.clone();
                        continue 'outer;
                    }
                    continue;
                } else if additional_t.is_calculating(i_s.db) {
                    break;
                }
                let t = current;
                if is_recursive_with_generics(t) {
                    continue;
                }
                if t.is_calculating(i_s.db) {
                    if additional_t == t {
                        continue 'outer;
                    } else {
                        continue;
                    }
                }
                if additional_t
                    .is_super_type_of(i_s, &mut Matcher::with_ignored_promotions(), t)
                    .bool()
                {
                    // After replacing the old entry we have to check all the following
                    // ones if they also need to be removed.
                    new_types
                        .extract_if(i + 1.., |e| {
                            // These are essentially the conditions from above repeated
                            if e.has_any(i_s.db)
                                || e.is_calculating(i_s.db)
                                || is_recursive_with_generics(e)
                            {
                                return false;
                            }
                            additional_t
                                .is_super_type_of(i_s, &mut Matcher::with_ignored_promotions(), e)
                                .bool()
                        })
                        .for_each(drop);
                    new_types[i] = additional_t.clone();
                    continue 'outer;
                }
                if t.is_super_type_of(i_s, &mut Matcher::with_ignored_promotions(), additional_t)
                    .bool()
                {
                    continue 'outer;
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
        new_types.push(additional_t.clone());
    }
    if had_enum_member {
        // If all enum members are found in a union, just use an enum instance instead.
        try_contracting_enum_members(&mut new_types)
    }
    if had_false && had_true {
        contract_bool_literals(i_s.db, &mut new_types)
    }
    if !literal_values.is_empty() {
        if !new_types.is_empty() {
            literal_values.retain(|_, (_, v)| {
                let Type::Literal(l) = v else { unreachable!() };
                !new_types.iter().any(|t| *t == l.fallback_type(i_s.db))
            });
        }
        if !literal_values.is_empty() {
            let mut all: Vec<_> = literal_values.into_values().collect();
            // Sort by the original order
            all.sort_by_key(|(i, _)| *i);
            // Insert in the first spot literals appeared, but since elements were removed by
            // contracting enums above, we have to account for that.
            let insert_index = all[0].0.min(new_types.len());
            new_types.splice(
                insert_index..insert_index,
                all.into_iter().map(|(_, v)| v.clone()),
            );
        }
    }
    Type::from_union_entries(
        new_types, true, // TODO shouldn't this be calculated?
    )
}

fn try_contracting_enum_members(entries: &mut Vec<Type>) {
    let mut enum_counts = HashMap::new();
    for e in entries.iter() {
        if let Type::EnumMember(member) = e {
            enum_counts
                .entry(member.enum_.defined_at)
                .or_insert((member.clone(), 0))
                .1 += 1;
        }
    }
    entries.retain_mut(|entry| {
        if let Type::EnumMember(member) = entry {
            for (first_member, count) in enum_counts.values() {
                if Arc::ptr_eq(&member.enum_, &first_member.enum_)
                    && first_member.enum_.members.len() <= *count
                {
                    debug_assert_eq!(first_member.enum_.members.len(), *count);
                    let should_retain = first_member.member_index == member.member_index;
                    if should_retain {
                        *entry = Type::Enum(member.enum_.clone())
                    }
                    return should_retain;
                }
            }
        }
        true
    })
}

fn contract_bool_literals(db: &Database, entries: &mut Vec<Type>) {
    let mut first = true;
    entries.retain_mut(|entry| {
        if let Type::Literal(literal) = entry
            && matches!(&literal.kind, LiteralKind::Bool(_))
        {
            if first {
                first = false;
                *entry = db.python_state.bool_type();
            } else {
                return false;
            }
        }
        true
    })
}

impl PartialEq for UnionType {
    fn eq(&self, other: &Self) -> bool {
        // might_have_type_vars is a hint and should be ignored when quickly checking if two types
        // are equal.
        self.entries == other.entries
    }
}

impl Hash for UnionType {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.entries.hash(state)
    }
}

#[derive(Debug, Clone, Eq)]
pub(crate) struct UnionType {
    pub entries: Arc<[Type]>,
    pub might_have_type_vars: bool,
}

impl UnionType {
    pub fn new(entries: Vec<Type>, might_have_type_vars: bool) -> Self {
        debug_assert!(entries.len() > 1);
        Self {
            entries: entries.into(),
            might_have_type_vars,
        }
    }

    pub fn from_types(types: impl IntoIterator<Item = Type>, might_have_type_vars: bool) -> Self {
        Self {
            entries: types.into_iter().collect(),
            might_have_type_vars,
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = &Type> + Clone {
        self.entries.iter()
    }

    pub fn bool_literal_count(&self) -> usize {
        self.iter()
            .filter(|t| {
                matches!(
                    t,
                    Type::Literal(Literal {
                        kind: LiteralKind::Bool(_),
                        ..
                    })
                )
            })
            .count()
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
                            .map(|t| match t {
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
        sorted += &iterator
            .map(|e| {
                let mut result = e.format(format_data);
                if matches!(e, Type::Callable(_))
                    && matches!(format_data.style, FormatStyle::MypyRevealType)
                {
                    result = format!("({result})").into();
                }
                result
            })
            .collect::<Vec<_>>()
            .join(" | ");
        sorted.into()
    }
}

pub type TypeGatherer = GenericTypeGatherer<Type>;
pub type ComplexTypeGatherer<'x> = GenericTypeGatherer<Cow<'x, Type>>;

// 4 elements is usually enough to use on the stack
#[derive(Debug)]
pub(crate) struct GenericTypeGatherer<T>(smallvec::SmallVec<[T; 4]>);

impl<T> Default for GenericTypeGatherer<T> {
    fn default() -> Self {
        Self(Default::default())
    }
}

impl<T> GenericTypeGatherer<T> {
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

impl TypeGatherer {
    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn add(&mut self, t: Type) {
        debug_assert!(!t.is_never());
        debug_assert!(!matches!(t, Type::Union(_)));
        self.0.push(t)
    }

    pub fn add_with_uniqueness_check(&mut self, t: Type) {
        if !self.0.contains(&t) {
            self.add(t)
        }
    }

    pub(crate) fn add_all_union_entries(&mut self, type_: Type) {
        match type_ {
            Type::Never(_) => (),
            Type::Union(u) => self.0.extend(u.iter().cloned()),
            _ => self.add(type_),
        }
    }

    pub fn extend(&mut self, other: Self) {
        self.0.extend(other.0)
    }

    pub fn iter(&self) -> impl Iterator<Item = &Type> + Clone {
        self.0.iter()
    }

    pub fn into_type(self) -> Type {
        self.into_type_with_might_have_type_vars(true)
    }

    pub fn into_type_with_might_have_type_vars(self, might_have_type_vars: bool) -> Type {
        match self.0.len() {
            0 => Type::NEVER,
            1 => self.0.into_iter().next().unwrap(),
            _ => Type::Union(UnionType::from_types(
                self.0.into_iter(),
                might_have_type_vars,
            )),
        }
    }

    pub(crate) fn into_type_without_simple_duplicates(mut self) -> Type {
        let mut seen = FastHashSet::default();
        // Try to remove duplicates
        self.0.retain(|entry| seen.insert(entry.clone()));
        self.into_type_with_might_have_type_vars(true)
    }
}

impl FromIterator<Type> for TypeGatherer {
    fn from_iter<T: IntoIterator<Item = Type>>(iter: T) -> Self {
        Self(iter.into_iter().collect())
    }
}

impl From<Type> for TypeGatherer {
    fn from(t: Type) -> Self {
        Self(smallvec::smallvec![t])
    }
}

impl<'a> From<&'a Type> for Cow<'a, Type> {
    fn from(t: &'a Type) -> Self {
        Cow::Borrowed(t)
    }
}

impl<'a> From<Type> for Cow<'a, Type> {
    fn from(t: Type) -> Self {
        Cow::Owned(t)
    }
}

impl<'x> ComplexTypeGatherer<'x> {
    pub fn add(&mut self, t: impl Into<Cow<'x, Type>>) {
        self.0.push(t.into())
    }

    pub fn into_simplified_type(self, i_s: &InferenceState) -> Type {
        match self.0.len() {
            0 => Type::NEVER,
            1 => self.0.into_iter().next().unwrap().into_owned(),
            _ => Type::simplified_union_from_iterators(i_s, self.0.iter().map(|t| t.as_ref())),
        }
    }
}

pub type InferredTypeGatherer<'x> = GenericTypeGatherer<Inferred>;

impl<'x> InferredTypeGatherer<'x> {
    pub fn add(&mut self, t: Inferred) {
        self.0.push(t)
    }

    pub fn revert_order(&mut self) {
        self.0.reverse()
    }

    pub fn into_inferred(self, i_s: &InferenceState) -> Inferred {
        match self.0.len() {
            0 => Inferred::new_never(NeverCause::Other),
            1 => self.0.into_iter().next().unwrap(),
            _ => {
                let types: Vec<_> = self.0.iter().map(|inf| inf.as_cow_type(i_s)).collect();
                let simplified =
                    Type::simplified_union_from_iterators(i_s, types.iter().map(|t| t.as_ref()));
                // In the case where the type matches the first original simply return the first
                // original, because it might already be saved somewhere and we can simply reuse
                // it.
                if simplified == *types[0] {
                    self.0.into_iter().next().unwrap()
                } else {
                    Inferred::from_type(simplified)
                }
            }
        }
    }

    pub fn into_inferred_if_not_never(self, i_s: &InferenceState) -> Option<Inferred> {
        (!self.is_empty()).then(|| self.into_inferred(i_s))
    }
}
