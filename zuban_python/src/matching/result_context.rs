use std::fmt;

use super::Matcher;
use crate::{
    node_ref::NodeRef,
    type_::{AnyCause, TupleArgs, Type},
    type_helpers::Class,
    InferenceState,
};

pub enum ResultContext<'a, 'b> {
    Known(&'a Type),
    WithMatcher {
        matcher: &'a mut Matcher<'b>,
        type_: &'a Type,
    },
    AssignmentNewDefinition,
    Unknown,
    ExpectUnused,
    RevealType,
}

impl<'a> ResultContext<'a, '_> {
    pub fn with_type_if_exists_and_replace_type_var_likes<T>(
        &self,
        i_s: &InferenceState<'_, '_>,
        callable: impl FnOnce(&Type) -> T,
    ) -> Option<T> {
        match self {
            Self::Known(type_) => Some(callable(type_)),
            Self::WithMatcher { matcher, type_ } => {
                let t = matcher.replace_type_var_likes_for_nested_context(i_s.db, type_);
                Some(callable(&t))
            }
            Self::Unknown
            | Self::AssignmentNewDefinition
            | Self::ExpectUnused
            | Self::RevealType => None,
        }
    }

    pub fn with_type_if_exists<T>(
        &mut self,
        callable: impl FnOnce(&Type, &mut Matcher) -> T,
    ) -> Option<T> {
        match self {
            Self::Known(type_) => Some(callable(type_, &mut Matcher::default())),
            Self::WithMatcher { matcher, type_ } => Some(callable(type_, matcher)),
            Self::Unknown
            | Self::AssignmentNewDefinition
            | Self::ExpectUnused
            | Self::RevealType => None,
        }
    }

    pub fn on_unique_type_in_unpacked_union<'db, T>(
        &mut self,
        i_s: &InferenceState,
        class: NodeRef,
        on_unique_found: impl FnOnce(&mut Matcher, Matcher) -> T,
    ) -> Option<T> {
        self.with_type_if_exists(|t, matcher| {
            t.on_unique_type_in_unpacked_union(
                i_s.db,
                matcher,
                &|t| {
                    if matches!(t, Type::Any(_)) {
                        return None;
                    }
                    let c = Class::from_non_generic_node_ref(class);
                    let mut matcher = Matcher::new_class_matcher(i_s, c);
                    let self_class = Class::with_self_generics(i_s.db, class);
                    self_class
                        .as_type(i_s.db)
                        .is_sub_type_of(i_s, &mut matcher, t)
                        .bool()
                        .then_some(matcher)
                },
                on_unique_found,
            )
        })
        .flatten()
    }

    pub fn has_explicit_type(&self) -> bool {
        matches!(self, Self::Known(_) | Self::WithMatcher { .. })
    }

    pub fn could_be_a_literal(&self, i_s: &InferenceState<'_, '_>) -> CouldBeALiteral {
        if matches!(self, Self::AssignmentNewDefinition) && !i_s.is_calculating_enum_members() {
            return CouldBeALiteral::No;
        }
        self.with_type_if_exists_and_replace_type_var_likes(i_s, |type_| match type_ {
            Type::Literal(l) => CouldBeALiteral::Yes { implicit: false },
            Type::EnumMember(_) => CouldBeALiteral::Yes { implicit: false },
            Type::Union(items)
                if items
                    .iter()
                    .any(|i| matches!(i, Type::Literal(_) | Type::EnumMember(_))) =>
            {
                CouldBeALiteral::Yes { implicit: false }
            }
            _ => CouldBeALiteral::No,
        })
        .unwrap_or(CouldBeALiteral::Yes { implicit: true })
    }

    pub fn expects_union(&self, i_s: &InferenceState) -> bool {
        match self {
            Self::Known(type_) | Self::WithMatcher { type_, .. } => {
                matches!(type_, Type::Union(_))
            }
            Self::Unknown
            | Self::ExpectUnused
            | Self::RevealType
            | Self::AssignmentNewDefinition => false,
        }
    }

    pub fn expect_not_none(&mut self, i_s: &InferenceState) -> bool {
        self.with_type_if_exists(|type_, matcher| !matches!(type_, Type::None))
            .unwrap_or_else(|| !matches!(self, Self::ExpectUnused | Self::RevealType))
    }

    pub fn with_tuple_context_iterator<T>(
        &mut self,
        i_s: &InferenceState,
        mut callable: impl FnMut(TupleContextIterator) -> T,
    ) -> T {
        self.with_type_if_exists_and_replace_type_var_likes(i_s, |type_| {
            for t in type_.iter_with_unpacked_unions(i_s.db) {
                match t {
                    Type::Tuple(tup) => {
                        return Some(match &tup.args {
                            TupleArgs::FixedLen(ts) => {
                                callable(TupleContextIterator::FixedLen(ts.iter()))
                            }
                            TupleArgs::ArbitraryLen(t) => {
                                callable(TupleContextIterator::ArbitraryLen(t))
                            }
                            TupleArgs::WithUnpack(_) => callable(TupleContextIterator::Unknown),
                        })
                    }
                    // Case x: Iterable[int] = (1, 1)
                    Type::Class(c) if c.link == i_s.db.python_state.iterable_link() => {
                        let t = c.class(i_s.db).nth_type_argument(i_s.db, 0);
                        return Some(callable(TupleContextIterator::ArbitraryLen(&t)));
                    }
                    _ => (),
                }
            }
            None
        })
        .flatten()
        .unwrap_or_else(|| callable(TupleContextIterator::Unknown))
    }
}

impl fmt::Debug for ResultContext<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Known(t) => write!(f, "Known({t:?})"),
            Self::WithMatcher { type_, .. } => write!(f, "WithMatcher(_, {type_:?})"),
            Self::Unknown => write!(f, "Unknown"),
            Self::ExpectUnused => write!(f, "ExpectUnused"),
            Self::RevealType => write!(f, "RevealType"),
            Self::AssignmentNewDefinition => write!(f, "AssignmentNewDefinition"),
        }
    }
}

pub enum TupleContextIterator<'a> {
    ArbitraryLen(&'a Type),
    FixedLen(std::slice::Iter<'a, Type>),
    Unknown,
}

impl<'a> Iterator for TupleContextIterator<'a> {
    type Item = &'a Type;

    fn next(&mut self) -> Option<Self::Item> {
        Some(match self {
            Self::ArbitraryLen(t) => t,
            Self::FixedLen(items) => items.next().unwrap_or(&Type::Any(AnyCause::Todo)),
            Self::Unknown => &Type::Any(AnyCause::Todo),
        })
    }
}

#[derive(Debug)]
pub enum CouldBeALiteral {
    Yes { implicit: bool },
    No,
}
