use core::fmt;

use crate::{
    InferenceState,
    database::PointLink,
    file::ClassNodeRef,
    matching::Matcher,
    type_::{AnyCause, TupleArgs, Type, UniqueInUnpackedUnionError},
    type_helpers::Class,
};

pub(crate) enum ResultContext<'a, 'b> {
    Known {
        type_: &'a Type,
        origin: ResultContextOrigin,
    },
    KnownLambdaReturn(&'a Type),
    WithMatcher {
        matcher: &'a mut Matcher<'b>,
        type_: &'a Type,
    },
    AssignmentNewDefinition {
        assignment_definition: PointLink,
    },
    ValueExpected,
    Unknown,
    ExpectUnused,
    Await,
    RevealType,
}

#[derive(Debug)]
pub(crate) enum ResultContextOrigin {
    AssignmentAnnotation,
    NormalAssignment,
    Other,
}

impl<'a> ResultContext<'a, '_> {
    pub fn new_known(type_: &'a Type) -> Self {
        Self::Known {
            type_,
            origin: ResultContextOrigin::Other,
        }
    }

    pub fn with_type_if_exists_and_replace_type_var_likes<T>(
        &self,
        i_s: &InferenceState<'_, '_>,
        callable: impl FnOnce(&Type) -> T,
    ) -> Option<T> {
        match self {
            Self::Known { type_, .. } | Self::KnownLambdaReturn(type_) => Some(callable(type_)),
            Self::WithMatcher { matcher, type_ } => {
                let t = matcher.replace_type_var_likes_for_nested_context(i_s.db, type_);
                Some(callable(&t))
            }
            Self::ValueExpected
            | Self::Unknown
            | Self::AssignmentNewDefinition { .. }
            | Self::ExpectUnused
            | Self::RevealType
            | Self::Await => None,
        }
    }

    pub fn with_type_if_exists<T>(
        &mut self,
        callable: impl FnOnce(&Type, &mut Matcher) -> T,
    ) -> Option<T> {
        match self {
            Self::Known { type_, .. } | Self::KnownLambdaReturn(type_) => {
                Some(callable(type_, &mut Matcher::default()))
            }
            Self::WithMatcher { matcher, type_ } => Some(callable(type_, matcher)),
            Self::ValueExpected
            | Self::Unknown
            | Self::AssignmentNewDefinition { .. }
            | Self::ExpectUnused
            | Self::RevealType
            | Self::Await => None,
        }
    }

    pub fn on_unique_type_in_unpacked_union<T>(
        &mut self,
        i_s: &InferenceState,
        class: ClassNodeRef,
        on_unique_found: impl FnOnce(&mut Matcher, Matcher) -> T,
    ) -> Option<Result<T, UniqueInUnpackedUnionError>> {
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
    }

    pub fn has_explicit_type(&self) -> bool {
        matches!(self, Self::Known { .. } | Self::WithMatcher { .. })
    }

    pub fn could_be_a_literal(&self, i_s: &InferenceState<'_, '_>) -> CouldBeALiteral {
        if matches!(self, Self::AssignmentNewDefinition { .. })
            && !i_s.is_calculating_enum_members()
        {
            return CouldBeALiteral::No;
        }
        self.with_type_if_exists_and_replace_type_var_likes(i_s, Type::could_be_a_literal)
            .unwrap_or(CouldBeALiteral::Yes { implicit: true })
    }

    pub fn expect_not_none(&mut self) -> bool {
        match self {
            Self::ExpectUnused | Self::RevealType | Self::KnownLambdaReturn(_) | Self::Unknown => {
                false
            }
            Self::Known { type_, .. } | Self::WithMatcher { type_, .. } => {
                !matches!(type_, Type::None)
            }
            Self::AssignmentNewDefinition { .. } | Self::ValueExpected | Self::Await => true,
        }
    }

    pub fn with_tuple_context_iterator<T>(
        &mut self,
        i_s: &InferenceState,
        mut callable: impl FnMut(TupleContextIterator) -> T,
    ) -> T {
        self.with_type_if_exists_and_replace_type_var_likes(i_s, |t| {
            t.on_unique_type_in_unpacked_union(
                i_s.db,
                &mut Matcher::default(),
                &|t| {
                    if matches!(t, Type::Tuple(_)) {
                        return Some(t.clone());
                    }
                    t.is_simple_super_type_of(i_s, &i_s.db.python_state.bare_tuple_type_with_any())
                        .bool()
                        .then_some(t.clone())
                },
                |_matcher, wanted_tuple| {
                    match wanted_tuple {
                        Type::Tuple(tup) => {
                            return Some(match &tup.args {
                                TupleArgs::FixedLen(ts) => {
                                    callable(TupleContextIterator::FixedLen(ts.iter()))
                                }
                                TupleArgs::ArbitraryLen(t) => {
                                    callable(TupleContextIterator::ArbitraryLen(t))
                                }
                                TupleArgs::WithUnpack(_) => callable(TupleContextIterator::Unknown),
                            });
                        }
                        // Case x: Iterable[int] = (1, 1)
                        Type::Class(c) if c.link == i_s.db.python_state.iterable_link() => {
                            let t = c.class(i_s.db).nth_type_argument(i_s.db, 0);
                            return Some(callable(TupleContextIterator::ArbitraryLen(&t)));
                        }
                        _ => (),
                    }
                    None
                },
            )
            .ok()
        })
        .flatten()
        .flatten()
        .unwrap_or_else(|| callable(TupleContextIterator::Unknown))
    }

    pub fn is_annotation_assignment(&self) -> bool {
        matches!(
            self,
            ResultContext::Known {
                origin: ResultContextOrigin::AssignmentAnnotation,
                ..
            }
        )
    }

    pub fn can_be_redefined(&self, i_s: &InferenceState) -> bool {
        matches!(
            self,
            ResultContext::Known {
                origin: ResultContextOrigin::NormalAssignment,
                ..
            }
        ) && i_s.flags().allow_redefinition
    }

    pub fn expects_type_form(&mut self) -> bool {
        self.with_type_if_exists(|t, _| matches!(t, Type::TypeForm(_)))
            .unwrap_or_default()
    }
}

impl fmt::Debug for ResultContext<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Known { type_: t, origin } => {
                write!(f, "Known {{ type_: {t:?}, origin: {origin:?}}}")
            }
            Self::KnownLambdaReturn(t) => write!(f, "KnownLambdaReturn({t:?})"),
            Self::WithMatcher { type_, .. } => write!(f, "WithMatcher(_, {type_:?})"),
            Self::ValueExpected => write!(f, "ValueExpected"),
            Self::Unknown => write!(f, "Unknown"),
            Self::ExpectUnused => write!(f, "ExpectUnused"),
            Self::RevealType => write!(f, "RevealType"),
            Self::AssignmentNewDefinition { .. } => write!(f, "AssignmentNewDefinition"),
            Self::Await => write!(f, "Await"),
        }
    }
}

pub(crate) enum TupleContextIterator<'a> {
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
pub(crate) enum CouldBeALiteral {
    Yes { implicit: bool },
    No,
}

impl Type {
    pub fn could_be_a_literal(&self) -> CouldBeALiteral {
        match self {
            Type::Literal(_) | Type::LiteralString { .. } | Type::EnumMember(_) => {
                CouldBeALiteral::Yes { implicit: false }
            }
            Type::Union(items) => {
                for t in items.iter() {
                    if let x @ CouldBeALiteral::Yes { .. } = t.could_be_a_literal() {
                        return x;
                    }
                }
                CouldBeALiteral::No
            }
            _ => CouldBeALiteral::No,
        }
    }
}
