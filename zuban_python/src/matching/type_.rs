use std::borrow::Cow;

use super::{ClassLike, Generics, Match, MismatchReason, TypeVarMatcher};
use crate::database::{Database, DbType, FormatStyle, UnionEntry, UnionType, Variance};
use crate::debug;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::matching::CalculatedTypeArguments;
use crate::node_ref::NodeRef;
use crate::value::{Callable, Class, Tuple};

#[derive(Debug, Clone)]
#[allow(clippy::enum_variant_names)]
pub enum Type<'db, 'a> {
    ClassLike(ClassLike<'db, 'a>),
    Union(Cow<'a, UnionType>),
    Any,
    Never,
}

impl<'db, 'a> Type<'db, 'a> {
    pub fn from_db_type(db: &'db Database, db_type: &'a DbType) -> Self {
        match db_type {
            DbType::Class(link) => {
                let node_ref = NodeRef::from_link(db, *link);
                Self::ClassLike(ClassLike::Class(
                    Class::from_position(node_ref, Generics::None, None).unwrap(),
                ))
            }
            DbType::None => Self::ClassLike(ClassLike::None),
            DbType::Any => Type::Any,
            DbType::Never => Self::Never,
            DbType::GenericClass(link, generics) => {
                let node_ref = NodeRef::from_link(db, *link);
                Self::ClassLike(ClassLike::Class(
                    Class::from_position(node_ref, Generics::new_list(generics), None).unwrap(),
                ))
            }
            DbType::Union(union_type) => Self::Union(Cow::Borrowed(union_type)),
            DbType::TypeVar(t) => Self::ClassLike(ClassLike::TypeVar(t)),
            DbType::Type(db_type) => Self::ClassLike(ClassLike::TypeWithDbType(db_type)),
            DbType::Tuple(content) => Self::ClassLike(ClassLike::Tuple(Tuple::new(content))),
            DbType::Callable(content) => {
                Self::ClassLike(ClassLike::Callable(Callable::new(db_type, content)))
            }
        }
    }

    pub fn union(self, i_s: &mut InferenceState<'db, '_>, other: Self) -> Self {
        if matches!(self, Self::Union(_)) || matches!(other, Self::Union(_)) {
            let t = self.into_db_type(i_s).union(other.into_db_type(i_s));
            match t {
                DbType::Union(t) => Type::Union(Cow::Owned(t)),
                _ => unreachable!(),
            }
        } else {
            // If we have no union, the type might be exactly the same. In that case just return
            // self again.
            let t = self.as_db_type(i_s).union(other.into_db_type(i_s));
            match t {
                DbType::Union(t) => Type::Union(Cow::Owned(t)),
                _ => self,
            }
        }
    }

    pub fn into_db_type(self, i_s: &mut InferenceState<'db, '_>) -> DbType {
        match self {
            Self::ClassLike(class_like) => class_like.as_db_type(i_s),
            Self::Union(cow) => DbType::Union(cow.into_owned()),
            Self::Any => DbType::Any,
            Self::Never => DbType::Never,
        }
    }

    pub fn as_db_type(&self, i_s: &mut InferenceState<'db, '_>) -> DbType {
        match self {
            Self::ClassLike(class_like) => class_like.as_db_type(i_s),
            Self::Union(cow) => DbType::Union(cow.clone().into_owned()),
            Self::Any => DbType::Any,
            Self::Never => DbType::Never,
        }
    }

    pub fn overlaps(&self, i_s: &mut InferenceState<'db, '_>, other: &Self) -> bool {
        match self {
            Self::ClassLike(class1) => match other {
                Self::ClassLike(class2) => class1.overlaps(i_s, class2),
                Self::Union(list2) => list2
                    .iter()
                    .any(|t| self.overlaps(i_s, &Type::from_db_type(i_s.db, t))),
                Self::Any => false,
                Self::Never => todo!(),
            },
            Self::Union(list1) => list1
                .iter()
                .any(|t| Type::from_db_type(i_s.db, t).overlaps(i_s, other)),
            Self::Any => true,
            Self::Never => todo!(),
        }
    }

    pub fn matches(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        mut matcher: Option<&mut TypeVarMatcher<'db, '_>>,
        value_class: &Self,
        variance: Variance,
    ) -> Match {
        match self {
            Self::ClassLike(class) => class.matches(i_s, value_class, matcher, variance),
            Self::Union(list1) => match value_class {
                // TODO this should use the variance argument
                Self::Union(list2) => match variance {
                    Variance::Covariant | Variance::Invariant => {
                        let mut type_var_usage = None;
                        let mut matches = true;
                        for g2 in list2.iter() {
                            let t2 = Type::from_db_type(i_s.db, g2);
                            matches &= list1.iter().any(|g1| {
                                if let Some(t) = g1.maybe_type_var_index() {
                                    type_var_usage = Some(t);
                                }
                                Type::from_db_type(i_s.db, g1)
                                    .matches(i_s, matcher.as_deref_mut(), &t2, variance)
                                    .bool()
                            })
                        }
                        matches.into()
                    }
                    Variance::Contravariant => list1
                        .iter()
                        .all(|g1| {
                            let t1 = Type::from_db_type(i_s.db, g1);
                            list2.iter().any(|g2| {
                                t1.matches(
                                    i_s,
                                    matcher.as_deref_mut(),
                                    &Type::from_db_type(i_s.db, g2),
                                    variance,
                                )
                                .bool()
                            })
                        })
                        .into(),
                },
                _ => match variance {
                    Variance::Contravariant => Match::new_false(),
                    Variance::Covariant | Variance::Invariant => list1
                        .iter()
                        .any(|g| {
                            Type::from_db_type(i_s.db, g)
                                .matches(i_s, matcher.as_deref_mut(), value_class, variance)
                                .bool()
                        })
                        .into(),
                },
            },
            Self::Any => match value_class {
                Self::Any => Match::TrueWithAny,
                _ => Match::True,
            },
            Self::Never => todo!(),
        }
    }

    pub fn error_if_not_matches<'x>(
        &self,
        i_s: &mut InferenceState<'db, 'x>,
        value: &Inferred<'db>,
        mut callback: impl FnMut(&mut InferenceState<'db, 'x>, Box<str>, Box<str>),
    ) {
        self.error_if_not_matches_with_matcher(
            i_s,
            None,
            value,
            Some(
                |i_s: &mut InferenceState<'db, 'x>, t1, t2, reason: &MismatchReason| {
                    callback(i_s, t1, t2)
                },
            ),
        );
    }

    pub fn error_if_not_matches_with_matcher<'x>(
        &self,
        i_s: &mut InferenceState<'db, 'x>,
        mut matcher: Option<&mut TypeVarMatcher<'db, '_>>,
        value: &Inferred<'db>,
        callback: Option<
            impl FnMut(&mut InferenceState<'db, 'x>, Box<str>, Box<str>, &MismatchReason),
        >,
    ) -> Match {
        let value_type = value.class_as_type(i_s);
        let matches = self.matches(
            i_s,
            matcher.as_deref_mut(),
            &value_type,
            Variance::Covariant,
        );
        if let Match::False(ref reason) | Match::FalseButSimilar(ref reason) = matches {
            let value_type = value.class_as_type(i_s);
            debug!(
                "Mismatch between {value_type:?} and {self:?} -> {:?}",
                matches.clone()
            );
            let input = value_type.format(i_s, None, FormatStyle::Short);
            let wanted = self.format(i_s, matcher.as_deref(), FormatStyle::Short);
            if let Some(mut callback) = callback {
                callback(i_s, input, wanted, reason)
            }
        }
        matches
    }

    pub fn execute_and_resolve_type_vars(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        class: Option<&Class<'db, '_>>,
        calculated_type_args: &CalculatedTypeArguments,
    ) -> Inferred<'db> {
        let db_type = self.internal_resolve_type_vars(i_s, class, calculated_type_args);
        debug!(
            "Resolved type vars: {}",
            db_type.format(i_s, None, FormatStyle::Short)
        );
        Inferred::execute_db_type(i_s, db_type)
    }

    fn internal_resolve_type_vars(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        class: Option<&Class<'db, '_>>,
        calculated_type_args: &CalculatedTypeArguments,
    ) -> DbType {
        match self {
            Self::ClassLike(c) => c.as_db_type(i_s).replace_type_vars(&mut |t| {
                calculated_type_args.lookup_type_var_usage(i_s, class, t)
            }),
            Self::Union(list) => DbType::Union(UnionType::new(
                list.entries
                    .iter()
                    .map(|e| UnionEntry {
                        type_: e.type_.replace_type_vars(&mut |t| {
                            calculated_type_args.lookup_type_var_usage(i_s, class, t)
                        }),
                        format_index: e.format_index,
                    })
                    .collect(),
            )),
            Self::Any => DbType::Any,
            Self::Never => DbType::Never,
        }
    }

    pub fn any(
        &self,
        db: &'db Database,
        callable: &mut impl FnMut(&ClassLike<'db, '_>) -> bool,
    ) -> bool {
        match self {
            Self::ClassLike(class_like) => callable(class_like),
            Self::Union(union_type) => union_type
                .iter()
                .any(|t| Type::from_db_type(db, t).any(db, callable)),
            Self::Any => true,
            Self::Never => todo!(),
        }
    }

    pub fn common_base_class(&self, i_s: &mut InferenceState<'db, '_>, other: &Self) -> DbType {
        match (self, other) {
            (Self::ClassLike(ClassLike::Class(c1)), Self::ClassLike(ClassLike::Class(c2))) => {
                for (_, c1) in c1.mro(i_s) {
                    for (_, c2) in c2.mro(i_s) {
                        if c1
                            .matches(i_s, &Type::ClassLike(c2), None, Variance::Invariant)
                            .bool()
                        {
                            return c1.as_db_type(i_s);
                        }
                    }
                }
            }
            _ => return i_s.db.python_state.object_db_type(),
        }
        unreachable!("object is always a common base class")
    }

    pub fn format(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        matcher: Option<&TypeVarMatcher<'db, '_>>,
        style: FormatStyle,
    ) -> Box<str> {
        match self {
            Self::ClassLike(c) => c.format(i_s, matcher, style),
            Self::Union(list) => list.format(i_s, matcher, style),
            Self::Any => Box::from("Any"),
            Self::Never => Box::from("<nothing>"),
        }
    }
}
