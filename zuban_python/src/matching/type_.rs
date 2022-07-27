use super::{ClassLike, FunctionOrCallable, Generics, Match, TypeVarMatcher};
use crate::database::{
    Database, DbType, FormatStyle, GenericsList, TypeVarType, TypeVarUsage, Variance,
};
use crate::debug;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::node_ref::NodeRef;
use crate::value::{CallableClass, Class, TupleClass};

#[derive(Debug, Clone)]
#[allow(clippy::enum_variant_names)]
pub enum Type<'db, 'a> {
    ClassLike(ClassLike<'db, 'a>),
    Union(Vec<DbType>),
    Any,
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
            DbType::Any | DbType::Unknown => Type::Any,
            DbType::Never => Self::ClassLike(ClassLike::Never),
            DbType::GenericClass(link, generics) => {
                let node_ref = NodeRef::from_link(db, *link);
                Self::ClassLike(ClassLike::Class(
                    Class::from_position(node_ref, Generics::new_list(generics), None).unwrap(),
                ))
            }
            DbType::Union(list) => Self::Union(list.iter().cloned().collect()),
            DbType::TypeVar(t) => Self::ClassLike(ClassLike::TypeVar(t)),
            DbType::Type(db_type) => Self::ClassLike(ClassLike::TypeWithDbType(db_type)),
            DbType::Tuple(content) => Self::ClassLike(ClassLike::Tuple(TupleClass::new(content))),
            DbType::Callable(content) => {
                Self::ClassLike(ClassLike::Callable(CallableClass::new(db_type, content)))
            }
        }
    }

    pub fn union(self, i_s: &mut InferenceState<'db, '_>, other: Self) -> Self {
        if let Self::Union(mut list1) = self {
            if let Self::Union(list2) = other {
                list1.extend(list2);
            } else {
                list1.push(other.into_db_type(i_s));
            }
            Self::Union(list1)
        } else if let Self::Union(_) = other {
            other.union(i_s, self)
        } else {
            Type::Union(vec![self.into_db_type(i_s), other.into_db_type(i_s)])
        }
    }

    pub fn into_db_type(self, i_s: &mut InferenceState<'db, '_>) -> DbType {
        match self {
            Self::ClassLike(class_like) => class_like.as_db_type(i_s),
            Self::Union(list) => DbType::Union(GenericsList::generics_from_vec(list)),
            Self::Any => DbType::Any,
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
            },
            Self::Union(list1) => list1
                .iter()
                .any(|t| Type::from_db_type(i_s.db, t).overlaps(i_s, other)),
            Self::Any => true,
        }
    }

    pub fn matches(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        mut matcher: Option<&mut TypeVarMatcher<'db, '_>>,
        value_class: Self,
        variance: Variance,
    ) -> Match {
        match self {
            Self::ClassLike(class) => class.matches(i_s, value_class, matcher, variance),
            Self::Union(list1) => match value_class {
                // TODO this should use the variance argument
                Self::Union(mut list2) => match variance {
                    Variance::Covariant | Variance::Invariant => {
                        let mut type_var_usage = None;
                        for g1 in list1 {
                            if let Some(t) = g1.maybe_type_var_index() {
                                type_var_usage = Some(t);
                            }
                            for (i, g2) in list2.iter().enumerate() {
                                if Type::from_db_type(i_s.db, g1)
                                    .matches(
                                        i_s,
                                        matcher.as_deref_mut(),
                                        Type::from_db_type(i_s.db, g2),
                                        variance,
                                    )
                                    .bool()
                                {
                                    list2.remove(i);
                                    break;
                                }
                            }
                        }
                        /*
                        if type_var_usage.is_some() {
                                Type::from_db_type(i_s.db, g1).matches(
                                    i_s,
                                    matcher,
                                    Type::from_db_type(i_s.db, g2),
                                );
                        }*/
                        if let Some(type_var_usage) = type_var_usage {
                            if let Some(matcher) = matcher {
                                let g = match list2.len() {
                                    0 => unreachable!(),
                                    1 => Type::from_db_type(i_s.db, &list2[0]),
                                    _ => Type::Union(list2),
                                };
                                matcher.match_or_add_type_var(i_s, type_var_usage, g)
                            } else {
                                Match::True
                            }
                        } else {
                            list2.is_empty().into()
                        }
                    }
                    Variance::Contravariant => list1
                        .iter()
                        .all(|g1| {
                            let t1 = Type::from_db_type(i_s.db, g1);
                            list2.iter().any(|g2| {
                                t1.matches(
                                    i_s,
                                    matcher.as_deref_mut(),
                                    Type::from_db_type(i_s.db, g2),
                                    variance,
                                )
                                .bool()
                            })
                        })
                        .into(),
                },
                _ => match variance {
                    Variance::Contravariant => Match::False,
                    Variance::Covariant | Variance::Invariant => list1
                        .iter()
                        .any(|g| {
                            Type::from_db_type(i_s.db, g)
                                .matches(i_s, matcher.as_deref_mut(), value_class.clone(), variance)
                                .bool()
                        })
                        .into(),
                },
            },
            Self::Any => match value_class {
                Self::Any => Match::TrueWithAny,
                _ => Match::True,
            },
        }
    }

    pub fn error_if_not_matches<'x>(
        &self,
        i_s: &mut InferenceState<'db, 'x>,
        mut matcher: Option<&mut TypeVarMatcher<'db, '_>>,
        value: &Inferred<'db>,
        mut callback: impl FnMut(&mut InferenceState<'db, 'x>, Box<str>, Box<str>),
    ) -> Match {
        let value_type = value.class_as_type(i_s);
        let matches = self.matches(i_s, matcher.as_deref_mut(), value_type, Variance::Covariant);
        if !matches {
            let class = matcher.and_then(|matcher| match &matcher.func_or_callable {
                FunctionOrCallable::Function(_, func) => func.class.as_ref(),
                FunctionOrCallable::Callable(_) => None,
            });
            let value_type = value.class_as_type(i_s);
            debug!("Mismatch between {value_type:?} and {self:?}");
            let input = value_type.format(i_s, None, FormatStyle::Short);
            let wanted = self.format(i_s, class, FormatStyle::Short);
            callback(i_s, input, wanted)
        }
        matches
    }

    pub fn execute_and_resolve_type_vars(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        class: Option<&Class<'db, '_>>,
        function_matcher: Option<&mut TypeVarMatcher<'db, '_>>,
    ) -> Inferred<'db> {
        let db_type = self.internal_resolve_type_vars(i_s, class, function_matcher);
        debug!(
            "Resolved type vars: {}",
            db_type.format(i_s.db, None, FormatStyle::Short)
        );
        Inferred::execute_db_type(i_s, db_type)
    }

    fn internal_resolve_type_vars(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        class: Option<&Class<'db, '_>>,
        mut function_matcher: Option<&mut TypeVarMatcher<'db, '_>>,
    ) -> DbType {
        let resolve_type_var = |i_s: &mut InferenceState<'db, '_>,
                                function_matcher: Option<&mut TypeVarMatcher<'db, '_>>,
                                usage: &TypeVarUsage| {
            match usage.type_ {
                TypeVarType::Class => {
                    if let Some(c) = class {
                        c.generics().nth(i_s, usage.index)
                    } else {
                        // TODO we are just passing the type vars again. Does this make sense?
                        DbType::TypeVar(usage.clone())
                    }
                }
                TypeVarType::Function => {
                    if let Some(fm) = function_matcher {
                        fm.nth(i_s, usage.index).unwrap_or_else(|| unreachable!())
                    } else {
                        // TODO we are just passing the type vars again. Does this make sense?
                        DbType::TypeVar(usage.clone())
                    }
                }
                TypeVarType::LateBound => {
                    // Just pass the type var again, because it might be resolved by a future
                    // callable, that is late bound, like Callable[..., Callable[[T], T]]
                    DbType::TypeVar(usage.clone())
                }
                _ => unreachable!(),
            }
        };

        match self {
            Self::ClassLike(c) => c.as_db_type(i_s).replace_type_vars(&mut |t| {
                resolve_type_var(i_s, function_matcher.as_deref_mut(), t)
            }),
            Self::Union(list) => DbType::Union(GenericsList::new_union(
                list.iter()
                    .map(|g| {
                        g.clone().replace_type_vars(&mut |t| {
                            resolve_type_var(i_s, function_matcher.as_deref_mut(), t)
                        })
                    })
                    .collect(),
            )),
            Self::Any => DbType::Any,
        }
    }

    pub fn format(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        class: Option<&Class<'db, '_>>,
        style: FormatStyle,
    ) -> Box<str> {
        match self {
            Self::ClassLike(c) => c.format(i_s, class, style),
            Self::Union(list) => list
                .iter()
                .fold(String::new(), |a, b| {
                    if a.is_empty() {
                        a + &b.format(i_s.db, None, style)
                    } else {
                        a + " | " + &b.format(i_s.db, None, style)
                    }
                })
                .into(),
            Self::Any => Box::from("Any"),
        }
    }
}
