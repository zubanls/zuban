use std::ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, Not};

use parsa_python_ast::{Expression, SliceContent, SliceIterator, SliceType, Slices};

use crate::database::{
    Database, DbType, FormatStyle, GenericsList, TypeVarIndex, TypeVarType, TypeVarUsage, TypeVars,
    Variance,
};
use crate::debug;
use crate::file::PythonFile;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::matcher::{FunctionOrCallable, TypeVarMatcher};
use crate::node_ref::NodeRef;
use crate::value::{CallableClass, Class, ClassLike, TupleClass};

pub enum SignatureMatch {
    False,
    FalseButSimilar,
    TrueWithAny(Vec<usize>),
    True,
}

#[derive(Copy, Clone, Debug)]
pub enum Match {
    False,
    FalseButSimilar,
    TrueWithAny,
    True,
}

impl Match {
    pub fn bool(self) -> bool {
        matches!(self, Self::True | Self::TrueWithAny)
    }
}

impl BitAnd for Match {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        match self {
            Self::True => rhs,
            Self::TrueWithAny => match rhs {
                Self::True => Self::TrueWithAny,
                _ => rhs,
            },
            Self::FalseButSimilar => match rhs {
                Self::False => Self::False,
                _ => self,
            },
            Self::False => Self::False,
        }
    }
}

impl BitOr for Match {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        match self {
            Self::True => Self::True,
            Self::TrueWithAny => match rhs {
                Self::True => Self::True,
                _ => Self::TrueWithAny,
            },
            Self::FalseButSimilar => match rhs {
                Self::True => Self::True,
                _ => self,
            },
            Self::False => rhs,
        }
    }
}

impl BitAndAssign for Match {
    fn bitand_assign(&mut self, rhs: Self) {
        *self = *self & rhs
    }
}

impl BitOrAssign for Match {
    fn bitor_assign(&mut self, rhs: Self) {
        *self = *self | rhs
    }
}

impl Not for Match {
    type Output = bool;

    fn not(self) -> Self::Output {
        !matches!(self, Self::True | Self::TrueWithAny)
    }
}

impl From<bool> for Match {
    fn from(item: bool) -> Self {
        match item {
            true => Match::True,
            _ => Match::False,
        }
    }
}

macro_rules! replace_class_vars {
    ($i_s:ident, $g:ident, $type_var_generics:ident) => {
        match $type_var_generics {
            None | Some(Generics::None) => $g.clone(),
            Some(type_var_generics) => $g.clone().replace_type_vars(&mut |t| {
                if t.type_ == TypeVarType::Class {
                    type_var_generics.nth($i_s, t.index)
                } else {
                    DbType::Unknown
                }
            }),
        }
    };
}

#[derive(Debug, Clone, Copy)]
pub enum Generics<'db, 'a> {
    SimpleGenericExpression(&'db PythonFile, Expression<'db>),
    SimpleGenericSlices(&'db PythonFile, Slices<'db>),
    List(&'a GenericsList, Option<&'a Generics<'db, 'a>>),
    Class(&'a Class<'db, 'a>),
    DbType(&'a DbType),
    None,
}

impl<'db, 'a> Generics<'db, 'a> {
    pub fn new_simple_generic_slice(file: &'db PythonFile, slice_type: SliceType<'db>) -> Self {
        match slice_type {
            SliceType::NamedExpression(named) => {
                Self::SimpleGenericExpression(file, named.expression())
            }
            SliceType::Slice(_) => unreachable!(),
            SliceType::Slices(slices) => Self::SimpleGenericSlices(file, slices),
        }
    }

    pub fn new_list(list: &'a GenericsList) -> Self {
        Self::List(list, None)
    }

    pub fn nth(&self, i_s: &mut InferenceState<'db, '_>, n: TypeVarIndex) -> DbType {
        match self {
            Self::SimpleGenericExpression(file, expr) => {
                if n.as_usize() == 0 {
                    file.inference(i_s)
                        .use_cached_simple_generic_type(*expr)
                        .into_db_type(i_s)
                } else {
                    debug!(
                        "Generic expr {:?} has one item, but {n:?} was requested",
                        expr.short_debug(),
                    );
                    todo!()
                }
            }
            Self::SimpleGenericSlices(file, slices) => slices
                .iter()
                .nth(n.as_usize())
                .map(|slice_content| match slice_content {
                    SliceContent::NamedExpression(n) => file
                        .inference(i_s)
                        .use_cached_simple_generic_type(n.expression())
                        .into_db_type(i_s),
                    SliceContent::Slice(s) => todo!(),
                })
                .unwrap_or_else(|| todo!()),
            Self::List(list, type_var_generics) => {
                if let Some(g) = list.nth(n) {
                    replace_class_vars!(i_s, g, type_var_generics)
                } else {
                    debug!(
                        "Generic list {} given, but item {n:?} was requested",
                        self.format(i_s, FormatStyle::Short, None),
                    );
                    todo!()
                }
            }
            Self::DbType(g) => {
                if n.as_usize() > 0 {
                    todo!()
                }
                (*g).clone()
            }
            Self::Class(s) => todo!(),
            Self::None => {
                debug!("No generics given, but {n:?} was requested");
                todo!()
            }
        }
    }

    pub fn iter(&self) -> GenericsIterator<'db, 'a> {
        match self {
            Self::SimpleGenericExpression(file, expr) => {
                GenericsIterator::SimpleGenericExpression(file, *expr)
            }
            Self::SimpleGenericSlices(file, slices) => {
                GenericsIterator::SimpleGenericSliceIterator(file, slices.iter())
            }
            Self::List(l, t) => GenericsIterator::GenericsList(l.iter(), *t),
            Self::DbType(g) => GenericsIterator::DbType(g),
            Self::Class(s) => GenericsIterator::Class(*s),
            Self::None => GenericsIterator::None,
        }
    }

    pub fn as_generics_list(&self, i_s: &mut InferenceState<'db, '_>) -> Option<GenericsList> {
        match self {
            Self::SimpleGenericExpression(file, expr) => {
                Some(GenericsList::new_generics(Box::new([file
                    .inference(i_s)
                    .use_cached_simple_generic_type(*expr)
                    .into_db_type(i_s)])))
            }
            Self::SimpleGenericSlices(file, slices) => Some(GenericsList::new_generics(
                slices
                    .iter()
                    .map(|slice| {
                        if let SliceContent::NamedExpression(n) = slice {
                            file.inference(i_s)
                                .use_cached_simple_generic_type(n.expression())
                                .into_db_type(i_s)
                        } else {
                            todo!()
                        }
                    })
                    .collect(),
            )),
            Self::DbType(g) => todo!(),
            Self::Class(_) => todo!(),
            Self::List(l, type_var_generics) => Some(GenericsList::new_generics(
                l.iter()
                    .map(|c| replace_class_vars!(i_s, c, type_var_generics))
                    .collect(),
            )),
            Self::None => None,
        }
    }

    pub fn format(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        style: FormatStyle,
        expected: Option<usize>,
    ) -> String {
        // Returns something like [str] or [List[int], Set[Any]]
        let mut strings = vec![];
        let mut i = 0;
        self.iter().run_on_all(i_s, &mut |i_s, g| {
            if expected.map(|e| i < e).unwrap_or(false) {
                strings.push(g.format(i_s, None, style));
                i += 1;
            }
        });
        if let Some(expected) = expected {
            for _ in i..expected {
                strings.push(Box::from("Any"));
            }
        }
        format!("[{}]", strings.join(", "))
    }

    pub fn matches(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        mut matcher: Option<&mut TypeVarMatcher<'db, '_>>,
        value_generics: Self,
        variance: Variance,
        type_vars: Option<&TypeVars>,
    ) -> Match {
        let mut value_generics = value_generics.iter();
        let mut matches = Match::True;
        let mut type_var_iterator = type_vars.map(|t| t.iter());
        self.iter().run_on_all(i_s, &mut |i_s, type_| {
            let appeared = value_generics.run_on_next(i_s, &mut |i_s, g| {
                let v = if let Some(t) = type_var_iterator.as_mut().and_then(|t| t.next()) {
                    match variance {
                        // TODO wtf this shouldn't be this way
                        Variance::Contravariant => Variance::Contravariant,
                        _ => t.variance,
                    }
                } else {
                    variance
                };
                matches &= type_.matches(i_s, matcher.as_deref_mut(), g, v);
            });
            if appeared.is_none() {
                debug!("Generic not found for: {type_:?}");
            }
        });
        matches
    }

    pub fn overlaps(
        self,
        i_s: &mut InferenceState<'db, '_>,
        other_generics: Self,
        type_vars: Option<&TypeVars>,
    ) -> bool {
        let mut other_generics = other_generics.iter();
        let mut matches = true;
        let mut type_var_iterator = type_vars.map(|t| t.iter());
        self.iter().run_on_all(i_s, &mut |i_s, type_| {
            let appeared = other_generics.run_on_next(i_s, &mut |i_s, g| {
                let xxx = if let Some(t) = type_var_iterator.as_mut().and_then(|t| t.next()) {
                    // TODO ?
                } else {
                };
                matches &= type_.overlaps(i_s, &g);
            });
            if appeared.is_none() {
                debug!("Overlap Generic not found for: {type_:?}");
                todo!();
            }
        });
        matches
    }
}

pub enum GenericsIterator<'db, 'a> {
    SimpleGenericSliceIterator(&'db PythonFile, SliceIterator<'db>),
    GenericsList(std::slice::Iter<'a, DbType>, Option<&'a Generics<'db, 'a>>),
    DbType(&'a DbType),
    Class(&'a Class<'db, 'a>),
    SimpleGenericExpression(&'db PythonFile, Expression<'db>),
    None,
}

impl<'db> GenericsIterator<'db, '_> {
    fn run_on_next<T>(
        &mut self,
        i_s: &mut InferenceState<'db, '_>,
        callable: &mut impl FnMut(&mut InferenceState<'db, '_>, Type<'db, '_>) -> T,
    ) -> Option<T> {
        match self {
            Self::SimpleGenericExpression(file, expr) => {
                let g = file.inference(i_s).use_cached_simple_generic_type(*expr);
                let result = callable(i_s, g);
                *self = Self::None;
                Some(result)
            }
            Self::SimpleGenericSliceIterator(file, iter) => {
                if let Some(SliceContent::NamedExpression(s)) = iter.next() {
                    let g = file
                        .inference(i_s)
                        .use_cached_simple_generic_type(s.expression());
                    Some(callable(i_s, g))
                } else {
                    None
                }
            }
            Self::GenericsList(iterator, type_var_generics) => iterator.next().map(|g| {
                let g = replace_class_vars!(i_s, g, type_var_generics);
                callable(i_s, Type::from_db_type(i_s.db, &g))
            }),
            Self::DbType(g) => {
                let result = Some(callable(i_s, Type::from_db_type(i_s.db, g)));
                *self = Self::None;
                result
            }
            Self::Class(s) => {
                let result = callable(i_s, Type::ClassLike(ClassLike::Class(**s)));
                *self = Self::None;
                Some(result)
            }
            Self::None => None,
        }
    }

    pub fn run_on_all(
        mut self,
        i_s: &mut InferenceState<'db, '_>,
        callable: &mut impl FnMut(&mut InferenceState<'db, '_>, Type<'db, '_>),
    ) {
        while self.run_on_next(i_s, callable).is_some() {}
    }
}

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
                    if let Some(function_matcher) = function_matcher {
                        if function_matcher.match_type == TypeVarType::LateBound {
                            if let Some(calculated) = function_matcher.nth(i_s, usage.index) {
                                return calculated;
                            }
                        }
                    }
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
