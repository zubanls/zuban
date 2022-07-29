use parsa_python_ast::{Expression, SliceContent, SliceIterator, SliceType, Slices};

use super::{ClassLike, Match, Type, TypeVarMatcher};
use crate::database::{
    DbType, FormatStyle, GenericsList, TypeVarIndex, TypeVarType, TypeVars, Variance,
};
use crate::debug;
use crate::file::PythonFile;
use crate::inference_state::InferenceState;
use crate::value::Class;

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
                matches &= type_.matches(i_s, matcher.as_deref_mut(), &g, v);
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
