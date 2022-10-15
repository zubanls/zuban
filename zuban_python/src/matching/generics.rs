use parsa_python_ast::{Expression, SliceContent, SliceIterator, SliceType, Slices};

use super::{FormatData, Match, Matcher, Type};
use crate::database::{DbType, GenericsList, TypeVarIndex, TypeVarLike, TypeVarLikes};
use crate::debug;
use crate::file::PythonFile;
use crate::inference_state::InferenceState;

macro_rules! replace_class_vars {
    ($i_s:ident, $g:ident, $type_var_generics:ident) => {
        match $type_var_generics {
            None | Some(Generics::None | Generics::Any) => Type::new($g),
            Some(type_var_generics) => Type::owned($g.replace_type_vars(&mut |t| {
                type_var_generics.nth($i_s, t.index).into_db_type($i_s)
            })),
        }
    };
}

#[derive(Debug, Clone, Copy)]
pub enum Generics<'a> {
    SimpleGenericExpression(&'a PythonFile, Expression<'a>),
    SimpleGenericSlices(&'a PythonFile, Slices<'a>),
    List(&'a GenericsList, Option<&'a Generics<'a>>),
    DbType(&'a DbType),
    None,
    Any,
}

impl<'a> Generics<'a> {
    pub fn new_simple_generic_slice(file: &'a PythonFile, slice_type: SliceType<'a>) -> Self {
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

    pub fn new_maybe_list(list: &'a Option<GenericsList>) -> Self {
        list.as_ref()
            .map(|l| Self::List(l, None))
            .unwrap_or(Generics::None)
    }

    pub fn nth<'db: 'a>(&self, i_s: &mut InferenceState<'db, '_>, n: TypeVarIndex) -> Type<'a> {
        match self {
            Self::SimpleGenericExpression(file, expr) => {
                if n.as_usize() == 0 {
                    file.inference(i_s).use_cached_simple_generic_type(*expr)
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
                        .use_cached_simple_generic_type(n.expression()),
                    SliceContent::Slice(s) => todo!(),
                })
                .unwrap_or_else(|| todo!()),
            Self::List(list, type_var_generics) => {
                if let Some(g) = list.nth(n) {
                    replace_class_vars!(i_s, g, type_var_generics)
                } else {
                    debug!(
                        "Generic list {} given, but item {n:?} was requested",
                        self.format(&FormatData::new_short(i_s.db), None),
                    );
                    todo!()
                }
            }
            Self::DbType(g) => {
                if n.as_usize() > 0 {
                    todo!()
                }
                Type::owned((*g).clone())
            }
            Self::Any => Type::new(&DbType::Any),
            Self::None => unreachable!("No generics given, but {n:?} was requested"),
        }
    }

    pub fn iter(&self) -> GenericsIterator<'a> {
        match self {
            Self::SimpleGenericExpression(file, expr) => {
                GenericsIterator::SimpleGenericExpression(file, *expr)
            }
            Self::SimpleGenericSlices(file, slices) => {
                GenericsIterator::SimpleGenericSliceIterator(file, slices.iter())
            }
            Self::List(l, t) => GenericsIterator::GenericsList(l.iter(), *t),
            Self::DbType(g) => GenericsIterator::DbType(g),
            Self::None | Self::Any => GenericsIterator::None,
        }
    }

    pub fn as_generics_list(
        &self,
        i_s: &mut InferenceState,
        type_vars: Option<&TypeVarLikes>,
    ) -> Option<GenericsList> {
        type_vars.map(|type_vars| match self {
            Self::SimpleGenericExpression(file, expr) => {
                GenericsList::new_generics(Box::new([file
                    .inference(i_s)
                    .use_cached_simple_generic_type(*expr)
                    .into_db_type(i_s)]))
            }
            Self::SimpleGenericSlices(file, slices) => GenericsList::new_generics(
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
            ),
            Self::DbType(g) => todo!(),
            Self::List(l, type_var_generics) => GenericsList::new_generics(
                l.iter()
                    .map(|c| replace_class_vars!(i_s, c, type_var_generics).into_db_type(i_s))
                    .collect(),
            ),
            Self::Any => GenericsList::new_generics(
                std::iter::repeat(DbType::Any)
                    .take(type_vars.len())
                    .collect(),
            ),
            Self::None => unreachable!(),
        })
    }

    pub fn format(&self, format_data: &FormatData, expected: Option<usize>) -> String {
        // Returns something like [str] or [List[int], Set[Any]]
        let mut strings = vec![];
        let mut i = 0;
        self.iter()
            .run_on_all(&mut InferenceState::new(format_data.db), &mut |i_s, g| {
                if expected.map(|e| i < e).unwrap_or(false) {
                    strings.push(g.format(format_data));
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
        i_s: &mut InferenceState,
        matcher: &mut Matcher,
        value_generics: Self,
        type_vars: &TypeVarLikes,
    ) -> Match {
        let mut value_generics = value_generics.iter();
        let mut matches = Match::new_true();
        let mut type_var_iterator = type_vars.iter();
        self.iter().run_on_all(i_s, &mut |i_s, type_| {
            let appeared = value_generics.run_on_next(i_s, &mut |i_s, g| {
                let v = match type_var_iterator.next().unwrap().as_ref() {
                    TypeVarLike::TypeVar(t) => t.variance,
                    TypeVarLike::TypeVarTuple(_) => todo!(),
                    TypeVarLike::ParamSpec(_) => todo!(),
                };
                matches &= type_.matches(i_s, matcher, &g, v);
            });
            if appeared.is_none() {
                debug!("Generic not found for: {type_:?}");
            }
        });
        matches
    }

    pub fn overlaps(
        self,
        i_s: &mut InferenceState,
        other_generics: Self,
        type_vars: Option<&TypeVarLikes>,
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

pub enum GenericsIterator<'a> {
    SimpleGenericSliceIterator(&'a PythonFile, SliceIterator<'a>),
    GenericsList(std::slice::Iter<'a, DbType>, Option<&'a Generics<'a>>),
    DbType(&'a DbType),
    SimpleGenericExpression(&'a PythonFile, Expression<'a>),
    None,
}

impl<'db> GenericsIterator<'_> {
    pub fn run_on_next<T>(
        &mut self,
        i_s: &mut InferenceState<'db, '_>,
        callable: &mut impl FnMut(&mut InferenceState<'db, '_>, Type) -> T,
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
                let t = replace_class_vars!(i_s, g, type_var_generics);
                callable(i_s, t)
            }),
            Self::DbType(g) => {
                let result = Some(callable(i_s, Type::new(g)));
                *self = Self::None;
                result
            }
            Self::None => None,
        }
    }

    pub fn run_on_all(
        mut self,
        i_s: &mut InferenceState<'db, '_>,
        callable: &mut impl FnMut(&mut InferenceState<'db, '_>, Type),
    ) {
        while self.run_on_next(i_s, callable).is_some() {}
    }
}
