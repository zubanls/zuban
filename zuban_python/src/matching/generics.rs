use parsa_python_ast::{Expression, SliceContent, SliceIterator, SliceType, Slices};

use super::{FormatData, Generic, Match, Matcher, Type};
use crate::database::{
    DbType, GenericItem, GenericsList, TypeVarLike, TypeVarLikeUsage, TypeVarLikes, Variance,
};
use crate::debug;
use crate::file::PythonFile;
use crate::inference_state::InferenceState;

macro_rules! replace_class_vars {
    ($i_s:expr, $g:ident, $type_var_generics:ident) => {
        match $type_var_generics {
            None | Some(Generics::None | Generics::Any) => Generic::new($g),
            Some(type_var_generics) => Generic::owned($g.replace_type_vars(&mut |t| {
                type_var_generics.nth_usage($i_s, t).into_generic_item($i_s)
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

    pub fn nth_usage<'db: 'a>(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        usage: TypeVarLikeUsage,
    ) -> Generic<'a> {
        self.nth(i_s, usage.as_type_var_like(), usage.index().as_usize())
    }

    pub fn nth<'db: 'a>(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        type_var_like: TypeVarLike,
        n: usize,
    ) -> Generic<'a> {
        match self {
            Self::SimpleGenericExpression(file, expr) => {
                if n == 0 {
                    Generic::TypeArgument(file.inference(i_s).use_cached_simple_generic_type(*expr))
                } else {
                    debug!(
                        "Generic expr {:?} has one item, but {:?} was requested",
                        expr.short_debug(),
                        n,
                    );
                    todo!()
                }
            }
            Self::SimpleGenericSlices(file, slices) => Generic::TypeArgument(
                slices
                    .iter()
                    .nth(n)
                    .map(|slice_content| match slice_content {
                        SliceContent::NamedExpression(n) => file
                            .inference(i_s)
                            .use_cached_simple_generic_type(n.expression()),
                        SliceContent::Slice(s) => todo!(),
                    })
                    .unwrap_or_else(|| todo!()),
            ),
            Self::List(list, type_var_generics) => {
                if let Some(g) = list.nth(n.into()) {
                    replace_class_vars!(i_s, g, type_var_generics)
                } else {
                    debug!(
                        "Generic list {} given, but item {:?} was requested",
                        self.format(&FormatData::new_short(i_s.db), None),
                        n,
                    );
                    todo!()
                }
            }
            Self::DbType(g) => {
                if n > 0 {
                    todo!()
                }
                // TODO TypeVarTuple is this correct?
                Generic::TypeArgument(Type::owned((*g).clone()))
            }
            Self::Any => Generic::owned(type_var_like.as_any_generic_item()),
            Self::None => unreachable!("No generics given, but {:?} was requested", n),
        }
    }

    pub fn iter<'x, 'y>(&'y self, i_s: InferenceState<'x, 'y>) -> GenericsIterator<'x, 'y> {
        GenericsIterator::new(
            i_s,
            match self {
                Self::SimpleGenericExpression(file, expr) => {
                    GenericsIteratorItem::SimpleGenericExpression(file, *expr)
                }
                Self::SimpleGenericSlices(file, slices) => {
                    GenericsIteratorItem::SimpleGenericSliceIterator(file, slices.iter())
                }
                Self::List(l, t) => GenericsIteratorItem::GenericsList(l.iter(), *t),
                Self::DbType(g) => GenericsIteratorItem::DbType(g),
                Self::None | Self::Any => GenericsIteratorItem::None,
            },
        )
    }

    pub fn as_generics_list(
        &self,
        i_s: &mut InferenceState,
        type_vars: Option<&TypeVarLikes>,
    ) -> Option<GenericsList> {
        type_vars.map(|type_vars| match self {
            Self::SimpleGenericExpression(file, expr) => {
                GenericsList::new_generics(Box::new([GenericItem::TypeArgument(
                    file.inference(i_s)
                        .use_cached_simple_generic_type(*expr)
                        .into_db_type(i_s),
                )]))
            }
            Self::SimpleGenericSlices(file, slices) => GenericsList::new_generics(
                slices
                    .iter()
                    .map(|slice| {
                        if let SliceContent::NamedExpression(n) = slice {
                            GenericItem::TypeArgument(
                                file.inference(i_s)
                                    .use_cached_simple_generic_type(n.expression())
                                    .into_db_type(i_s),
                            )
                        } else {
                            todo!()
                        }
                    })
                    .collect(),
            ),
            Self::DbType(g) => todo!(),
            Self::List(l, type_var_generics) => GenericsList::new_generics(
                l.iter()
                    .map(|c| replace_class_vars!(i_s, c, type_var_generics).into_generic_item(i_s))
                    .collect(),
            ),
            Self::Any => GenericsList::new_generics(
                type_vars.iter().map(|t| t.as_any_generic_item()).collect(),
            ),
            Self::None => unreachable!(),
        })
    }

    pub fn format(&self, format_data: &FormatData, expected: Option<usize>) -> String {
        // Returns something like [str] or [List[int], Set[Any]]
        let mut strings: Vec<_> = self
            .iter(InferenceState::new(format_data.db))
            .map(|g| g.format(format_data))
            .collect();
        if let Some(expected) = expected {
            if strings.len() != expected {
                // TODO this should probably never happen and we should assert this
            }
            strings.resize_with(expected, || Box::from("Any"))
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
        let value_generics = value_generics.iter(i_s.clone());
        let mut matches = Match::new_true();
        for ((t1, t2), tv) in self
            .iter(i_s.clone())
            .zip(value_generics)
            .zip(type_vars.iter())
        {
            let v = match tv {
                TypeVarLike::TypeVar(t) => t.variance,
                TypeVarLike::TypeVarTuple(_) => Variance::Invariant,
                TypeVarLike::ParamSpec(_) => todo!(),
            };
            matches &= t1.matches(i_s, matcher, t2, v);
        }
        matches
    }

    pub fn overlaps(
        self,
        i_s: &mut InferenceState,
        other_generics: Self,
        type_vars: Option<&TypeVarLikes>,
    ) -> bool {
        let other_generics = other_generics.iter(i_s.clone());
        let mut matches = true;
        let mut type_var_iterator = type_vars.map(|t| t.iter());
        for (t1, t2) in self.iter(i_s.clone()).zip(other_generics) {
            if let Some(t) = type_var_iterator.as_mut().and_then(|t| t.next()) {
                // TODO ?
            } else {
            };
            matches &= t1.overlaps(i_s, t2);
        }
        matches
    }
}

pub struct GenericsIterator<'a, 'b> {
    i_s: InferenceState<'a, 'b>,
    ended: bool,
    item: GenericsIteratorItem<'b>,
}

impl<'a, 'b> GenericsIterator<'a, 'b> {
    fn new(i_s: InferenceState<'a, 'b>, item: GenericsIteratorItem<'b>) -> Self {
        Self {
            i_s,
            ended: false,
            item,
        }
    }
}

enum GenericsIteratorItem<'a> {
    SimpleGenericSliceIterator(&'a PythonFile, SliceIterator<'a>),
    GenericsList(std::slice::Iter<'a, GenericItem>, Option<&'a Generics<'a>>),
    DbType(&'a DbType),
    SimpleGenericExpression(&'a PythonFile, Expression<'a>),
    None,
}

impl<'b> Iterator for GenericsIterator<'_, 'b> {
    type Item = Generic<'b>;

    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.item {
            GenericsIteratorItem::SimpleGenericExpression(file, expr) => {
                if self.ended {
                    return None;
                }
                self.ended = true;
                Some(Generic::TypeArgument(
                    file.inference(&mut self.i_s)
                        .use_cached_simple_generic_type(*expr),
                ))
            }
            GenericsIteratorItem::SimpleGenericSliceIterator(file, iter) => {
                if let Some(SliceContent::NamedExpression(s)) = iter.next() {
                    Some(Generic::TypeArgument(
                        file.inference(&mut self.i_s)
                            .use_cached_simple_generic_type(s.expression()),
                    ))
                } else {
                    None
                }
            }
            GenericsIteratorItem::GenericsList(iterator, type_var_generics) => iterator
                .next()
                .map(|g| replace_class_vars!(&mut self.i_s, g, type_var_generics)),
            GenericsIteratorItem::DbType(g) => {
                if self.ended {
                    return None;
                }
                self.ended = true;
                Some(Generic::TypeArgument(Type::new(g)))
            }
            GenericsIteratorItem::None => None,
        }
    }
}
