use parsa_python_cst::{Expression, SliceContent, SliceIterator, Slices};

use super::Generic;
use crate::{
    database::{Database, PointLink},
    file::{use_cached_simple_generic_type, ClassNodeRef, PythonFile},
    node_ref::NodeRef,
    type_::{ClassGenerics, GenericItem, GenericsList, TypeVarLike, TypeVarLikeUsage},
};

macro_rules! replace_class_vars {
    ($db:expr, $g:ident, $type_var_generics:ident) => {
        match $type_var_generics {
            None | Some(Generics::None) => Generic::new($g),
            Some(type_var_generics) => Generic::owned(
                $g.replace_type_var_likes_and_self(
                    $db,
                    &mut |t| Some(type_var_generics.nth_usage($db, &t).into_generic_item()),
                    &|| None,
                )
                .unwrap_or($g.clone()),
            ),
        }
    };
}

#[derive(Debug, Clone, Copy)]
pub(crate) enum Generics<'a> {
    ExpressionWithClassType(&'a PythonFile, Expression<'a>),
    SlicesWithClassTypes(&'a PythonFile, Slices<'a>),
    // The remapping of type vars is done by List(). In a lot of
    // cases this is T -> T and S -> S, but it could also be T -> S and S
    // -> List[T] or something completely arbitrary. Therefore we have two generics.
    List(&'a GenericsList, Option<&'a Generics<'a>>),
    Self_ { class_ref: ClassNodeRef<'a> },
    None,
    NotDefinedYet { class_ref: ClassNodeRef<'a> },
}

impl<'a> Generics<'a> {
    pub fn from_class_generics(
        db: &'a Database,
        class_ref: ClassNodeRef<'a>,
        g: &'a ClassGenerics,
    ) -> Self {
        match g {
            ClassGenerics::List(l) => Self::List(l, None),
            ClassGenerics::None => Generics::None,
            ClassGenerics::ExpressionWithClassType(link) => {
                let node_ref = NodeRef::from_link(db, *link);
                Self::ExpressionWithClassType(node_ref.file, node_ref.expect_expression())
            }
            ClassGenerics::SlicesWithClassTypes(link) => {
                let node_ref = NodeRef::from_link(db, *link);
                Self::SlicesWithClassTypes(node_ref.file, node_ref.expect_slices())
            }
            ClassGenerics::NotDefinedYet => Generics::NotDefinedYet { class_ref },
        }
    }

    pub fn nth_usage<'db: 'a>(&self, db: &'db Database, usage: &TypeVarLikeUsage) -> Generic<'a> {
        self.nth(db, usage.index().as_usize())
    }

    pub fn nth<'db: 'a>(&self, db: &'db Database, n: usize) -> Generic<'a> {
        match self {
            Self::ExpressionWithClassType(file, expr) => {
                debug_assert_eq!(n, 0);
                Generic::TypeArg(use_cached_simple_generic_type(db, file, *expr))
            }
            Self::SlicesWithClassTypes(file, slices) => Generic::TypeArg(
                slices
                    .iter()
                    .nth(n)
                    .map(|slice_content| match slice_content {
                        SliceContent::NamedExpression(n) => {
                            use_cached_simple_generic_type(db, file, n.expression())
                        }
                        _ => unreachable!(),
                    })
                    .unwrap(),
            ),
            Self::List(list, type_var_generics) => {
                if let Some(g) = list.nth(n.into()) {
                    replace_class_vars!(db, g, type_var_generics)
                } else {
                    unreachable!("Generic list given, but item {:?} was requested", n);
                }
            }
            Self::NotDefinedYet { class_ref } => {
                let type_var_like = &class_ref.use_cached_type_vars(db)[n];
                Generic::owned(type_var_like.as_any_generic_item(db))
            }
            Self::Self_ { class_ref } => Generic::owned(
                class_ref.use_cached_type_vars(db)[n]
                    .as_type_var_like_usage(n.into(), class_ref.as_link())
                    .into_generic_item(),
            ),
            Self::None => unreachable!("No generics given, but {:?} was requested", n),
        }
    }

    pub fn iter<'x>(&'x self, db: &'x Database) -> GenericsIterator<'x> {
        let item = match self {
            Self::ExpressionWithClassType(file, expr) => {
                GenericsIteratorItem::SimpleGenericExpression(file, *expr)
            }
            Self::SlicesWithClassTypes(file, slices) => {
                GenericsIteratorItem::SimpleGenericSliceIterator(file, slices.iter())
            }
            Self::List(l, t) => GenericsIteratorItem::GenericsList(l.iter(), *t),
            Self::Self_ { class_ref } => GenericsIteratorItem::TypeVarLikeIterator {
                iterator: class_ref.use_cached_type_vars(db).iter().enumerate(),
                definition: class_ref.as_link(),
            },
            Self::NotDefinedYet { class_ref } => {
                let type_vars = class_ref.use_cached_type_vars(db);
                GenericsIteratorItem::AnyTypeVars(type_vars.iter())
            }
            Self::None => GenericsIteratorItem::None,
        };
        GenericsIterator::new(db, item)
    }
}

pub(crate) struct GenericsIterator<'a> {
    db: &'a Database,
    ended: bool,
    item: GenericsIteratorItem<'a>,
}

impl<'a> GenericsIterator<'a> {
    fn new(db: &'a Database, item: GenericsIteratorItem<'a>) -> Self {
        Self {
            db,
            ended: false,
            item,
        }
    }
}

enum GenericsIteratorItem<'a> {
    SimpleGenericSliceIterator(&'a PythonFile, SliceIterator<'a>),
    GenericsList(std::slice::Iter<'a, GenericItem>, Option<&'a Generics<'a>>),
    SimpleGenericExpression(&'a PythonFile, Expression<'a>),
    TypeVarLikeIterator {
        iterator: std::iter::Enumerate<std::slice::Iter<'a, TypeVarLike>>,
        definition: PointLink,
    },
    AnyTypeVars(std::slice::Iter<'a, TypeVarLike>),
    None,
}

impl<'a> Iterator for GenericsIterator<'a> {
    type Item = Generic<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.item {
            GenericsIteratorItem::SimpleGenericExpression(file, expr) => {
                if self.ended {
                    return None;
                }
                self.ended = true;
                Some(Generic::TypeArg(use_cached_simple_generic_type(
                    self.db, file, *expr,
                )))
            }
            GenericsIteratorItem::SimpleGenericSliceIterator(file, iter) => {
                if let Some(SliceContent::NamedExpression(s)) = iter.next() {
                    Some(Generic::TypeArg(use_cached_simple_generic_type(
                        self.db,
                        file,
                        s.expression(),
                    )))
                } else {
                    None
                }
            }
            GenericsIteratorItem::GenericsList(iterator, type_var_generics) => iterator
                .next()
                .map(|g| replace_class_vars!(self.db, g, type_var_generics)),
            GenericsIteratorItem::TypeVarLikeIterator {
                iterator,
                definition,
            } => iterator.next().map(|(i, t)| {
                Generic::owned(
                    t.as_type_var_like_usage(i.into(), *definition)
                        .into_generic_item(),
                )
            }),
            GenericsIteratorItem::AnyTypeVars(type_var_likes) => Some(Generic::owned(
                type_var_likes.next()?.as_any_generic_item(self.db),
            )),
            GenericsIteratorItem::None => None,
        }
    }
}
