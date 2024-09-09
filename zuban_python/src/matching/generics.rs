use parsa_python_cst::{Expression, SliceContent, SliceIterator, Slices};

use super::Generic;
use crate::{
    database::{Database, PointLink},
    debug,
    file::{use_cached_simple_generic_type, PythonFile},
    node_ref::NodeRef,
    type_::{
        ClassGenerics, GenericItem, GenericsList, Type, TypeVarLike, TypeVarLikeUsage, TypeVarLikes,
    },
};

macro_rules! replace_class_vars {
    ($db:expr, $g:ident, $type_var_generics:ident, $class_node_ref:expr) => {
        match $type_var_generics {
            None | Some(Generics::None | Generics::NotDefinedYet) => Generic::new($g),
            Some(type_var_generics) => Generic::owned($g.replace_type_var_likes_and_self(
                $db,
                &mut |t| {
                    type_var_generics
                        .nth_usage($db, &t, $class_node_ref)
                        .into_generic_item($db)
                },
                &|| Type::Self_,
            )),
        }
    };
}

#[derive(Debug, Clone, Copy)]
pub enum Generics<'a> {
    ExpressionWithClassType(&'a PythonFile, Expression<'a>),
    SlicesWithClassTypes(&'a PythonFile, Slices<'a>),
    // The remapping of type vars is done by List(). In a lot of
    // cases this is T -> T and S -> S, but it could also be T -> S and S
    // -> List[T] or something completely arbitrary. Therefore we have two generics.
    List(&'a GenericsList, Option<&'a Generics<'a>>),
    Self_ {
        class_definition: PointLink,
        type_var_likes: &'a TypeVarLikes,
    },
    None,
    NotDefinedYet,
}

impl<'a> Generics<'a> {
    pub fn new_list(list: &'a GenericsList) -> Self {
        Self::List(list, None)
    }

    pub fn from_class_generics(db: &'a Database, g: &'a ClassGenerics) -> Self {
        match g {
            ClassGenerics::List(l) => Self::List(l, None),
            ClassGenerics::None => Generics::None,
            ClassGenerics::ExpressionWithClassType(link) => {
                let node_ref = NodeRef::from_link(db, *link);
                Self::ExpressionWithClassType(node_ref.file, node_ref.as_expression())
            }
            ClassGenerics::SlicesWithClassTypes(link) => {
                let node_ref = NodeRef::from_link(db, *link);
                Self::SlicesWithClassTypes(node_ref.file, node_ref.as_slices())
            }
            ClassGenerics::NotDefinedYet => Generics::NotDefinedYet,
        }
    }

    pub fn nth_usage<'db: 'a>(
        &self,
        db: &'db Database,
        usage: &TypeVarLikeUsage,
        class_node_ref: NodeRef,
    ) -> Generic<'a> {
        self.nth(
            db,
            &usage.as_type_var_like(),
            usage.index().as_usize(),
            class_node_ref,
        )
    }

    pub fn nth<'db: 'a>(
        &self,
        db: &'db Database,
        type_var_like: &TypeVarLike,
        n: usize,
        class_node_ref: NodeRef,
    ) -> Generic<'a> {
        match self {
            Self::ExpressionWithClassType(file, expr) => {
                if n == 0 {
                    Generic::TypeArg(use_cached_simple_generic_type(db, file, *expr))
                } else {
                    debug!(
                        "Generic expr {:?} has one item, but {:?} was requested",
                        expr.short_debug(),
                        n,
                    );
                    todo!()
                }
            }
            Self::SlicesWithClassTypes(file, slices) => Generic::TypeArg(
                slices
                    .iter()
                    .nth(n)
                    .map(|slice_content| match slice_content {
                        SliceContent::NamedExpression(n) => {
                            use_cached_simple_generic_type(db, file, n.expression())
                        }
                        SliceContent::StarredExpression(n) => todo!(),
                        SliceContent::Slice(s) => todo!(),
                    })
                    .unwrap_or_else(|| todo!()),
            ),
            Self::List(list, type_var_generics) => {
                if let Some(g) = list.nth(n.into()) {
                    replace_class_vars!(db, g, type_var_generics, class_node_ref)
                } else {
                    unreachable!("Generic list given, but item {:?} was requested", n);
                }
            }
            Self::NotDefinedYet => Generic::owned(type_var_like.as_any_generic_item()),
            Self::Self_ {
                class_definition, ..
            } => Generic::owned(
                type_var_like
                    .as_type_var_like_usage(
                        n.into(),
                        *class_definition, /*class_node_ref.as_link()*/
                    )
                    .into_generic_item(),
            ),
            Self::None => unreachable!("No generics given, but {:?} was requested", n),
        }
    }

    pub fn iter<'x>(&self, db: &'x Database, class_node_ref: NodeRef<'x>) -> GenericsIterator<'x>
    where
        'a: 'x,
    {
        let item = match self {
            Self::ExpressionWithClassType(file, expr) => {
                GenericsIteratorItem::SimpleGenericExpression(file, *expr)
            }
            Self::SlicesWithClassTypes(file, slices) => {
                GenericsIteratorItem::SimpleGenericSliceIterator(file, slices.iter())
            }
            Self::List(l, t) => GenericsIteratorItem::GenericsList(l.iter(), *t),
            Self::Self_ {
                class_definition,
                type_var_likes,
            } => GenericsIteratorItem::TypeVarLikeIterator {
                iterator: type_var_likes.iter().enumerate(),
                definition: *class_definition,
            },
            Self::None | Self::NotDefinedYet => GenericsIteratorItem::None,
        };
        GenericsIterator::new(db, item, class_node_ref)
    }
}

pub struct GenericsIterator<'a> {
    db: &'a Database,
    ended: bool,
    class_node_ref: NodeRef<'a>,
    item: GenericsIteratorItem<'a>,
}

impl<'a> GenericsIterator<'a> {
    fn new(db: &'a Database, item: GenericsIteratorItem<'a>, class_node_ref: NodeRef<'a>) -> Self {
        Self {
            db,
            ended: false,
            item,
            class_node_ref,
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
                .map(|g| replace_class_vars!(self.db, g, type_var_generics, self.class_node_ref)),
            GenericsIteratorItem::TypeVarLikeIterator {
                iterator,
                definition,
            } => iterator.next().map(|(i, t)| {
                Generic::owned(
                    t.as_type_var_like_usage(i.into(), *definition)
                        .into_generic_item(),
                )
            }),
            GenericsIteratorItem::None => None,
        }
    }
}
