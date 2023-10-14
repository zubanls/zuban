use std::borrow::Cow;
use std::rc::Rc;

use crate::database::{Database, TypeAlias};

use crate::type_::{
    DbType, GenericItem, GenericsList, ParamSpecUsage, RecursiveAlias, TypeVarLike,
    TypeVarLikeUsage, TypeVarTupleUsage, TypeVarUsage,
};

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum LookupKind {
    Normal,
    // In CPython there is PyTypeObject (for documentation see CPython's `Doc/c-api/typeobj.rst`).
    // This type object is used to access __and__, when a user types `int & int`. Note that int
    // defines __and__ as well, but the type of int does not, hence it should lead to an error.
    OnlyType,
}

#[derive(Debug, Clone)]
#[allow(clippy::enum_variant_names)]
pub struct Type<'a>(pub Cow<'a, DbType>);

impl<'x> From<&'x DbType> for Type<'x> {
    fn from(item: &'x DbType) -> Self {
        Self(Cow::Borrowed(item))
    }
}

impl From<DbType> for Type<'static> {
    fn from(item: DbType) -> Self {
        Self(Cow::Owned(item))
    }
}

impl std::ops::Deref for Type<'_> {
    type Target = DbType;

    fn deref(&self) -> &Self::Target {
        self.0.as_ref()
    }
}

impl<'a> Type<'a> {
    pub fn new(t: &'a DbType) -> Self {
        Self(Cow::Borrowed(t))
    }

    pub fn owned(t: DbType) -> Self {
        Self(Cow::Owned(t))
    }

    pub fn into_cow(self) -> Cow<'a, DbType> {
        self.0
    }

    pub fn into_db_type(self) -> DbType {
        self.0.into_owned()
    }

    pub fn as_db_type(&self) -> DbType {
        self.0.as_ref().clone()
    }

    pub fn as_ref(&self) -> &DbType {
        self
    }
}

impl TypeAlias {
    pub fn as_db_type_and_set_type_vars_any(&self, db: &Database) -> DbType {
        if self.is_recursive() {
            return DbType::RecursiveAlias(Rc::new(RecursiveAlias::new(
                self.location,
                (!self.type_vars.is_empty()).then(|| {
                    GenericsList::new_generics(
                        self.type_vars
                            .iter()
                            .map(|tv| tv.as_any_generic_item())
                            .collect(),
                    )
                }),
            )));
        }
        let db_type = self.db_type_if_valid();
        if self.type_vars.is_empty() {
            db_type.clone()
        } else {
            Type::new(db_type).replace_type_var_likes(db, &mut |t| match t.in_definition()
                == self.location
            {
                true => t.as_type_var_like().as_any_generic_item(),
                false => t.into_generic_item(),
            })
        }
    }

    pub fn replace_type_var_likes(
        &self,
        db: &Database,
        remove_recursive_wrapper: bool,
        callable: &mut impl FnMut(TypeVarLikeUsage) -> GenericItem,
    ) -> Cow<DbType> {
        if self.is_recursive() && !remove_recursive_wrapper {
            return Cow::Owned(DbType::RecursiveAlias(Rc::new(RecursiveAlias::new(
                self.location,
                (!self.type_vars.is_empty()).then(|| {
                    GenericsList::new_generics(
                        self.type_vars
                            .iter()
                            .enumerate()
                            .map(|(i, type_var_like)| match type_var_like {
                                TypeVarLike::TypeVar(type_var) => {
                                    callable(TypeVarLikeUsage::TypeVar(Cow::Owned(TypeVarUsage {
                                        type_var: type_var.clone(),
                                        index: i.into(),
                                        in_definition: self.location,
                                    })))
                                }
                                TypeVarLike::TypeVarTuple(t) => callable(
                                    TypeVarLikeUsage::TypeVarTuple(Cow::Owned(TypeVarTupleUsage {
                                        type_var_tuple: t.clone(),
                                        index: i.into(),
                                        in_definition: self.location,
                                    })),
                                ),
                                TypeVarLike::ParamSpec(p) => callable(TypeVarLikeUsage::ParamSpec(
                                    Cow::Owned(ParamSpecUsage {
                                        param_spec: p.clone(),
                                        index: i.into(),
                                        in_definition: self.location,
                                    }),
                                )),
                            })
                            .collect(),
                    )
                }),
            ))));
        }
        let db_type = self.db_type_if_valid();
        if self.type_vars.is_empty() {
            Cow::Borrowed(db_type)
        } else {
            Cow::Owned(Type::new(db_type).replace_type_var_likes(db, callable))
        }
    }
}

impl RecursiveAlias {
    pub fn calculated_db_type<'db: 'slf, 'slf>(&'slf self, db: &'db Database) -> &'slf DbType {
        let alias = self.type_alias(db);
        if self.generics.is_none() {
            alias.db_type_if_valid()
        } else {
            self.calculated_db_type.get_or_init(|| {
                self.type_alias(db)
                    .replace_type_var_likes(db, true, &mut |t| {
                        self.generics
                            .as_ref()
                            .map(|g| g.nth(t.index()).unwrap().clone())
                            .unwrap()
                    })
                    .into_owned()
            })
        }
    }
}
