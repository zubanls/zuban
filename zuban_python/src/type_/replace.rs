use std::{borrow::Cow, rc::Rc};

use crate::{
    database::{Database, PointLink},
    inference_state::InferenceState,
};

use super::{
    simplified_union_from_iterators, CallableContent, CallableParam, CallableParams, ClassGenerics,
    Dataclass, DoubleStarredParamSpecific, GenericClass, GenericItem, GenericsList, NamedTuple,
    ParamSpecArgument, ParamSpecTypeVars, ParamSpecific, RecursiveAlias, StarredParamSpecific,
    Tuple, TupleTypeArguments, Type, TypeArguments, TypeOrTypeVarTuple, TypeVarLike,
    TypeVarLikeUsage, TypeVarLikes, TypeVarManager, TypedDict, TypedDictGenerics, UnionEntry,
    UnionType,
};

pub type ReplaceTypeVarLike<'x> = &'x mut dyn FnMut(TypeVarLikeUsage) -> GenericItem;
pub type ReplaceSelf<'x> = &'x dyn Fn() -> Type;

impl Type {
    pub fn replace_type_var_likes(
        &self,
        db: &Database,
        callable: &mut impl FnMut(TypeVarLikeUsage) -> GenericItem,
    ) -> Type {
        self.replace_type_var_likes_and_self(db, callable, &|| Type::Self_)
    }

    pub fn replace_type_var_likes_and_self(
        &self,
        db: &Database,
        callable: ReplaceTypeVarLike,
        replace_self: ReplaceSelf,
    ) -> Type {
        let replace_tuple_likes = |args: &TupleTypeArguments,
                                   callable: ReplaceTypeVarLike,
                                   replace_self: ReplaceSelf| {
            match args {
                TupleTypeArguments::FixedLength(ts) => {
                    let mut new_args = vec![];
                    for g in ts.iter() {
                        match g {
                            TypeOrTypeVarTuple::Type(t) => new_args.push(TypeOrTypeVarTuple::Type(
                                t.replace_type_var_likes_and_self(db, callable, replace_self),
                            )),
                            TypeOrTypeVarTuple::TypeVarTuple(t) => {
                                match callable(TypeVarLikeUsage::TypeVarTuple(Cow::Borrowed(t))) {
                                    GenericItem::TypeArguments(new) => {
                                        match new.args {
                                            TupleTypeArguments::FixedLength(fixed) => {
                                                // Performance issue: clone could probably be removed. Rc -> Vec check
                                                // https://github.com/rust-lang/rust/issues/93610#issuecomment-1528108612
                                                new_args.extend(fixed.iter().cloned())
                                            }
                                            TupleTypeArguments::ArbitraryLength(t) => {
                                                match ts.len() {
                                                    // TODO this might be wrong with different data types??
                                                    1 => {
                                                        return TupleTypeArguments::ArbitraryLength(
                                                            t,
                                                        )
                                                    }
                                                    _ => todo!(),
                                                }
                                            }
                                        }
                                    }
                                    x => unreachable!("{x:?}"),
                                }
                            }
                        }
                    }
                    TupleTypeArguments::FixedLength(new_args.into())
                }
                TupleTypeArguments::ArbitraryLength(t) => TupleTypeArguments::ArbitraryLength(
                    Box::new(t.replace_type_var_likes_and_self(db, callable, replace_self)),
                ),
            }
        };
        let mut replace_generics = |generics: &GenericsList| {
            GenericsList::new_generics(
                generics
                    .iter()
                    .map(|g| match g {
                        GenericItem::TypeArgument(t) => GenericItem::TypeArgument(
                            t.replace_type_var_likes_and_self(db, callable, replace_self),
                        ),
                        GenericItem::TypeArguments(ts) => {
                            GenericItem::TypeArguments(TypeArguments {
                                args: replace_tuple_likes(&ts.args, callable, replace_self),
                            })
                        }
                        GenericItem::ParamSpecArgument(p) => {
                            let mut type_vars = p.type_vars.clone().map(|t| t.type_vars.as_vec());
                            GenericItem::ParamSpecArgument(ParamSpecArgument::new(
                                Self::replace_callable_param_type_var_likes_and_self(
                                    db,
                                    &p.params,
                                    &mut type_vars,
                                    p.type_vars.as_ref().map(|t| t.in_definition),
                                    callable,
                                    replace_self,
                                )
                                .0,
                                type_vars.map(|t| ParamSpecTypeVars {
                                    type_vars: TypeVarLikes::from_vec(t),
                                    in_definition: p.type_vars.as_ref().unwrap().in_definition,
                                }),
                            ))
                        }
                    })
                    .collect(),
            )
        };
        match self {
            Type::Any(cause) => Type::Any(*cause),
            Type::None => Type::None,
            Type::Never => Type::Never,
            Type::Class(c) => Type::new_class(c.link, c.generics.map_list(replace_generics)),
            Type::FunctionOverload(overload) => {
                Type::FunctionOverload(overload.map_functions(|functions| {
                    functions
                        .iter()
                        .map(|c| {
                            Self::replace_type_var_likes_and_self_for_callable(
                                c,
                                db,
                                callable,
                                replace_self,
                            )
                        })
                        .collect()
                }))
            }
            Type::Union(u) => {
                let new_entries = u
                    .entries
                    .iter()
                    .map(|u| {
                        (
                            u.format_index,
                            u.type_
                                .replace_type_var_likes_and_self(db, callable, replace_self),
                        )
                    })
                    .collect::<Vec<_>>();
                let i_s = InferenceState::new(db);
                let highest_union_format_index = new_entries
                    .iter()
                    .map(|e| e.1.highest_union_format_index())
                    .max()
                    .unwrap();
                simplified_union_from_iterators(
                    &i_s,
                    new_entries.into_iter(),
                    highest_union_format_index,
                    u.format_as_optional,
                )
            }
            Type::TypeVar(t) => match callable(TypeVarLikeUsage::TypeVar(Cow::Borrowed(&t))) {
                GenericItem::TypeArgument(t) => t,
                GenericItem::TypeArguments(ts) => unreachable!(),
                GenericItem::ParamSpecArgument(params) => todo!(),
            },
            Type::Type(t) => Type::Type(Rc::new(t.replace_type_var_likes_and_self(
                db,
                callable,
                replace_self,
            ))),
            Type::Tuple(content) => Type::Tuple(Rc::new(Tuple::new(replace_tuple_likes(
                &content.args,
                callable,
                replace_self,
            )))),
            Type::Callable(content) => {
                Type::Callable(Rc::new(Self::replace_type_var_likes_and_self_for_callable(
                    &content,
                    db,
                    callable,
                    replace_self,
                )))
            }
            Type::Literal { .. } => self.clone(),
            Type::NewType(t) => Type::NewType(t.clone()),
            Type::RecursiveAlias(rec) => Type::RecursiveAlias(Rc::new(RecursiveAlias::new(
                rec.link,
                rec.generics.as_ref().map(replace_generics),
            ))),
            Type::Module(file_index) => Type::Module(*file_index),
            Type::Namespace(namespace) => Type::Namespace(namespace.clone()),
            Type::Self_ => replace_self(),
            Type::ParamSpecArgs(usage) => todo!(),
            Type::ParamSpecKwargs(usage) => todo!(),
            Type::Dataclass(d) => Type::Dataclass({
                if matches!(d.class.generics, ClassGenerics::List(_)) {
                    Dataclass::new(
                        GenericClass {
                            link: d.class.link,
                            generics: d.class.generics.map_list(replace_generics),
                        },
                        d.options,
                    )
                } else {
                    d.clone()
                }
            }),
            Type::TypedDict(td) => {
                let generics = match &td.generics {
                    TypedDictGenerics::None => TypedDictGenerics::None,
                    TypedDictGenerics::NotDefinedYet(tvs) => {
                        TypedDictGenerics::NotDefinedYet(tvs.clone())
                    }
                    TypedDictGenerics::Generics(generics) => {
                        TypedDictGenerics::Generics(replace_generics(generics))
                    }
                };
                Type::TypedDict(TypedDict::new(
                    td.name,
                    td.members
                        .iter()
                        .map(|m| {
                            m.replace_type(|t| {
                                t.replace_type_var_likes_and_self(db, callable, replace_self)
                            })
                        })
                        .collect(),
                    td.defined_at,
                    generics,
                ))
            }
            Type::NamedTuple(nt) => {
                let mut constructor = nt.__new__.as_ref().clone();
                constructor.params = CallableParams::Simple(
                    constructor
                        .expect_simple_params()
                        .iter()
                        .map(|param| {
                            let ParamSpecific::PositionalOrKeyword(t) = &param.param_specific else {
                                return param.clone()
                            };
                            CallableParam {
                                param_specific: ParamSpecific::PositionalOrKeyword(
                                    t.replace_type_var_likes_and_self(db, callable, replace_self),
                                ),
                                has_default: param.has_default,
                                name: param.name.clone(),
                            }
                        })
                        .collect(),
                );
                Type::NamedTuple(Rc::new(NamedTuple::new(nt.name, constructor)))
            }
            t @ (Type::Enum(_) | Type::EnumMember(_)) => t.clone(),
            Type::Super { .. } => todo!(),
            Type::CustomBehavior(_) => todo!(),
        }
    }

    pub fn replace_type_var_likes_and_self_for_callable(
        c: &CallableContent,
        db: &Database,
        callable: ReplaceTypeVarLike,
        replace_self: ReplaceSelf,
    ) -> CallableContent {
        let has_type_vars = !c.type_vars.is_empty();
        let mut type_vars = has_type_vars.then(|| c.type_vars.clone().as_vec());
        let (params, remap_data) = Self::replace_callable_param_type_var_likes_and_self(
            db,
            &c.params,
            &mut type_vars,
            Some(c.defined_at),
            callable,
            replace_self,
        );
        let mut result_type =
            c.result_type
                .replace_type_var_likes_and_self(db, callable, replace_self);
        if let Some(remap_data) = remap_data {
            result_type = result_type.replace_type_var_likes_and_self(
                db,
                &mut |usage| {
                    Self::replace_param_spec_inner_type_var_likes_and_self(
                        usage,
                        c.defined_at,
                        remap_data,
                    )
                },
                replace_self,
            );
        }
        CallableContent {
            name: c.name.clone(),
            class_name: c.class_name,
            defined_at: c.defined_at,
            kind: c.kind,
            type_vars: type_vars
                .map(TypeVarLikes::from_vec)
                .unwrap_or_else(|| db.python_state.empty_type_var_likes.clone()),
            params,
            result_type,
        }
    }

    fn rewrite_late_bound_callables_for_callable(
        c: &CallableContent,
        manager: &TypeVarManager,
    ) -> CallableContent {
        let type_vars = manager
            .iter()
            .filter_map(|t| {
                (t.most_outer_callable == Some(c.defined_at)).then(|| t.type_var_like.clone())
            })
            .collect::<Rc<_>>();
        CallableContent {
            name: c.name.clone(),
            class_name: c.class_name,
            defined_at: c.defined_at,
            kind: c.kind,
            type_vars: TypeVarLikes::new(type_vars),
            params: match &c.params {
                CallableParams::Simple(params) => CallableParams::Simple(
                    params
                        .iter()
                        .map(|p| CallableParam {
                            param_specific: match &p.param_specific {
                                ParamSpecific::PositionalOnly(t) => ParamSpecific::PositionalOnly(
                                    t.rewrite_late_bound_callables(manager),
                                ),
                                ParamSpecific::PositionalOrKeyword(t) => {
                                    ParamSpecific::PositionalOrKeyword(
                                        t.rewrite_late_bound_callables(manager),
                                    )
                                }
                                ParamSpecific::KeywordOnly(t) => ParamSpecific::KeywordOnly(
                                    t.rewrite_late_bound_callables(manager),
                                ),
                                ParamSpecific::Starred(s) => ParamSpecific::Starred(match s {
                                    StarredParamSpecific::ArbitraryLength(t) => {
                                        StarredParamSpecific::ArbitraryLength(
                                            t.rewrite_late_bound_callables(manager),
                                        )
                                    }
                                    StarredParamSpecific::ParamSpecArgs(_) => todo!(),
                                }),
                                ParamSpecific::DoubleStarred(d) => {
                                    ParamSpecific::DoubleStarred(match d {
                                        DoubleStarredParamSpecific::ValueType(t) => {
                                            DoubleStarredParamSpecific::ValueType(
                                                t.rewrite_late_bound_callables(manager),
                                            )
                                        }
                                        DoubleStarredParamSpecific::ParamSpecKwargs(_) => {
                                            todo!()
                                        }
                                    })
                                }
                            },
                            has_default: p.has_default,
                            name: p.name.clone(),
                        })
                        .collect(),
                ),
                CallableParams::Any(cause) => CallableParams::Any(*cause),
                CallableParams::WithParamSpec(types, param_spec) => CallableParams::WithParamSpec(
                    types
                        .iter()
                        .map(|t| t.rewrite_late_bound_callables(manager))
                        .collect(),
                    manager.remap_param_spec(param_spec),
                ),
            },
            result_type: c.result_type.rewrite_late_bound_callables(manager),
        }
    }

    fn replace_callable_param_type_var_likes_and_self(
        db: &Database,
        params: &CallableParams,
        type_vars: &mut Option<Vec<TypeVarLike>>,
        in_definition: Option<PointLink>,
        callable: ReplaceTypeVarLike,
        replace_self: ReplaceSelf,
    ) -> (CallableParams, Option<(PointLink, usize)>) {
        let mut replace_data = None;
        let new_params = match params {
            CallableParams::Simple(params) => CallableParams::Simple(
                params
                    .iter()
                    .map(|p| CallableParam {
                        param_specific: match &p.param_specific {
                            ParamSpecific::PositionalOnly(t) => ParamSpecific::PositionalOnly(
                                t.replace_type_var_likes_and_self(db, callable, replace_self),
                            ),
                            ParamSpecific::PositionalOrKeyword(t) => {
                                ParamSpecific::PositionalOrKeyword(
                                    t.replace_type_var_likes_and_self(db, callable, replace_self),
                                )
                            }
                            ParamSpecific::KeywordOnly(t) => ParamSpecific::KeywordOnly(
                                t.replace_type_var_likes_and_self(db, callable, replace_self),
                            ),
                            ParamSpecific::Starred(s) => ParamSpecific::Starred(match s {
                                StarredParamSpecific::ArbitraryLength(t) => {
                                    StarredParamSpecific::ArbitraryLength(
                                        t.replace_type_var_likes_and_self(
                                            db,
                                            callable,
                                            replace_self,
                                        ),
                                    )
                                }
                                StarredParamSpecific::ParamSpecArgs(_) => todo!(),
                            }),
                            ParamSpecific::DoubleStarred(d) => {
                                ParamSpecific::DoubleStarred(match d {
                                    DoubleStarredParamSpecific::ValueType(t) => {
                                        DoubleStarredParamSpecific::ValueType(
                                            t.replace_type_var_likes_and_self(
                                                db,
                                                callable,
                                                replace_self,
                                            ),
                                        )
                                    }
                                    DoubleStarredParamSpecific::ParamSpecKwargs(_) => {
                                        todo!()
                                    }
                                })
                            }
                        },
                        has_default: p.has_default,
                        name: p.name.clone(),
                    })
                    .collect(),
            ),
            CallableParams::Any(cause) => CallableParams::Any(*cause),
            CallableParams::WithParamSpec(types, param_spec) => {
                let result = callable(TypeVarLikeUsage::ParamSpec(Cow::Borrowed(param_spec)));
                let GenericItem::ParamSpecArgument(mut new) = result else {
                    unreachable!()
                };
                if let Some(new_spec_type_vars) = new.type_vars {
                    if let Some(in_definition) = in_definition {
                        let type_var_len = type_vars.as_ref().map(|t| t.len()).unwrap_or(0);
                        replace_data = Some((new_spec_type_vars.in_definition, type_var_len));
                        let new_params = Self::replace_callable_param_type_var_likes_and_self(
                            db,
                            &new.params,
                            &mut None,
                            None,
                            &mut |usage| {
                                Self::replace_param_spec_inner_type_var_likes_and_self(
                                    usage,
                                    in_definition,
                                    replace_data.unwrap(),
                                )
                            },
                            replace_self,
                        );
                        if let Some(type_vars) = type_vars.as_mut() {
                            type_vars.extend(new_spec_type_vars.type_vars.as_vec());
                        } else {
                            *type_vars = Some(new_spec_type_vars.type_vars.as_vec());
                        }
                        new.params = new_params.0;
                    } else {
                        debug_assert!(type_vars.is_none());
                        *type_vars = Some(new_spec_type_vars.type_vars.as_vec());
                        todo!("Can probably just be removed")
                    }
                }
                if types.is_empty() {
                    new.params
                } else {
                    match new.params {
                        CallableParams::Simple(params) => {
                            // Performance issue: Rc -> Vec check https://github.com/rust-lang/rust/issues/93610#issuecomment-1528108612
                            let mut params = Vec::from(params.as_ref());
                            params.splice(
                                0..0,
                                types.iter().map(|t| CallableParam {
                                    param_specific: ParamSpecific::PositionalOnly(
                                        t.replace_type_var_likes_and_self(
                                            db,
                                            callable,
                                            replace_self,
                                        ),
                                    ),
                                    name: None,
                                    has_default: false,
                                }),
                            );
                            CallableParams::Simple(Rc::from(params))
                        }
                        CallableParams::Any(cause) => CallableParams::Any(cause),
                        CallableParams::WithParamSpec(new_types, p) => {
                            let mut types: Vec<Type> = types
                                .iter()
                                .map(|t| {
                                    t.replace_type_var_likes_and_self(db, callable, replace_self)
                                })
                                .collect();
                            // Performance issue: Rc -> Vec check https://github.com/rust-lang/rust/issues/93610#issuecomment-1528108612
                            types.extend(new_types.iter().cloned());
                            CallableParams::WithParamSpec(types.into(), p)
                        }
                    }
                }
            }
        };
        (new_params, replace_data)
    }

    fn replace_param_spec_inner_type_var_likes_and_self(
        mut usage: TypeVarLikeUsage,
        in_definition: PointLink,
        replace_data: (PointLink, usize),
    ) -> GenericItem {
        if usage.in_definition() == replace_data.0 {
            usage.update_in_definition_and_index(
                in_definition,
                (usage.index().as_usize() + replace_data.1).into(),
            );
        }
        usage.into_generic_item()
    }

    pub fn rewrite_late_bound_callables(&self, manager: &TypeVarManager) -> Type {
        let rewrite_generics = |generics: &GenericsList| {
            GenericsList::new_generics(
                generics
                    .iter()
                    .map(|g| match g {
                        GenericItem::TypeArgument(t) => {
                            GenericItem::TypeArgument(t.rewrite_late_bound_callables(manager))
                        }
                        GenericItem::TypeArguments(ts) => todo!(),
                        GenericItem::ParamSpecArgument(p) => GenericItem::ParamSpecArgument({
                            debug_assert!(p.type_vars.is_none());
                            ParamSpecArgument {
                                params: match &p.params {
                                    CallableParams::WithParamSpec(types, param_spec) => {
                                        CallableParams::WithParamSpec(
                                            types
                                                .iter()
                                                .map(|t| t.rewrite_late_bound_callables(manager))
                                                .collect(),
                                            manager.remap_param_spec(param_spec),
                                        )
                                    }
                                    CallableParams::Simple(x) => unreachable!(),
                                    CallableParams::Any(_) => unreachable!(),
                                },
                                type_vars: p.type_vars.clone(),
                            }
                        }),
                    })
                    .collect(),
            )
        };
        match self {
            Type::Any(cause) => Type::Any(*cause),
            Type::None => Type::None,
            Type::Never => Type::Never,
            Type::Class(c) => Type::Class(GenericClass {
                link: c.link,
                generics: c.generics.map_list(rewrite_generics),
            }),
            Type::Union(u) => Type::Union(UnionType {
                entries: u
                    .entries
                    .iter()
                    .map(|e| UnionEntry {
                        type_: e.type_.rewrite_late_bound_callables(manager),
                        format_index: e.format_index,
                    })
                    .collect(),
                format_as_optional: u.format_as_optional,
            }),
            Type::FunctionOverload(overload) => {
                Type::FunctionOverload(overload.map_functions(|functions| {
                    functions
                        .iter()
                        .map(|e| Self::rewrite_late_bound_callables_for_callable(e, manager))
                        .collect()
                }))
            }
            Type::TypeVar(t) => Type::TypeVar(manager.remap_type_var(t)),
            Type::Type(type_) => Type::Type(Rc::new(type_.rewrite_late_bound_callables(manager))),
            Type::Tuple(content) => Type::Tuple(match &content.args {
                TupleTypeArguments::FixedLength(ts) => Rc::new(Tuple::new_fixed_length(
                    ts.iter()
                        .map(|g| match g {
                            TypeOrTypeVarTuple::Type(t) => {
                                TypeOrTypeVarTuple::Type(t.rewrite_late_bound_callables(manager))
                            }
                            TypeOrTypeVarTuple::TypeVarTuple(t) => {
                                TypeOrTypeVarTuple::TypeVarTuple(manager.remap_type_var_tuple(t))
                            }
                        })
                        .collect(),
                )),
                TupleTypeArguments::ArbitraryLength(t) => Rc::new(Tuple::new_arbitrary_length(
                    t.rewrite_late_bound_callables(manager),
                )),
            }),
            Type::Literal { .. } => self.clone(),
            Type::Callable(content) => Type::Callable(Rc::new(
                Self::rewrite_late_bound_callables_for_callable(content, manager),
            )),
            Type::NewType(_) => todo!(),
            Type::RecursiveAlias(recursive_alias) => {
                Type::RecursiveAlias(Rc::new(RecursiveAlias::new(
                    recursive_alias.link,
                    recursive_alias.generics.as_ref().map(rewrite_generics),
                )))
            }
            Type::ParamSpecArgs(usage) => Type::ParamSpecArgs(manager.remap_param_spec(usage)),
            Type::ParamSpecKwargs(usage) => Type::ParamSpecKwargs(manager.remap_param_spec(usage)),
            Type::Dataclass(d) => Type::Dataclass(Dataclass::new(
                GenericClass {
                    link: d.class.link,
                    generics: d.class.generics.map_list(rewrite_generics),
                },
                d.options,
            )),
            Type::TypedDict(_) => todo!(),
            Type::NamedTuple(_) => todo!(),
            Type::Enum(_) => todo!(),
            Type::EnumMember(_) => todo!(),
            Type::Super { .. } => todo!(),
            t @ (Type::Module(_) | Type::Namespace(_) | Type::Self_ | Type::CustomBehavior(_)) => {
                t.clone()
            }
        }
    }
}

impl GenericItem {
    pub fn replace_type_var_likes(
        &self,
        db: &Database,
        callable: &mut impl FnMut(TypeVarLikeUsage) -> GenericItem,
        replace_self: ReplaceSelf,
    ) -> Self {
        match self {
            Self::TypeArgument(t) => {
                Self::TypeArgument(t.replace_type_var_likes_and_self(db, callable, replace_self))
            }
            Self::TypeArguments(_) => todo!(),
            Self::ParamSpecArgument(_) => todo!(),
        }
    }
}
