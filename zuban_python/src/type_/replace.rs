use std::{borrow::Cow, rc::Rc};

use super::{
    simplified_union_from_iterators_with_format_index, CallableContent, CallableParam,
    CallableParams, ClassGenerics, Dataclass, GenericClass, GenericItem, GenericsList, NamedTuple,
    ParamSpecArg, ParamSpecTypeVars, ParamType, RecursiveType, StarParamType, StarStarParamType,
    Tuple, TupleArgs, Type, TypeArgs, TypeVarLike, TypeVarLikeUsage, TypeVarLikes, TypeVarManager,
    TypedDictGenerics, UnionEntry, UnionType,
};
use crate::{
    database::{Database, PointLink},
    inference_state::InferenceState,
    type_::{TupleUnpack, WithUnpack},
    utils::rc_slice_into_vec,
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
        let mut replace_generics = |generics: &GenericsList| {
            GenericsList::new_generics(
                generics
                    .iter()
                    .map(|g| match g {
                        GenericItem::TypeArg(t) => GenericItem::TypeArg(
                            t.replace_type_var_likes_and_self(db, callable, replace_self),
                        ),
                        GenericItem::TypeArgs(ts) => GenericItem::TypeArgs(TypeArgs {
                            args: ts.args.replace_type_var_likes_and_self(
                                db,
                                callable,
                                replace_self,
                            ),
                        }),
                        GenericItem::ParamSpecArg(p) => GenericItem::ParamSpecArg(
                            p.replace_type_var_likes_and_self(db, callable, replace_self),
                        ),
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
                        .map(|c| c.replace_type_var_likes_and_self(db, callable, replace_self))
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
                simplified_union_from_iterators_with_format_index(
                    &i_s,
                    new_entries.into_iter(),
                    highest_union_format_index,
                    u.format_as_optional,
                )
            }
            Type::TypeVar(t) => match callable(TypeVarLikeUsage::TypeVar(Cow::Borrowed(&t))) {
                GenericItem::TypeArg(t) => t,
                GenericItem::TypeArgs(ts) => unreachable!(),
                GenericItem::ParamSpecArg(params) => todo!(),
            },
            Type::Type(t) => Type::Type(Rc::new(t.replace_type_var_likes_and_self(
                db,
                callable,
                replace_self,
            ))),
            Type::Tuple(content) => Type::Tuple(Tuple::new(
                content
                    .args
                    .replace_type_var_likes_and_self(db, callable, replace_self),
            )),
            Type::Callable(c) => Type::Callable(Rc::new(c.replace_type_var_likes_and_self(
                db,
                callable,
                replace_self,
            ))),
            Type::Literal { .. } => self.clone(),
            Type::NewType(t) => Type::NewType(t.clone()),
            Type::RecursiveType(rec) => Type::RecursiveType(Rc::new(RecursiveType::new(
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
                Type::TypedDict(td.replace_type_var_likes_and_self(
                    db,
                    generics,
                    callable,
                    replace_self,
                ))
            }
            Type::NamedTuple(nt) => {
                let mut constructor = nt.__new__.as_ref().clone();
                constructor.params = CallableParams::Simple(
                    constructor
                        .expect_simple_params()
                        .iter()
                        .map(|param| {
                            let ParamType::PositionalOrKeyword(t) = &param.type_ else {
                                return param.clone()
                            };
                            CallableParam {
                                type_: ParamType::PositionalOrKeyword(
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

    pub fn rewrite_late_bound_callables(&self, manager: &TypeVarManager) -> Self {
        let rewrite_generics = |generics: &GenericsList| {
            GenericsList::new_generics(
                generics
                    .iter()
                    .map(|g| match g {
                        GenericItem::TypeArg(t) => {
                            GenericItem::TypeArg(t.rewrite_late_bound_callables(manager))
                        }
                        GenericItem::TypeArgs(ts) => GenericItem::TypeArgs(TypeArgs::new(
                            ts.args.rewrite_late_bound_callables(manager),
                        )),
                        GenericItem::ParamSpecArg(p) => GenericItem::ParamSpecArg({
                            debug_assert!(p.type_vars.is_none());
                            ParamSpecArg {
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
                        .map(|c| c.rewrite_late_bound_callables(manager))
                        .collect()
                }))
            }
            Type::TypeVar(t) => Type::TypeVar(manager.remap_type_var(t)),
            Type::Type(type_) => Type::Type(Rc::new(type_.rewrite_late_bound_callables(manager))),
            Type::Tuple(tup) => {
                Type::Tuple(Tuple::new(tup.args.rewrite_late_bound_callables(manager)))
            }
            Type::Literal { .. } => self.clone(),
            Type::Callable(c) => Type::Callable(Rc::new(c.rewrite_late_bound_callables(manager))),
            Type::NewType(_) => todo!(),
            Type::RecursiveType(recursive_alias) => {
                Type::RecursiveType(Rc::new(RecursiveType::new(
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
    pub fn replace_type_var_likes_and_self(
        &self,
        db: &Database,
        callable: &mut impl FnMut(TypeVarLikeUsage) -> GenericItem,
        replace_self: ReplaceSelf,
    ) -> Self {
        match self {
            Self::TypeArg(t) => {
                Self::TypeArg(t.replace_type_var_likes_and_self(db, callable, replace_self))
            }
            Self::TypeArgs(ta) => Self::TypeArgs(TypeArgs {
                args: ta
                    .args
                    .replace_type_var_likes_and_self(db, callable, replace_self),
            }),
            Self::ParamSpecArg(param_spec_arg) => {
                let tv_ref = param_spec_arg.type_vars.as_ref();
                let mut type_vars = tv_ref.map(|tv| tv.type_vars.as_vec());
                let (params, defined_at_and_other) =
                    param_spec_arg.params.replace_type_var_likes_and_self(
                        db,
                        &mut type_vars,
                        tv_ref.map(|x| x.in_definition),
                        callable,
                        replace_self,
                    );
                GenericItem::ParamSpecArg(ParamSpecArg {
                    params,
                    type_vars: type_vars.map(|tvs| ParamSpecTypeVars {
                        type_vars: TypeVarLikes::from_vec(tvs),
                        in_definition: defined_at_and_other
                            .map(|(d, _)| d)
                            .unwrap_or_else(|| tv_ref.unwrap().in_definition),
                    }),
                })
            }
        }
    }
}

impl CallableContent {
    pub fn replace_type_var_likes_and_self(
        &self,
        db: &Database,
        callable: ReplaceTypeVarLike,
        replace_self: ReplaceSelf,
    ) -> CallableContent {
        let has_type_vars = !self.type_vars.is_empty();
        let mut type_vars = has_type_vars.then(|| self.type_vars.clone().as_vec());
        let (params, remap_data) = self.params.replace_type_var_likes_and_self(
            db,
            &mut type_vars,
            Some(self.defined_at),
            callable,
            replace_self,
        );
        let mut return_type =
            self.return_type
                .replace_type_var_likes_and_self(db, callable, replace_self);
        if let Some(remap_data) = remap_data {
            return_type = return_type.replace_type_var_likes_and_self(
                db,
                &mut |usage| {
                    replace_param_spec_inner_type_var_likes_and_self(
                        usage,
                        self.defined_at,
                        remap_data,
                    )
                },
                replace_self,
            );
        }
        CallableContent {
            name: self.name.clone(),
            class_name: self.class_name,
            defined_at: self.defined_at,
            kind: self.kind,
            type_vars: type_vars
                .map(TypeVarLikes::from_vec)
                .unwrap_or_else(|| db.python_state.empty_type_var_likes.clone()),
            params,
            return_type,
        }
    }

    fn rewrite_late_bound_callables(&self, manager: &TypeVarManager) -> Self {
        let type_vars = manager
            .iter()
            .filter_map(|t| {
                (t.most_outer_callable == Some(self.defined_at)).then(|| t.type_var_like.clone())
            })
            .collect::<Rc<_>>();
        CallableContent {
            name: self.name.clone(),
            class_name: self.class_name,
            defined_at: self.defined_at,
            kind: self.kind,
            type_vars: TypeVarLikes::new(type_vars),
            params: match &self.params {
                CallableParams::Simple(params) => CallableParams::Simple(
                    params
                        .iter()
                        .map(|p| CallableParam {
                            type_: match &p.type_ {
                                ParamType::PositionalOnly(t) => ParamType::PositionalOnly(
                                    t.rewrite_late_bound_callables(manager),
                                ),
                                ParamType::PositionalOrKeyword(t) => {
                                    ParamType::PositionalOrKeyword(
                                        t.rewrite_late_bound_callables(manager),
                                    )
                                }
                                ParamType::KeywordOnly(t) => {
                                    ParamType::KeywordOnly(t.rewrite_late_bound_callables(manager))
                                }
                                ParamType::Star(s) => ParamType::Star(match s {
                                    StarParamType::ArbitraryLen(t) => StarParamType::ArbitraryLen(
                                        t.rewrite_late_bound_callables(manager),
                                    ),
                                    StarParamType::UnpackedTuple(tup) => {
                                        StarParamType::UnpackedTuple(Tuple::new(
                                            tup.args.rewrite_late_bound_callables(manager),
                                        ))
                                    }
                                    StarParamType::ParamSpecArgs(_) => todo!(),
                                }),
                                ParamType::StarStar(d) => ParamType::StarStar(match d {
                                    StarStarParamType::ValueType(t) => {
                                        StarStarParamType::ValueType(
                                            t.rewrite_late_bound_callables(manager),
                                        )
                                    }
                                    StarStarParamType::UnpackTypedDict(_) => {
                                        todo!()
                                    }
                                    StarStarParamType::ParamSpecKwargs(_) => {
                                        todo!()
                                    }
                                }),
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
            return_type: self.return_type.rewrite_late_bound_callables(manager),
        }
    }
}

impl CallableParams {
    pub fn replace_type_var_likes_and_self(
        &self,
        db: &Database,
        type_vars: &mut Option<Vec<TypeVarLike>>,
        in_definition: Option<PointLink>,
        callable: ReplaceTypeVarLike,
        replace_self: ReplaceSelf,
    ) -> (CallableParams, Option<(PointLink, usize)>) {
        let mut replace_data = None;
        let new_params = match self {
            CallableParams::Simple(params) => CallableParams::Simple({
                let mut new_params = vec![];
                for p in params.iter() {
                    let new_param_type = match &p.type_ {
                        ParamType::PositionalOnly(t) => ParamType::PositionalOnly(
                            t.replace_type_var_likes_and_self(db, callable, replace_self),
                        ),
                        ParamType::PositionalOrKeyword(t) => ParamType::PositionalOrKeyword(
                            t.replace_type_var_likes_and_self(db, callable, replace_self),
                        ),
                        ParamType::KeywordOnly(t) => ParamType::KeywordOnly(
                            t.replace_type_var_likes_and_self(db, callable, replace_self),
                        ),
                        ParamType::Star(s) => ParamType::Star(match s {
                            StarParamType::ArbitraryLen(t) => StarParamType::ArbitraryLen(
                                t.replace_type_var_likes_and_self(db, callable, replace_self),
                            ),
                            StarParamType::UnpackedTuple(u) => {
                                match u.args.replace_type_var_likes_and_self(
                                    db,
                                    callable,
                                    replace_self,
                                ) {
                                    TupleArgs::FixedLen(types) => {
                                        for t in rc_slice_into_vec(types) {
                                            new_params.push(CallableParam::new_anonymous(
                                                ParamType::PositionalOnly(t),
                                            ))
                                        }
                                        continue;
                                    }
                                    TupleArgs::ArbitraryLen(t) => {
                                        new_params.push(CallableParam::new_anonymous(
                                            ParamType::Star(StarParamType::ArbitraryLen(*t)),
                                        ));
                                        continue;
                                    }
                                    TupleArgs::WithUnpack(mut with_unpack) => {
                                        let before = std::mem::replace(
                                            &mut with_unpack.before,
                                            Rc::from([]),
                                        );
                                        for t in before.iter() {
                                            new_params.push(CallableParam::new_anonymous(
                                                ParamType::PositionalOnly(t.clone()),
                                            ))
                                        }
                                        StarParamType::UnpackedTuple(Tuple::new(
                                            TupleArgs::WithUnpack(with_unpack),
                                        ))
                                    }
                                }
                            }
                            StarParamType::ParamSpecArgs(_) => todo!(),
                        }),
                        ParamType::StarStar(d) => ParamType::StarStar(match d {
                            StarStarParamType::ValueType(t) => StarStarParamType::ValueType(
                                t.replace_type_var_likes_and_self(db, callable, replace_self),
                            ),
                            StarStarParamType::UnpackTypedDict(_) => {
                                todo!()
                            }
                            StarStarParamType::ParamSpecKwargs(_) => {
                                todo!()
                            }
                        }),
                    };
                    new_params.push(CallableParam {
                        type_: new_param_type,
                        has_default: p.has_default,
                        name: p.name.clone(),
                    })
                }
                new_params.into()
            }),
            CallableParams::Any(cause) => CallableParams::Any(*cause),
            CallableParams::WithParamSpec(types, param_spec) => {
                let result = callable(TypeVarLikeUsage::ParamSpec(Cow::Borrowed(param_spec)));
                let GenericItem::ParamSpecArg(mut new) = result else {
                    unreachable!()
                };
                if let Some(new_spec_type_vars) = new.type_vars {
                    if let Some(in_definition) = in_definition {
                        let type_var_len = type_vars.as_ref().map(|t| t.len()).unwrap_or(0);
                        replace_data = Some((new_spec_type_vars.in_definition, type_var_len));
                        let new_params = new.params.replace_type_var_likes_and_self(
                            db,
                            &mut None,
                            None,
                            &mut |usage| {
                                replace_param_spec_inner_type_var_likes_and_self(
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
                            let mut params = rc_slice_into_vec(params);
                            params.splice(
                                0..0,
                                types.iter().map(|t| CallableParam {
                                    type_: ParamType::PositionalOnly(
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
                            types.append(&mut rc_slice_into_vec(new_types));
                            CallableParams::WithParamSpec(types.into(), p)
                        }
                    }
                }
            }
        };
        (new_params, replace_data)
    }
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

impl TupleArgs {
    pub fn replace_type_var_likes_and_self(
        &self,
        db: &Database,
        callable: ReplaceTypeVarLike,
        replace_self: ReplaceSelf,
    ) -> Self {
        match self {
            TupleArgs::FixedLen(ts) => TupleArgs::FixedLen(
                ts.iter()
                    .map(|t| t.replace_type_var_likes_and_self(db, callable, replace_self))
                    .collect(),
            ),
            TupleArgs::ArbitraryLen(t) => TupleArgs::ArbitraryLen(Box::new(
                t.replace_type_var_likes_and_self(db, callable, replace_self),
            )),
            TupleArgs::WithUnpack(unpack) => match &unpack.unpack {
                TupleUnpack::TypeVarTuple(tvt) => {
                    let GenericItem::TypeArgs(new) = callable(TypeVarLikeUsage::TypeVarTuple(Cow::Borrowed(tvt))) else {
                            unreachable!();
                        };
                    let new_before: Vec<_> = unpack
                        .before
                        .iter()
                        .map(|t| t.replace_type_var_likes_and_self(db, callable, replace_self))
                        .collect();
                    let new_after: Vec<_> = unpack
                        .after
                        .iter()
                        .map(|t| t.replace_type_var_likes_and_self(db, callable, replace_self))
                        .collect();
                    new.args.add_before_and_after(new_before, new_after)
                }
                TupleUnpack::ArbitraryLen(t) => TupleArgs::WithUnpack(WithUnpack {
                    before: unpack.before.clone(),
                    unpack: TupleUnpack::ArbitraryLen(t.replace_type_var_likes_and_self(
                        db,
                        callable,
                        replace_self,
                    )),
                    after: unpack.after.clone(),
                }),
            },
        }
    }

    pub fn rewrite_late_bound_callables(&self, manager: &TypeVarManager) -> Self {
        match self {
            Self::FixedLen(ts) => Self::FixedLen(
                ts.iter()
                    .map(|t| t.rewrite_late_bound_callables(manager))
                    .collect(),
            ),
            Self::ArbitraryLen(t) => {
                Self::ArbitraryLen(Box::new(t.rewrite_late_bound_callables(manager)))
            }
            Self::WithUnpack(with_unpack) => Self::WithUnpack(WithUnpack {
                before: with_unpack
                    .before
                    .iter()
                    .map(|t| t.rewrite_late_bound_callables(manager))
                    .collect(),
                unpack: match &with_unpack.unpack {
                    TupleUnpack::TypeVarTuple(tvt) => {
                        TupleUnpack::TypeVarTuple(manager.remap_type_var_tuple(tvt))
                    }
                    TupleUnpack::ArbitraryLen(t) => {
                        TupleUnpack::ArbitraryLen(t.rewrite_late_bound_callables(manager))
                    }
                },
                after: with_unpack
                    .after
                    .iter()
                    .map(|t| t.rewrite_late_bound_callables(manager))
                    .collect(),
            }),
        }
    }
}
