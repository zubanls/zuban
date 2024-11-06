use std::rc::Rc;

use super::{
    simplified_union_from_iterators_with_format_index, type_var_likes::CallableId, CallableContent,
    CallableParam, CallableParams, ClassGenerics, Dataclass, FunctionOverload, GenericClass,
    GenericItem, GenericsList, Intersection, NamedTuple, ParamSpecArg, ParamSpecTypeVars,
    ParamSpecUsage, ParamType, RecursiveType, StarParamType, StarStarParamType, Tuple, TupleArgs,
    Type, TypeArgs, TypeGuardInfo, TypeVarLike, TypeVarLikeUsage, TypeVarLikes, TypeVarManager,
    TypeVarTupleUsage, TypedDict, TypedDictGenerics, UnionEntry, UnionType,
};
use crate::{
    database::{Database, PointLink},
    inference_state::InferenceState,
    type_::{AnyCause, NeverCause, TupleUnpack, WithUnpack},
    utils::rc_slice_into_vec,
};

pub type ReplaceTypeVarLike<'x> = &'x mut dyn FnMut(TypeVarLikeUsage) -> Option<GenericItem>;
pub type ReplaceSelf<'x> = &'x dyn Fn() -> Type;

trait Replacer {
    fn replace_type(&mut self, t: &Type) -> Option<Type>;
    fn replace_callable_params(&mut self, p: &CallableParams) -> Option<CallableParams> {
        None
    }
    fn replace_callable(&mut self, c: &Rc<CallableContent>) -> Option<Rc<CallableContent>> {
        None
    }
    fn replace_type_var_tuple(&mut self, tvt: &TypeVarTupleUsage) -> Option<TupleArgs> {
        None
    }
    fn replace_param_spec(
        &mut self,
        type_vars: &mut Option<Vec<TypeVarLike>>,
        in_definition: Option<PointLink>,
        replace_data: &mut Option<(PointLink, usize)>,
        p: &ParamSpecUsage,
    ) -> Option<ReplacedParamSpec> {
        None
    }
}

enum ReplacedParamSpec {
    ParamSpec(ParamSpecUsage),
    Params(CallableParams),
}

impl Type {
    pub fn replace_never_from_inference_with_any(&self) -> Self {
        struct NeverReplacer();
        impl Replacer for NeverReplacer {
            #[inline]
            fn replace_type(&mut self, t: &Type) -> Option<Type> {
                match t {
                    Type::Never(NeverCause::Inference) => Some(Type::Any(AnyCause::FromError)),
                    _ => None,
                }
            }
            #[inline]
            fn replace_callable_params(&mut self, p: &CallableParams) -> Option<CallableParams> {
                match p {
                    CallableParams::Never(_) => Some(CallableParams::Any(AnyCause::FromError)),
                    _ => None,
                }
            }
        }
        self.replace_internal(&mut NeverReplacer())
            .unwrap_or_else(|| self.clone())
    }

    pub fn rewrite_late_bound_callables<T: CallableId>(&self, manager: &TypeVarManager<T>) -> Self {
        struct LateBoundReplacer<'a, X>(&'a TypeVarManager<X>);
        impl<X: CallableId> Replacer for LateBoundReplacer<'_, X> {
            #[inline]
            fn replace_type(&mut self, t: &Type) -> Option<Type> {
                match t {
                    Type::TypeVar(t) => Some(Type::TypeVar(self.0.remap_type_var(t))),
                    Type::ParamSpecArgs(usage) => {
                        Some(Type::ParamSpecArgs(self.0.remap_param_spec(usage)))
                    }
                    Type::ParamSpecKwargs(usage) => {
                        Some(Type::ParamSpecKwargs(self.0.remap_param_spec(usage)))
                    }
                    _ => None,
                }
            }
            #[inline]
            fn replace_callable(&mut self, c: &Rc<CallableContent>) -> Option<Rc<CallableContent>> {
                let new = self.0.type_vars_for_callable(c);
                (new != c.type_vars).then(|| {
                    Rc::new(CallableContent {
                        name: c.name.clone(),
                        class_name: c.class_name,
                        defined_at: c.defined_at,
                        kind: c.kind,
                        type_vars: new,
                        guard: c
                            .guard
                            .as_ref()
                            .map(|g| g.replace_internal(self).unwrap_or_else(|| g.clone())),
                        is_abstract: c.is_abstract,
                        is_final: c.is_final,
                        no_type_check: c.no_type_check,
                        params: c
                            .params
                            .replace_internal(self, &mut None, None)
                            .map(|(params, _)| params)
                            .unwrap_or_else(|| c.params.clone()),
                        return_type: c
                            .return_type
                            .replace_internal(self)
                            .unwrap_or_else(|| c.return_type.clone()),
                    })
                })
            }
            fn replace_type_var_tuple(&mut self, tvt: &TypeVarTupleUsage) -> Option<TupleArgs> {
                Some(TupleArgs::WithUnpack(
                    WithUnpack::with_empty_before_and_after(TupleUnpack::TypeVarTuple(
                        self.0.remap_type_var_tuple(tvt),
                    )),
                ))
            }
            fn replace_param_spec(
                &mut self,
                type_vars: &mut Option<Vec<TypeVarLike>>,
                in_definition: Option<PointLink>,
                replace_data: &mut Option<(PointLink, usize)>,
                p: &ParamSpecUsage,
            ) -> Option<ReplacedParamSpec> {
                let new_param_spec = self.0.remap_param_spec(p);
                if p == &new_param_spec {
                    return None;
                }
                Some(ReplacedParamSpec::ParamSpec(new_param_spec))
            }
        }

        self.replace_internal(&mut LateBoundReplacer(manager))
            .unwrap_or_else(|| self.clone())
    }

    pub fn replace_type_var_likes_and_self(
        &self,
        db: &Database,
        callable: ReplaceTypeVarLike,
        replace_self: ReplaceSelf,
    ) -> Option<Self> {
        self.replace_internal(&mut ReplaceTypeVarLikes {
            db,
            callable,
            replace_self,
        })
    }

    fn replace_internal(&self, replacer: &mut impl Replacer) -> Option<Self> {
        if let Some(t) = replacer.replace_type(self) {
            return Some(t);
        }

        match self {
            Type::Class(c) => match &c.generics {
                ClassGenerics::List(l) => l
                    .replace_internal(replacer)
                    .map(|g| Type::new_class(c.link, ClassGenerics::List(g))),
                _ => None,
            },
            Type::FunctionOverload(overload) => Some(Type::FunctionOverload(
                FunctionOverload::new(maybe_replace_iterable(overload.iter_functions(), |c| {
                    if let Some(new) = replacer.replace_callable(c) {
                        return Some(new);
                    }
                    c.replace_internal(replacer).map(Rc::new)
                })?),
            )),
            Type::Union(u) => Some(Type::Union(UnionType::new(maybe_replace_iterable(
                u.entries.iter(),
                |union_entry| {
                    Some(UnionEntry {
                        type_: union_entry.type_.replace_internal(replacer)?,
                        format_index: union_entry.format_index,
                    })
                },
            )?))),
            Type::Type(t) => Some(Type::Type(Rc::new(t.replace_internal(replacer)?))),
            Type::Tuple(content) => Some(Type::Tuple(Tuple::new(
                content.args.replace_internal(replacer)?,
            ))),
            Type::Callable(c) => {
                if let Some(new) = replacer.replace_callable(c) {
                    return Some(Type::Callable(new));
                }
                Some(Type::Callable(Rc::new(c.replace_internal(replacer)?)))
            }
            Type::RecursiveType(rec) => Some(Type::RecursiveType(Rc::new(RecursiveType::new(
                rec.link,
                Some(rec.generics.as_ref()?.replace_internal(replacer)?),
            )))),
            Type::Dataclass(d) => match &d.class.generics {
                ClassGenerics::List(l) => Some(Type::Dataclass(Dataclass::new(
                    GenericClass {
                        link: d.class.link,
                        generics: ClassGenerics::List(l.replace_internal(replacer)?),
                    },
                    d.options,
                ))),
                _ => None,
            },
            Type::TypedDict(td) => td.replace_internal(replacer).map(Type::TypedDict),
            Type::NamedTuple(nt) => {
                let new_params =
                    maybe_replace_iterable(nt.__new__.expect_simple_params().iter(), |param| {
                        let ParamType::PositionalOrKeyword(t) = &param.type_ else {
                            return None;
                        };
                        Some(CallableParam {
                            type_: ParamType::PositionalOrKeyword(t.replace_internal(replacer)?),
                            has_default: param.has_default,
                            name: param.name.clone(),
                        })
                    })?;
                let mut constructor = nt.__new__.as_ref().clone();
                constructor.params = CallableParams::new_simple(new_params);
                Some(Type::NamedTuple(Rc::new(NamedTuple::new(
                    nt.name,
                    constructor,
                ))))
            }
            Type::Intersection(intersection) => Some(Type::Intersection(Intersection::new(
                maybe_replace_iterable(intersection.iter_entries(), |t| {
                    t.replace_internal(replacer)
                })?,
            ))),
            Type::Any(..)
            | Type::None
            | Type::Never(..)
            | Type::TypeVar(_)
            | Type::Self_
            | Type::Literal { .. }
            | Type::Module(_)
            | Type::Namespace(_)
            | Type::Enum(_)
            | Type::EnumMember(_)
            | Type::NewType(_)
            | Type::Super { .. }
            | Type::CustomBehavior(_)
            | Type::ParamSpecArgs(_)
            | Type::ParamSpecKwargs(_) => None,
        }
    }

    pub fn replace_type_var_likes(
        &self,
        db: &Database,
        callable: &mut impl FnMut(TypeVarLikeUsage) -> Option<GenericItem>,
    ) -> Option<Self> {
        self.replace_type_var_likes_and_self(db, callable, &|| Type::Self_)
    }

    pub fn replace_self(&self, db: &Database, replace_self: ReplaceSelf) -> Option<Self> {
        self.replace_type_var_likes_and_self(db, &mut |usage| None, replace_self)
    }
}

#[inline]
fn maybe_replace_iterable<
    'x,
    T: Clone + 'x,
    IT: Iterator<Item = &'x T> + Clone,
    R: FromIterator<T>,
>(
    elements: IT,
    mut replace: impl FnMut(&T) -> Option<T>,
) -> Option<R> {
    let iter2 = elements.into_iter();
    let mut iter1 = iter2.clone();
    for (i, x) in iter1.by_ref().enumerate() {
        let Some(first_replaced) = replace(x) else {
            continue;
        };
        let result = iter2
            .take(i)
            .cloned()
            .chain(std::iter::once(first_replaced))
            .chain(iter1.map(|t| replace(t).unwrap_or_else(|| t.clone())))
            .collect();
        return Some(result);
    }
    None
}

impl GenericItem {
    fn replace_internal(&self, replacer: &mut impl Replacer) -> Option<Self> {
        match self {
            Self::TypeArg(t) => Some(Self::TypeArg(t.replace_internal(replacer)?)),
            Self::TypeArgs(ta) => Some(Self::TypeArgs(TypeArgs {
                args: ta.args.replace_internal(replacer)?,
            })),
            Self::ParamSpecArg(param_spec_arg) => Some(Self::ParamSpecArg(
                param_spec_arg.replace_internal(replacer)?,
            )),
        }
    }

    pub fn replace_type_var_likes_and_self(
        &self,
        db: &Database,
        callable: &mut impl FnMut(TypeVarLikeUsage) -> Option<GenericItem>,
        replace_self: ReplaceSelf,
    ) -> Option<Self> {
        self.replace_internal(&mut ReplaceTypeVarLikes {
            db,
            callable,
            replace_self,
        })
    }
}

impl ParamSpecArg {
    fn replace_internal(&self, replacer: &mut impl Replacer) -> Option<Self> {
        let type_vars = self.type_vars.as_ref().map(|t| t.type_vars.as_vec());
        // TODO what todo about changing type vars? like replace_type_var_likes_and_self
        Some(Self::new(
            self.params.replace_internal(replacer, &mut None, None)?.0,
            type_vars.map(|t| ParamSpecTypeVars {
                type_vars: TypeVarLikes::from_vec(t),
                in_definition: self.type_vars.as_ref().unwrap().in_definition,
            }),
        ))
    }
}

impl CallableContent {
    fn replace_internal(&self, replacer: &mut impl Replacer) -> Option<Self> {
        let new_param_data = self.params.replace_internal(replacer, &mut None, None);
        let new_return_type = self.return_type.replace_internal(replacer);
        let new_guard = match &self.guard {
            None => Some(None),
            Some(g) => g.replace_internal(replacer).map(Some),
        };
        if new_guard.is_none() && new_param_data.is_none() && new_return_type.is_none() {
            return None;
        }
        let (params, remap_data) = new_param_data.unwrap_or_else(|| (self.params.clone(), None));
        Some(CallableContent {
            name: self.name.clone(),
            class_name: self.class_name,
            defined_at: self.defined_at,
            kind: self.kind,
            type_vars: self.type_vars.clone(),
            guard: new_guard.unwrap_or_else(|| self.guard.clone()),
            is_abstract: self.is_abstract,
            is_final: self.is_final,
            no_type_check: self.no_type_check,
            params,
            return_type: new_return_type.unwrap_or_else(|| self.return_type.clone()),
        })
    }

    pub fn replace_type_var_likes_and_self_inplace(
        self,
        db: &Database,
        callable: ReplaceTypeVarLike,
        replace_self: ReplaceSelf,
    ) -> Self {
        let replacer = &mut ReplaceTypeVarLikes {
            db,
            callable,
            replace_self,
        };
        if let Some(c) = replacer.replace_callable_without_rc(&self) {
            return c;
        }
        self.replace_internal(replacer).unwrap_or(self)
    }

    pub fn replace_type_var_likes_and_self(
        &self,
        db: &Database,
        callable: ReplaceTypeVarLike,
        replace_self: ReplaceSelf,
    ) -> CallableContent {
        let replacer = &mut ReplaceTypeVarLikes {
            db,
            callable,
            replace_self,
        };
        if let Some(c) = replacer.replace_callable_without_rc(&self) {
            return c;
        }
        self.replace_internal(replacer)
            .unwrap_or_else(|| self.clone())
    }
}

impl TypeGuardInfo {
    fn replace_internal(&self, replacer: &mut impl Replacer) -> Option<Self> {
        Some(TypeGuardInfo {
            type_: self.type_.replace_internal(replacer)?,
            from_type_is: self.from_type_is,
        })
    }
}

impl CallableParams {
    fn replace_internal(
        &self,
        replacer: &mut impl Replacer,
        type_vars: &mut Option<Vec<TypeVarLike>>,
        in_definition: Option<PointLink>,
    ) -> Option<(CallableParams, Option<(PointLink, usize)>)> {
        if let Some(replaced) = replacer.replace_callable_params(self) {
            return Some((replaced, None));
        }
        let mut replace_data = None;
        match self {
            CallableParams::Simple(params) => {
                let mut had_replace = false;
                let mut backfill = |new_params: &mut Vec<_>, len| {
                    had_replace = true;
                    new_params.extend_from_slice(&params[..len]);
                };
                let mut new_params = vec![];
                let mut overwritten_params = None;
                let mut maybe_add = |new_params: &mut Vec<_>, i, param: &CallableParam| {
                    let new_param_type = match &param.type_ {
                        ParamType::PositionalOnly(t) => {
                            ParamType::PositionalOnly(t.replace_internal(replacer)?)
                        }
                        ParamType::PositionalOrKeyword(t) => {
                            ParamType::PositionalOrKeyword(t.replace_internal(replacer)?)
                        }
                        ParamType::KeywordOnly(t) => {
                            ParamType::KeywordOnly(t.replace_internal(replacer)?)
                        }
                        ParamType::Star(s) => ParamType::Star(match s {
                            StarParamType::ArbitraryLen(t) => {
                                StarParamType::ArbitraryLen(t.replace_internal(replacer)?)
                            }
                            StarParamType::UnpackedTuple(u) => {
                                let replaced = u.args.replace_internal(replacer)?;
                                if new_params.is_empty() {
                                    backfill(new_params, i)
                                }
                                match replaced {
                                    TupleArgs::FixedLen(types) => {
                                        for t in rc_slice_into_vec(types) {
                                            new_params.push(CallableParam::new_anonymous(
                                                ParamType::PositionalOnly(t),
                                            ))
                                        }
                                        return Some(());
                                    }
                                    TupleArgs::ArbitraryLen(t) => StarParamType::ArbitraryLen(*t),
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
                            StarParamType::ParamSpecArgs(u) => {
                                let result = replacer.replace_param_spec(
                                    type_vars,
                                    in_definition,
                                    &mut replace_data,
                                    u,
                                )?;
                                if new_params.is_empty() {
                                    backfill(new_params, i)
                                }
                                match result {
                                    ReplacedParamSpec::ParamSpec(p) => {
                                        new_params.push(CallableParam::new_anonymous(
                                            ParamType::Star(StarParamType::ParamSpecArgs(
                                                p.clone(),
                                            )),
                                        ));
                                        new_params.push(CallableParam::new_anonymous(
                                            ParamType::StarStar(
                                                StarStarParamType::ParamSpecKwargs(p),
                                            ),
                                        ));
                                    }
                                    ReplacedParamSpec::Params(new) => match new {
                                        CallableParams::Simple(params) => {
                                            new_params.extend_from_slice(&params);
                                        }
                                        CallableParams::Any(cause) => {
                                            overwritten_params = Some(CallableParams::Any(cause))
                                        }
                                        CallableParams::Never(cause) => {
                                            overwritten_params = Some(CallableParams::Never(cause))
                                        }
                                    },
                                };
                                return Some(());
                            }
                        }),
                        ParamType::StarStar(d) => ParamType::StarStar(match d {
                            StarStarParamType::ValueType(t) => {
                                StarStarParamType::ValueType(t.replace_internal(replacer)?)
                            }
                            StarStarParamType::UnpackTypedDict(td) => {
                                StarStarParamType::UnpackTypedDict(td.replace_internal(replacer)?)
                            }
                            StarStarParamType::ParamSpecKwargs(_) => {
                                // Was already handled in ParamSpecArgs
                                return Some(());
                            }
                        }),
                    };
                    if new_params.is_empty() {
                        backfill(new_params, i)
                    }
                    new_params.push(CallableParam {
                        type_: new_param_type,
                        has_default: param.has_default,
                        name: param.name.clone(),
                    });
                    Some(())
                };
                for (i, param) in params.iter().enumerate() {
                    if maybe_add(&mut new_params, i, param).is_none() && !new_params.is_empty() {
                        new_params.push(param.clone())
                    }
                }
                if let Some(p) = overwritten_params {
                    Some((p, replace_data))
                } else {
                    had_replace
                        .then(|| (CallableParams::new_simple(new_params.into()), replace_data))
                }
            }
            CallableParams::Any(cause) => Some((CallableParams::Any(*cause), None)),
            CallableParams::Never(cause) => Some((CallableParams::Never(*cause), None)),
        }
    }

    pub fn replace_type_var_likes_and_self(
        &self,
        db: &Database,
        callable: ReplaceTypeVarLike,
        replace_self: ReplaceSelf,
    ) -> Option<CallableParams> {
        self.replace_internal(
            &mut ReplaceTypeVarLikes {
                db,
                callable,
                replace_self,
            },
            &mut None,
            None,
        )
        .map(|(params, _)| params)
    }
}

pub fn replace_param_spec(
    db: &Database,
    callable: ReplaceTypeVarLike,
    u: &ParamSpecUsage,
) -> CallableParams {
    replace_param_spec_internal(db, &mut None, None, callable, &|| Type::Self_, &mut None, u)
}

fn replace_param_spec_internal(
    db: &Database,
    type_vars: &mut Option<Vec<TypeVarLike>>,
    in_definition: Option<PointLink>,
    callable: ReplaceTypeVarLike,
    replace_self: ReplaceSelf,
    replace_data: &mut Option<(PointLink, usize)>,
    u: &ParamSpecUsage,
) -> CallableParams {
    let result = callable(TypeVarLikeUsage::ParamSpec(u.clone()));
    // TODO should we use the TypeVarLikeUsage like this?
    let GenericItem::ParamSpecArg(mut new) =
        result.unwrap_or_else(|| TypeVarLikeUsage::ParamSpec(u.clone()).into_generic_item())
    else {
        unreachable!()
    };
    if let Some(new_spec_type_vars) = new.type_vars {
        if let Some(in_definition) = in_definition {
            let type_var_len = type_vars.as_ref().map(|t| t.len()).unwrap_or(0);
            *replace_data = Some((new_spec_type_vars.in_definition, type_var_len));
            let new_params = new.params.replace_type_var_likes_and_self(
                db,
                &mut |usage| {
                    replace_param_spec_inner_type_var_likes(
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
            new.params = new_params.unwrap_or_else(|| new.params.clone());
        } else {
            debug_assert!(type_vars.is_none());
        }
    }
    new.params
}

fn replace_param_spec_inner_type_var_likes(
    mut usage: TypeVarLikeUsage,
    in_definition: PointLink,
    replace_data: (PointLink, usize),
) -> Option<GenericItem> {
    if usage.in_definition() != replace_data.0 {
        return None;
    }
    usage.update_in_definition_and_index(
        in_definition,
        (usage.index().as_usize() + replace_data.1).into(),
    );
    Some(usage.into_generic_item())
}

impl TupleArgs {
    fn replace_internal(&self, replacer: &mut impl Replacer) -> Option<Self> {
        Some(match self {
            TupleArgs::FixedLen(ts) => {
                TupleArgs::FixedLen(maybe_replace_iterable(ts.iter(), |t| {
                    t.replace_internal(replacer)
                })?)
            }
            TupleArgs::ArbitraryLen(t) => {
                TupleArgs::ArbitraryLen(Box::new(t.replace_internal(replacer)?))
            }
            TupleArgs::WithUnpack(unpack) => {
                let new_before: Option<Vec<_>> =
                    maybe_replace_iterable(unpack.before.iter(), |t| t.replace_internal(replacer));
                let new_after: Option<Vec<_>> =
                    maybe_replace_iterable(unpack.after.iter(), |t| t.replace_internal(replacer));
                let inner = match &unpack.unpack {
                    TupleUnpack::TypeVarTuple(tvt) => match replacer.replace_type_var_tuple(tvt) {
                        Some(new) => {
                            return Some(
                                new.add_before_and_after(
                                    new_before
                                        .map(|v| v.into())
                                        .unwrap_or_else(|| unpack.before.clone()),
                                    new_after
                                        .map(|v| v.into())
                                        .unwrap_or_else(|| unpack.after.clone()),
                                ),
                            )
                        }
                        None => None,
                    },
                    TupleUnpack::ArbitraryLen(t) => t
                        .replace_internal(replacer)
                        .map(|t| TupleUnpack::ArbitraryLen(t)),
                };
                if inner.is_none() && new_before.is_none() && new_after.is_none() {
                    return None;
                }
                TupleArgs::WithUnpack(WithUnpack {
                    before: new_before
                        .map(|v| v.into())
                        .unwrap_or_else(|| unpack.before.clone()),
                    unpack: inner.unwrap_or_else(|| unpack.unpack.clone()),
                    after: new_after
                        .map(|v| v.into())
                        .unwrap_or_else(|| unpack.after.clone()),
                })
            }
        })
    }

    pub fn replace_type_var_likes(
        &self,
        db: &Database,
        callable: ReplaceTypeVarLike,
    ) -> Option<Self> {
        self.replace_internal(&mut ReplaceTypeVarLikes {
            db,
            callable,
            replace_self: &|| Type::Self_,
        })
    }
}

impl GenericsList {
    pub fn replace_type_var_likes(self, db: &Database, callable: ReplaceTypeVarLike) -> Self {
        self.replace_internal(&mut ReplaceTypeVarLikes {
            db,
            callable,
            replace_self: &|| Type::Self_,
        })
        .unwrap_or_else(|| self)
    }

    fn replace_internal(&self, replacer: &mut impl Replacer) -> Option<Self> {
        Some(GenericsList::new_generics(maybe_replace_iterable(
            self.iter(),
            |g| g.replace_internal(replacer),
        )?))
    }
}

impl TypedDict {
    fn replace_internal(&self, replacer: &mut impl Replacer) -> Option<Rc<Self>> {
        let generics = match &self.generics {
            TypedDictGenerics::Generics(generics) => {
                TypedDictGenerics::Generics(generics.replace_internal(replacer)?)
            }
            TypedDictGenerics::NotDefinedYet(_) => self.generics.clone(),
            TypedDictGenerics::None => return None,
        };
        Some(self.replace(generics, &mut |t| {
            t.replace_internal(replacer).unwrap_or_else(|| t.clone())
        }))
    }
}

struct ReplaceTypeVarLikes<'db, 'a> {
    db: &'db Database,
    callable: ReplaceTypeVarLike<'a>,
    replace_self: ReplaceSelf<'a>,
}

impl ReplaceTypeVarLikes<'_, '_> {
    #[inline]
    fn replace_callable_without_rc(&mut self, c: &CallableContent) -> Option<CallableContent> {
        let has_type_vars = !c.type_vars.is_empty();
        let mut type_vars = has_type_vars.then(|| c.type_vars.as_vec());
        let new_param_data = c
            .params
            .replace_internal(self, &mut type_vars, Some(c.defined_at));
        let new_return_type = c.return_type.replace_internal(self);
        let new_guard = match &c.guard {
            None => Some(None),
            Some(g) => g.replace_internal(self).map(Some),
        };
        if new_param_data.is_none() && new_return_type.is_none() && new_guard.is_none() {
            return None;
        }
        let (params, remap_data) = new_param_data.unwrap_or_else(|| (c.params.clone(), None));
        let mut return_type = new_return_type.unwrap_or_else(|| c.return_type.clone());
        if let Some(remap_data) = remap_data {
            return_type = return_type
                .replace_type_var_likes_and_self(
                    self.db,
                    &mut |usage| {
                        replace_param_spec_inner_type_var_likes(usage, c.defined_at, remap_data)
                    },
                    self.replace_self,
                )
                .unwrap_or_else(|| return_type.clone());
        }
        Some(CallableContent {
            name: c.name.clone(),
            class_name: c.class_name,
            defined_at: c.defined_at,
            kind: c.kind,
            type_vars: type_vars
                .map(|v| TypeVarLikes::from_vec(v))
                .unwrap_or_else(|| self.db.python_state.empty_type_var_likes.clone()),
            guard: new_guard.unwrap_or_else(|| c.guard.clone()),
            is_abstract: c.is_abstract,
            is_final: c.is_final,
            no_type_check: c.no_type_check,
            params,
            return_type,
        })
    }
}

impl Replacer for ReplaceTypeVarLikes<'_, '_> {
    #[inline]
    fn replace_type(&mut self, t: &Type) -> Option<Type> {
        match t {
            Type::Union(u) => {
                let new_entries: Vec<_> = maybe_replace_iterable(u.entries.iter(), |u| {
                    Some(UnionEntry {
                        // Performance: It is a bit questionable that this always clones.
                        // The problem is that if it doesn't, we won't use simplified union
                        // logic in all cases.
                        // Perhaps we should find a way to check whether this we are in a
                        // simplified union case. But this is generally tricky. And might
                        // also intensify workloads.
                        type_: u
                            .type_
                            .replace_internal(self)
                            .unwrap_or_else(|| u.type_.clone()),
                        format_index: u.format_index,
                    })
                })?;
                let i_s = InferenceState::new(self.db);
                let highest_union_format_index = new_entries
                    .iter()
                    .map(|e| e.type_.highest_union_format_index())
                    .max()
                    .unwrap();
                Some(simplified_union_from_iterators_with_format_index(
                    &i_s,
                    new_entries.into_iter().map(|e| (e.format_index, e.type_)),
                    highest_union_format_index,
                ))
            }
            Type::TypeVar(tv) => match (self.callable)(TypeVarLikeUsage::TypeVar(tv.clone()))? {
                GenericItem::TypeArg(t) => Some(t),
                GenericItem::TypeArgs(ts) => unreachable!(),
                GenericItem::ParamSpecArg(params) => unreachable!(),
            },
            Type::Self_ => Some((self.replace_self)()),
            _ => None,
        }
    }

    #[inline]
    fn replace_callable(&mut self, c: &Rc<CallableContent>) -> Option<Rc<CallableContent>> {
        self.replace_callable_without_rc(c).map(Rc::new)
    }

    fn replace_type_var_tuple(&mut self, tvt: &TypeVarTupleUsage) -> Option<TupleArgs> {
        let GenericItem::TypeArgs(new) =
            (self.callable)(TypeVarLikeUsage::TypeVarTuple(tvt.clone()))?
        else {
            unreachable!();
        };
        Some(new.args)
    }

    fn replace_param_spec(
        &mut self,
        type_vars: &mut Option<Vec<TypeVarLike>>,
        in_definition: Option<PointLink>,
        replace_data: &mut Option<(PointLink, usize)>,
        p: &ParamSpecUsage,
    ) -> Option<ReplacedParamSpec> {
        let result = replace_param_spec_internal(
            self.db,
            type_vars,
            in_definition,
            self.callable,
            self.replace_self,
            replace_data,
            p,
        );
        Some(ReplacedParamSpec::Params(result))
    }
}
