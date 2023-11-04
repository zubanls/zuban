use std::{borrow::Cow, rc::Rc};

use parsa_python_ast::ParamKind;

use crate::{
    database::{Database, FileIndex, PointLink},
    inference_state::InferenceState,
    matching::{
        maybe_class_usage,
        params::{WrappedDoubleStarred, WrappedParamSpecific, WrappedStarred},
        FormatData, Param, ParamsStyle,
    },
    type_::{FormatStyle, TypeVarLikeUsage},
    type_helpers::Class,
    utils::join_with_commas,
};

use super::{
    AnyCause, DbString, FunctionKind, ParamSpecUsage, RecursiveAlias, StringSlice, Type, TypeVar,
    TypeVarKind, TypeVarLike, TypeVarLikes, TypeVarName, TypeVarUsage, Variance,
};

#[derive(Debug, Clone, PartialEq)]
pub enum StarredParamSpecific {
    ArbitraryLength(Type),
    ParamSpecArgs(ParamSpecUsage),
}

#[derive(Debug, Clone, PartialEq)]
pub enum DoubleStarredParamSpecific {
    ValueType(Type),
    ParamSpecKwargs(ParamSpecUsage),
}

#[derive(Debug, Clone, PartialEq)]
pub enum ParamSpecific {
    PositionalOnly(Type),
    PositionalOrKeyword(Type),
    KeywordOnly(Type),
    Starred(StarredParamSpecific),
    DoubleStarred(DoubleStarredParamSpecific),
}

impl ParamSpecific {
    pub fn param_kind(&self) -> ParamKind {
        match self {
            Self::PositionalOnly(_) => ParamKind::PositionalOnly,
            Self::PositionalOrKeyword(_) => ParamKind::PositionalOrKeyword,
            Self::KeywordOnly(_) => ParamKind::KeywordOnly,
            Self::Starred(_) => ParamKind::Starred,
            Self::DoubleStarred(_) => ParamKind::DoubleStarred,
        }
    }

    pub fn maybe_positional_type(&self) -> Option<&Type> {
        match self {
            Self::PositionalOnly(t) | Self::PositionalOrKeyword(t) => Some(t),
            _ => None,
        }
    }

    pub fn expect_positional_type(self) -> Type {
        match self {
            Self::PositionalOnly(t) | Self::PositionalOrKeyword(t) => t,
            _ => unreachable!(),
        }
    }

    pub fn expect_positional_type_as_ref(&self) -> &Type {
        match &self {
            Self::PositionalOnly(t) | Self::PositionalOrKeyword(t) => t,
            _ => unreachable!(),
        }
    }

    pub fn maybe_type(&self) -> Option<&Type> {
        match self {
            Self::PositionalOnly(t)
            | Self::PositionalOrKeyword(t)
            | Self::KeywordOnly(t)
            | Self::Starred(StarredParamSpecific::ArbitraryLength(t))
            | Self::DoubleStarred(DoubleStarredParamSpecific::ValueType(t)) => Some(t),
            Self::Starred(StarredParamSpecific::ParamSpecArgs(_)) | Self::DoubleStarred(_) => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct CallableParam {
    pub param_specific: ParamSpecific,
    pub name: Option<DbString>,
    pub has_default: bool,
}

impl CallableParam {
    pub fn new_anonymous(param_specific: ParamSpecific) -> Self {
        CallableParam {
            param_specific,
            name: None,
            has_default: false,
        }
    }

    pub fn format(&self, format_data: &FormatData) -> Box<str> {
        if !matches!(self.param_specific, ParamSpecific::PositionalOnly(_))
            || format_data.verbose && self.has_default
        {
            if let ParamSpecific::Starred(t) = &self.param_specific {
                return match t {
                    StarredParamSpecific::ArbitraryLength(t) => {
                        format!("VarArg({})", t.format(format_data))
                    }
                    StarredParamSpecific::ParamSpecArgs(u) => unreachable!(),
                }
                .into();
            } else if let ParamSpecific::DoubleStarred(t) = &self.param_specific {
                return match t {
                    DoubleStarredParamSpecific::ValueType(t) => {
                        format!("KwArg({})", t.format(format_data))
                    }
                    DoubleStarredParamSpecific::ParamSpecKwargs(_) => unreachable!(),
                }
                .into();
            } else if let Some(name) = self.name.as_ref() {
                match format_data.style {
                    FormatStyle::MypyRevealType => {
                        let mut string = match &self.param_specific {
                            ParamSpecific::PositionalOnly(t)
                            | ParamSpecific::PositionalOrKeyword(t)
                            | ParamSpecific::KeywordOnly(t) => {
                                format!(
                                    "{}: {}",
                                    name.as_str(format_data.db),
                                    t.format(format_data),
                                )
                            }
                            // TODO these two cases are probably unreachable
                            ParamSpecific::Starred(s) => format!(
                                "*{}: {}",
                                name.as_str(format_data.db),
                                match s {
                                    StarredParamSpecific::ArbitraryLength(t) =>
                                        t.format(format_data),
                                    StarredParamSpecific::ParamSpecArgs(_) => todo!(),
                                }
                            ),
                            ParamSpecific::DoubleStarred(d) => format!(
                                "**{}: {}",
                                name.as_str(format_data.db),
                                match d {
                                    DoubleStarredParamSpecific::ValueType(t) =>
                                        t.format(format_data),
                                    DoubleStarredParamSpecific::ParamSpecKwargs(_) => todo!(),
                                }
                            ),
                        };
                        if self.has_default {
                            string += " =";
                        }
                        return string.into();
                    }
                    _ => {
                        return match &self.param_specific {
                            ParamSpecific::PositionalOnly(t)
                            | ParamSpecific::PositionalOrKeyword(t) => {
                                let t = t.format(format_data);
                                if !format_data.verbose {
                                    return t;
                                }
                                let default = match self.has_default {
                                    false => "",
                                    true => "Default",
                                };
                                format!("{default}Arg({t}, '{}')", name.as_str(format_data.db))
                            }
                            ParamSpecific::KeywordOnly(t) => {
                                let default = match self.has_default {
                                    false => "",
                                    true => "Default",
                                };
                                format!(
                                    "{default}NamedArg({}, '{}')",
                                    t.format(format_data),
                                    name.as_str(format_data.db)
                                )
                            }
                            ParamSpecific::Starred(_) | ParamSpecific::DoubleStarred(_) => {
                                unreachable!()
                            }
                        }
                        .into();
                    }
                }
            } else if self.has_default {
                return match &self.param_specific {
                    ParamSpecific::PositionalOnly(t)
                    | ParamSpecific::PositionalOrKeyword(t)
                    | ParamSpecific::KeywordOnly(t) => {
                        format!("DefaultArg({})", t.format(format_data)).into()
                    }
                    _ => unreachable!(),
                };
            }
        }
        match &self.param_specific {
            ParamSpecific::PositionalOnly(t) => t.format(format_data),
            _ => unreachable!(),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum CallableParams {
    Simple(Rc<[CallableParam]>),
    WithParamSpec(Rc<[Type]>, ParamSpecUsage),
    Any(AnyCause),
}

impl CallableParams {
    pub fn format(&self, format_data: &FormatData, style: ParamsStyle) -> Box<str> {
        let parts = match self {
            Self::Simple(params) => {
                let mut out_params = Vec::with_capacity(params.len());
                // Display a star only if we are displaying a "normal" function signature
                let mut had_param_spec_args = false;
                for (i, param) in params.iter().enumerate() {
                    use DoubleStarredParamSpecific::ParamSpecKwargs;
                    use ParamSpecific::{DoubleStarred, Starred};
                    use StarredParamSpecific::ParamSpecArgs;
                    match &param.param_specific {
                        Starred(ParamSpecArgs(usage1)) => match params
                            .get(i + 1)
                            .map(|p| &p.param_specific)
                        {
                            Some(DoubleStarred(ParamSpecKwargs(usage2))) if usage1 == usage2 => {
                                had_param_spec_args = true;
                            }
                            _ => todo!(),
                        },
                        DoubleStarred(ParamSpecKwargs(usage)) => match had_param_spec_args {
                            true => out_params.push(format_data.format_type_var_like(
                                // TODO is this even reachable?
                                &TypeVarLikeUsage::ParamSpec(Cow::Borrowed(usage)),
                                style,
                            )),
                            false => todo!(),
                        },
                        _ => out_params.push(param.format(format_data)),
                    }
                }
                out_params
            }
            Self::WithParamSpec(pre_types, usage) => {
                let style = match style {
                    ParamsStyle::CallableParams if !pre_types.is_empty() => {
                        ParamsStyle::CallableParamsInner
                    }
                    _ => style,
                };
                let spec = format_data.format_type_var_like(
                    &TypeVarLikeUsage::ParamSpec(Cow::Borrowed(usage)),
                    style,
                );
                if pre_types.len() == 0 {
                    return spec;
                }
                let parts = pre_types.iter().map(|t| t.format(format_data));
                if spec.is_empty() {
                    parts.collect()
                } else {
                    parts.chain(std::iter::once(spec)).collect()
                }
            }
            Self::Any(_) => return Box::from("..."),
        };
        let params = parts.join(", ");
        match style {
            ParamsStyle::CallableParams => format!("[{params}]").into(),
            _ => params.into(),
        }
    }

    pub(super) fn has_any_internal(
        &self,
        i_s: &InferenceState,
        already_checked: &mut Vec<Rc<RecursiveAlias>>,
    ) -> bool {
        match self {
            Self::Simple(params) => params.iter().any(|param| match &param.param_specific {
                ParamSpecific::PositionalOnly(t)
                | ParamSpecific::PositionalOrKeyword(t)
                | ParamSpecific::KeywordOnly(t)
                | ParamSpecific::Starred(StarredParamSpecific::ArbitraryLength(t))
                | ParamSpecific::DoubleStarred(DoubleStarredParamSpecific::ValueType(t)) => {
                    t.has_any_internal(i_s, already_checked)
                }
                ParamSpecific::Starred(StarredParamSpecific::ParamSpecArgs(_)) => false,
                ParamSpecific::DoubleStarred(DoubleStarredParamSpecific::ParamSpecKwargs(_)) => {
                    false
                }
            }),
            Self::WithParamSpec(pre_types, usage) => pre_types
                .iter()
                .any(|t| t.has_any_internal(i_s, already_checked)),
            Self::Any(_) => true,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct CallableContent {
    pub name: Option<DbString>,
    pub class_name: Option<StringSlice>,
    pub defined_at: PointLink,
    pub kind: FunctionKind,
    pub type_vars: TypeVarLikes,
    pub params: CallableParams,
    pub result_type: Type,
}

impl CallableContent {
    pub fn new_any(type_vars: TypeVarLikes) -> Self {
        Self::new_any_internal(PointLink::new(FileIndex(0), 0), type_vars)
    }

    pub fn name<'x>(&'x self, db: &'x Database) -> &'x str {
        self.name
            .as_ref()
            .map(|n| n.as_str(db))
            .unwrap_or("function")
    }

    fn new_any_internal(defined_at: PointLink, type_vars: TypeVarLikes) -> Self {
        Self {
            name: None,
            class_name: None,
            defined_at,
            kind: FunctionKind::Function {
                had_first_self_or_class_annotation: false,
            },
            type_vars,
            params: CallableParams::Any(AnyCause::Todo),
            result_type: Type::Any(AnyCause::Todo),
        }
    }
    pub fn new_any_with_defined_at(db: &Database, defined_at: PointLink) -> Self {
        Self::new_any_internal(defined_at, db.python_state.empty_type_var_likes.clone())
    }

    pub fn expect_simple_params(&self) -> &[CallableParam] {
        let CallableParams::Simple(params) = &self.params else {
            unreachable!()
        };
        params
    }

    pub fn remove_first_param(&self) -> Option<Self> {
        let mut c = self.clone();
        c.params = match &self.params {
            CallableParams::Simple(params) => {
                if params.len() == 0 {
                    todo!()
                }
                let mut params = params.to_vec();
                params.remove(0);
                CallableParams::Simple(params.into())
            }
            CallableParams::WithParamSpec(pre, usage) => {
                todo!()
            }
            CallableParams::Any(cause) => CallableParams::Any(*cause),
        };
        Some(c)
    }

    pub fn first_positional_type(&self) -> Option<Type> {
        match &self.params {
            CallableParams::Simple(params) => {
                params.first().and_then(|p| match &p.param_specific {
                    ParamSpecific::PositionalOnly(t) | ParamSpecific::PositionalOrKeyword(t) => {
                        Some(t.clone())
                    }
                    _ => todo!(),
                })
            }
            CallableParams::WithParamSpec(pre, usage) => {
                todo!()
            }
            CallableParams::Any(cause) => Some(Type::Any(*cause)),
        }
    }

    pub fn has_exactly_one_positional_parameter(&self) -> Option<WrongPositionalCount> {
        match &self.params {
            CallableParams::Simple(params) => match params.len() {
                0 => Some(WrongPositionalCount::TooFew),
                1 => None,
                _ => {
                    for param in params.iter().skip(1) {
                        if !param.has_default
                            && !matches!(
                                &param.param_specific,
                                ParamSpecific::Starred(_) | ParamSpecific::DoubleStarred(_)
                            )
                        {
                            return Some(WrongPositionalCount::TooMany);
                        }
                    }
                    None
                }
            },
            CallableParams::WithParamSpec(_, _) => Some(WrongPositionalCount::TooMany),
            CallableParams::Any(_) => None,
        }
    }

    pub(super) fn has_any_internal(
        &self,
        i_s: &InferenceState,
        already_checked: &mut Vec<Rc<RecursiveAlias>>,
    ) -> bool {
        self.result_type.has_any_internal(i_s, already_checked)
            || self.params.has_any_internal(i_s, already_checked)
    }

    pub fn has_self_type(&self) -> bool {
        self.result_type.has_self_type() || match &self.params {
            CallableParams::Simple(params) => {
                params.iter().any(|param| match &param.param_specific {
                    ParamSpecific::PositionalOnly(t)
                    | ParamSpecific::PositionalOrKeyword(t)
                    | ParamSpecific::KeywordOnly(t)
                    | ParamSpecific::Starred(StarredParamSpecific::ArbitraryLength(t))
                    | ParamSpecific::DoubleStarred(DoubleStarredParamSpecific::ValueType(t)) => {
                        t.has_self_type()
                    }
                    ParamSpecific::Starred(StarredParamSpecific::ParamSpecArgs(_)) => false,
                    ParamSpecific::DoubleStarred(DoubleStarredParamSpecific::ParamSpecKwargs(
                        _,
                    )) => false,
                })
            }
            CallableParams::Any(_) => false,
            CallableParams::WithParamSpec(types, param_spec) => {
                todo!()
            }
        }
    }

    pub fn format(&self, format_data: &FormatData) -> String {
        if format_data.style == FormatStyle::MypyRevealType {
            return self.format_pretty(format_data).into();
        }
        let result = self.result_type.format(format_data);
        let params = self.params.format(format_data, ParamsStyle::CallableParams);
        format!("Callable[{params}, {result}]")
    }

    pub fn format_pretty(&self, format_data: &FormatData) -> Box<str> {
        let db = format_data.db;
        let not_reveal_type = format_data.style != FormatStyle::MypyRevealType;
        let name = self
            .name
            .as_ref()
            .and_then(|s| not_reveal_type.then(|| s.as_str(db)))
            .unwrap_or("");
        match &self.params {
            CallableParams::Simple(params) => {
                let avoid_self_annotation = !self.kind.had_first_self_or_class_annotation();
                format_pretty_function_like(
                    format_data,
                    None,
                    avoid_self_annotation && not_reveal_type,
                    name,
                    &self.type_vars,
                    params.iter(),
                    Some(&self.result_type),
                )
            }
            CallableParams::WithParamSpec(pre_types, usage) => {
                if !pre_types.is_empty() {
                    todo!()
                }
                let spec = usage.param_spec.name(db);
                format_pretty_function_with_params(
                    format_data,
                    None,
                    &self.type_vars,
                    Some(&self.result_type),
                    name,
                    &format!("*{spec}.args, **{spec}.kwargs"),
                )
            }
            CallableParams::Any(_) => {
                let mut s = format!("def {name}(*Any, **Any)");
                if self.result_type != Type::None {
                    s += " -> ";
                    s += &self.result_type.format(format_data);
                }
                s.into()
            }
        }
    }

    pub fn merge_class_type_vars(
        &self,
        db: &Database,
        class: Class,
        attribute_class: Class,
    ) -> CallableContent {
        let mut needs_self_type_variable = self.result_type.has_self_type();
        for param in self.expect_simple_params().iter() {
            if let Some(t) = param.param_specific.maybe_type() {
                needs_self_type_variable |= t.has_self_type();
            }
        }
        let mut type_vars = self.type_vars.as_vec();
        let mut self_type_var_usage = None;
        for type_var in class.use_cached_type_vars(db).iter() {
            type_vars.push(type_var.clone());
        }
        if needs_self_type_variable {
            let bound = Class::with_self_generics(db, class.node_ref)
                .as_type(db)
                .replace_type_var_likes(db, &mut |mut usage| {
                    if usage.in_definition() == class.node_ref.as_link() {
                        usage.add_to_index(self.type_vars.len() as i32);
                    }
                    usage.into_generic_item()
                });
            let self_type_var = Rc::new(TypeVar {
                name_string: TypeVarName::Self_,
                kind: TypeVarKind::Bound(bound),
                variance: Variance::Invariant,
            });
            self_type_var_usage = Some(TypeVarUsage {
                in_definition: self.defined_at,
                type_var: self_type_var.clone(),
                index: type_vars.len().into(),
            });
            type_vars.push(TypeVarLike::TypeVar(self_type_var));
        }
        let type_vars = TypeVarLikes::from_vec(type_vars);
        let mut callable = Type::replace_type_var_likes_and_self_for_callable(
            self,
            db,
            &mut |usage| {
                let in_definition = usage.in_definition();
                if let Some(result) = maybe_class_usage(db, &attribute_class, &usage) {
                    result.replace_type_var_likes(
                        db,
                        &mut |usage| {
                            if usage.in_definition() == class.node_ref.as_link() {
                                type_vars
                                    .find(usage.as_type_var_like(), self.defined_at)
                                    .unwrap()
                                    .into_generic_item()
                            } else {
                                usage.into_generic_item()
                            }
                        },
                        &|| todo!("Type::TypeVar(self_type_var_usage.clone().unwrap())"),
                    )
                } else {
                    // This can happen for example if the return value is a Callable with its
                    // own type vars.
                    usage.into_generic_item()
                }
            },
            &|| Type::TypeVar(self_type_var_usage.clone().unwrap()),
        );
        callable.type_vars = type_vars;
        callable
    }
}

pub enum WrongPositionalCount {
    TooMany,
    TooFew,
}

pub fn format_callable_params<'db: 'x, 'x, P: Param<'x>>(
    format_data: &FormatData<'db, '_, '_, '_>,
    class: Option<Class>,
    avoid_self_annotation: bool,
    params: impl Iterator<Item = P>,
    show_additional_information: bool,
) -> String {
    let db = format_data.db;
    let mut previous_kind = None;
    let mut had_kwargs_separator = false;
    let mut args = join_with_commas(params.enumerate().map(|(i, p)| {
        let specific = p.specific(db);
        let annotation_str = match &specific {
            WrappedParamSpecific::PositionalOnly(t)
            | WrappedParamSpecific::PositionalOrKeyword(t)
            | WrappedParamSpecific::KeywordOnly(t)
            | WrappedParamSpecific::Starred(WrappedStarred::ArbitraryLength(t))
            | WrappedParamSpecific::DoubleStarred(WrappedDoubleStarred::ValueType(t)) => t
                .as_ref()
                .map(|t| format_function_type(format_data, t, class)),
            WrappedParamSpecific::Starred(WrappedStarred::ParamSpecArgs(u)) => todo!(),
            WrappedParamSpecific::DoubleStarred(WrappedDoubleStarred::ParamSpecKwargs(u)) => {
                todo!()
            }
        };
        let current_kind = p.kind(db);
        let stars = match current_kind {
            ParamKind::Starred => "*",
            ParamKind::DoubleStarred => "**",
            _ => "",
        };
        let mut out = if i == 0 && avoid_self_annotation && stars.is_empty() {
            p.name(db).unwrap().to_owned()
        } else {
            let mut out = if current_kind == ParamKind::PositionalOnly {
                annotation_str.unwrap_or_else(|| Box::from("Any")).into()
            } else if let Some(name) = p.name(db) {
                format!(
                    "{stars}{}: {}",
                    name,
                    annotation_str.as_deref().unwrap_or("Any")
                )
            } else {
                format!("{stars}{}", annotation_str.as_deref().unwrap_or("Any"))
            };
            if previous_kind == Some(ParamKind::PositionalOnly)
                && current_kind != ParamKind::PositionalOnly
                && show_additional_information
            {
                out = format!("/, {out}")
            }
            out
        };
        if matches!(&specific, WrappedParamSpecific::KeywordOnly(_)) && !had_kwargs_separator {
            had_kwargs_separator = true;
            out = format!("*, {out}");
        }
        had_kwargs_separator |= matches!(specific, WrappedParamSpecific::Starred(_));
        if p.has_default() {
            if show_additional_information {
                out += " = ...";
            } else {
                out += " =";
            }
        }
        previous_kind = Some(current_kind);
        out
    }));
    if previous_kind == Some(ParamKind::PositionalOnly) && show_additional_information {
        args += ", /";
    }
    args
}

fn format_pretty_function_like<'db: 'x, 'x, P: Param<'x>>(
    format_data: &FormatData<'db, '_, '_, '_>,
    class: Option<Class>,
    avoid_self_annotation: bool,
    name: &str,
    type_vars: &TypeVarLikes,
    params: impl Iterator<Item = P>,
    return_type: Option<&Type>,
) -> Box<str> {
    let params = format_callable_params(
        format_data,
        class,
        avoid_self_annotation,
        params,
        format_data.style != FormatStyle::MypyRevealType,
    );
    format_pretty_function_with_params(format_data, class, type_vars, return_type, name, &params)
}

fn format_pretty_function_with_params(
    format_data: &FormatData,
    class: Option<Class>,
    type_vars: &TypeVarLikes,
    return_type: Option<&Type>,
    name: &str,
    params: &str,
) -> Box<str> {
    let type_var_string = (!type_vars.is_empty()).then(|| type_vars.format(format_data));
    let type_var_str = type_var_string.as_deref().unwrap_or("");
    let result_string = return_type
        .as_ref()
        .filter(|t| format_data.style != FormatStyle::MypyRevealType || !matches!(t, Type::None))
        .map(|t| format_function_type(format_data, t, class));

    if let Some(result_string) = result_string {
        format!("def {type_var_str}{name}({params}) -> {result_string}").into()
    } else {
        format!("def {type_var_str}{name}({params})").into()
    }
}

fn format_function_type(format_data: &FormatData, t: &Type, class: Option<Class>) -> Box<str> {
    if let Some(func_class) = class {
        let t = t.replace_type_var_likes_and_self(
            format_data.db,
            &mut |usage| {
                maybe_class_usage(format_data.db, &func_class, &usage)
                    .unwrap_or_else(|| usage.into_generic_item())
            },
            &|| todo!(),
        );
        t.format(format_data)
    } else {
        t.format(format_data)
    }
}
