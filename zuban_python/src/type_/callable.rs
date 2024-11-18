use std::{borrow::Cow, rc::Rc};

use parsa_python_cst::ParamKind;

use super::{
    AnyCause, DbString, FunctionKind, NeverCause, ParamSpecUsage, RecursiveType, StringSlice,
    Tuple, Type, TypeVar, TypeVarKind, TypeVarLike, TypeVarLikes, TypeVarName, TypeVarUsage,
    TypedDict, Variance,
};
use crate::{
    database::{Database, FileIndex, PointLink},
    format_data::{FormatData, ParamsStyle},
    inference_state::InferenceState,
    matching::{maybe_class_usage, Generics},
    params::{
        params_have_self_type_after_self, Param, WrappedParamType, WrappedStar, WrappedStarStar,
    },
    type_::{FormatStyle, TupleArgs, TypeVarLikeUsage},
    type_helpers::{Class, TypeOrClass},
    utils::join_with_commas,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum StarParamType {
    ArbitraryLen(Type),
    ParamSpecArgs(ParamSpecUsage),
    UnpackedTuple(Rc<Tuple>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum StarStarParamType {
    ValueType(Type),
    ParamSpecKwargs(ParamSpecUsage),
    UnpackTypedDict(Rc<TypedDict>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ParamType {
    PositionalOnly(Type),
    PositionalOrKeyword(Type),
    KeywordOnly(Type),
    Star(StarParamType),
    StarStar(StarStarParamType),
}

impl ParamType {
    pub fn param_kind(&self) -> ParamKind {
        match self {
            Self::PositionalOnly(_) => ParamKind::PositionalOnly,
            Self::PositionalOrKeyword(_) => ParamKind::PositionalOrKeyword,
            Self::KeywordOnly(_) => ParamKind::KeywordOnly,
            Self::Star(_) => ParamKind::Star,
            Self::StarStar(_) => ParamKind::StarStar,
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
            | Self::Star(StarParamType::ArbitraryLen(t))
            | Self::StarStar(StarStarParamType::ValueType(t)) => Some(t),
            Self::Star(_) | Self::StarStar(_) => None,
        }
    }

    pub fn maybe_param_spec(&self) -> Option<&ParamSpecUsage> {
        match self {
            Self::Star(StarParamType::ParamSpecArgs(p)) => Some(p),
            Self::StarStar(StarStarParamType::ParamSpecKwargs(p)) => Some(p),
            _ => None,
        }
    }

    pub fn details(&self) -> ParamTypeDetails {
        match self {
            Self::PositionalOnly(t)
            | Self::PositionalOrKeyword(t)
            | Self::KeywordOnly(t)
            | Self::Star(StarParamType::ArbitraryLen(t))
            | Self::StarStar(StarStarParamType::ValueType(t)) => ParamTypeDetails::Type(t),
            Self::Star(StarParamType::ParamSpecArgs(usage)) => {
                ParamTypeDetails::ParamSpecUsage(usage)
            }
            Self::Star(StarParamType::UnpackedTuple(tup)) => {
                ParamTypeDetails::UnpackedTuple(tup.clone())
            }
            Self::StarStar(StarStarParamType::ParamSpecKwargs(usage)) => {
                ParamTypeDetails::ParamSpecUsage(usage)
            }
            Self::StarStar(StarStarParamType::UnpackTypedDict(td)) => {
                ParamTypeDetails::UnpackTypedDict(td.clone())
            }
        }
    }
}

pub enum ParamTypeDetails<'a> {
    Type(&'a Type),
    ParamSpecUsage(&'a ParamSpecUsage),
    UnpackedTuple(Rc<Tuple>),
    UnpackTypedDict(Rc<TypedDict>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CallableParam {
    pub type_: ParamType,
    pub name: Option<DbString>,
    pub has_default: bool,
}

impl CallableParam {
    pub fn new_anonymous(type_: ParamType) -> Self {
        CallableParam {
            type_,
            name: None,
            has_default: false,
        }
    }

    pub fn similar_kind_and_keyword_if_kw_param(&self, db: &Database, other: &Self) -> bool {
        use ParamType::*;
        match &self.type_ {
            PositionalOnly(_) | PositionalOrKeyword(_) => {
                matches!(&other.type_, PositionalOnly(_) | PositionalOrKeyword(_))
            }
            KeywordOnly(_) => {
                matches!(&other.type_, KeywordOnly(_))
                    && self
                        .name
                        .as_ref()
                        .zip(other.name.as_ref())
                        .is_some_and(|(n1, n2)| n1.as_str(db) == n2.as_str(db))
            }
            Star(_) => matches!(&other.type_, Star(_)),
            StarStar(_) => matches!(&other.type_, StarStar(_)),
        }
    }

    pub fn format(&self, format_data: &FormatData) -> Box<str> {
        if !matches!(self.type_, ParamType::PositionalOnly(_))
            || format_data.verbose && self.has_default
        {
            if let ParamType::Star(t) = &self.type_ {
                return match t {
                    StarParamType::ArbitraryLen(t) => {
                        format!("VarArg({})", t.format(format_data))
                    }
                    StarParamType::ParamSpecArgs(u) => unreachable!(),
                    StarParamType::UnpackedTuple(tup) => {
                        if let Some(matcher) = format_data.matcher {
                            let tup_t = Type::Tuple(tup.clone());
                            let replaced = matcher.replace_type_var_likes_for_unknown_type_vars(
                                format_data.db,
                                &tup_t,
                            );
                            let Type::Tuple(tup) = replaced.as_ref() else {
                                unreachable!()
                            };
                            let result = tup.args.format(&format_data.remove_matcher());
                            match &tup.args {
                                TupleArgs::FixedLen(ts) if ts.is_empty() => "".to_owned(),
                                TupleArgs::FixedLen(ts) => result.into(),
                                _ => format!("VarArg(Unpack[Tuple[{result}]])"),
                            }
                        } else {
                            format!("VarArg({})", tup.format_with_simplified_unpack(format_data))
                        }
                    }
                }
                .into();
            } else if let ParamType::StarStar(t) = &self.type_ {
                return match t {
                    StarStarParamType::ValueType(t) => {
                        format!("KwArg({})", t.format(format_data))
                    }
                    StarStarParamType::UnpackTypedDict(td) => {
                        format!("**Unpack[{}]", td.format(format_data))
                    }
                    StarStarParamType::ParamSpecKwargs(_) => unreachable!(),
                }
                .into();
            } else if let Some(name) = self.name.as_ref() {
                match format_data.style {
                    FormatStyle::MypyRevealType => {
                        let mut string = match &self.type_ {
                            ParamType::PositionalOnly(t)
                            | ParamType::PositionalOrKeyword(t)
                            | ParamType::KeywordOnly(t) => {
                                format!(
                                    "{}: {}",
                                    name.as_str(format_data.db),
                                    t.format(format_data),
                                )
                            }
                            _ => unreachable!(), // Cases are handled above
                        };
                        if self.has_default {
                            string += " =";
                        }
                        return string.into();
                    }
                    FormatStyle::Short => {
                        return match &self.type_ {
                            ParamType::PositionalOnly(t) | ParamType::PositionalOrKeyword(t) => {
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
                            ParamType::KeywordOnly(t) => {
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
                            ParamType::Star(_) | ParamType::StarStar(_) => {
                                unreachable!()
                            }
                        }
                        .into();
                    }
                }
            } else if self.has_default {
                return match &self.type_ {
                    ParamType::PositionalOnly(t)
                    | ParamType::PositionalOrKeyword(t)
                    | ParamType::KeywordOnly(t) => {
                        format!("DefaultArg({})", t.format(format_data)).into()
                    }
                    _ => unreachable!(),
                };
            }
        }
        match &self.type_ {
            ParamType::PositionalOnly(t) => t.format(format_data),
            _ => unreachable!(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum CallableParams {
    Simple(Rc<[CallableParam]>),
    Any(AnyCause),
    Never(NeverCause),
}

impl CallableParams {
    pub fn new_simple(params: Rc<[CallableParam]>) -> Self {
        Self::Simple(params)
    }

    pub fn new_param_spec(p: ParamSpecUsage) -> Self {
        Self::Simple(Rc::new([
            CallableParam::new_anonymous(ParamType::Star(StarParamType::ParamSpecArgs(p.clone()))),
            CallableParam::new_anonymous(ParamType::StarStar(StarStarParamType::ParamSpecKwargs(
                p,
            ))),
        ]))
    }

    pub fn format(&self, format_data: &FormatData, style: ParamsStyle) -> Box<str> {
        let parts = match self {
            Self::Simple(params) => {
                if let Some(result) = format_params_as_param_spec(format_data, params) {
                    return result;
                }
                let mut out_params = Vec::with_capacity(params.len());
                // Display a star only if we are displaying a "normal" function signature
                for (i, param) in params.iter().enumerate() {
                    match &param.type_ {
                        ParamType::Star(StarParamType::ParamSpecArgs(usage)) => {
                            out_params.push(format_data.format_param_spec(usage, style));
                            // ParamSpecs are are always at the end
                            break;
                        }
                        _ => out_params.push(param.format(format_data)),
                    }
                }
                out_params
            }
            Self::Any(_) => return Box::from("..."),
            Self::Never(_) => return Box::from("Never"),
        };
        let params = parts.join(", ");
        match style {
            ParamsStyle::CallableParams => format!("[{params}]").into(),
            _ => params.into(),
        }
    }

    pub fn has_any(&self, i_s: &InferenceState) -> bool {
        self.has_any_internal(i_s, &mut Vec::new())
    }

    pub(super) fn has_any_internal(
        &self,
        i_s: &InferenceState,
        already_checked: &mut Vec<Rc<RecursiveType>>,
    ) -> bool {
        match self {
            Self::Simple(params) => params.iter().any(|param| match &param.type_ {
                ParamType::PositionalOnly(t)
                | ParamType::PositionalOrKeyword(t)
                | ParamType::KeywordOnly(t)
                | ParamType::Star(StarParamType::ArbitraryLen(t))
                | ParamType::StarStar(StarStarParamType::ValueType(t)) => {
                    t.has_any_internal(i_s, already_checked)
                }
                ParamType::Star(StarParamType::ParamSpecArgs(_)) => false,
                ParamType::Star(StarParamType::UnpackedTuple(tup)) => {
                    tup.args.has_any_internal(i_s, already_checked)
                }
                ParamType::StarStar(StarStarParamType::ParamSpecKwargs(_)) => false,
                ParamType::StarStar(StarStarParamType::UnpackTypedDict(td)) => {
                    td.has_any_internal(i_s, already_checked)
                }
            }),
            Self::Any(_) => true,
            Self::Never(_) => false,
        }
    }

    pub fn is_any_args_and_kwargs(&self) -> bool {
        let Self::Simple(params) = self else {
            return false;
        };
        let mut iterator = params.iter();
        let Some(first) = iterator.next() else {
            return false;
        };
        if !matches!(
            &first.type_,
            ParamType::Star(StarParamType::ArbitraryLen(Type::Any(_)))
        ) {
            return false;
        }
        let Some(second) = iterator.next() else {
            return false;
        };
        matches!(
            &second.type_,
            ParamType::StarStar(StarStarParamType::ValueType(Type::Any(_)))
        )
    }

    pub fn maybe_param_spec(&self) -> Option<&ParamSpecUsage> {
        let Self::Simple(params) = self else {
            return None;
        };
        params.last()?.type_.maybe_param_spec()
    }

    pub fn search_type_vars<C: FnMut(TypeVarLikeUsage) + ?Sized>(&self, found_type_var: &mut C) {
        match self {
            Self::Simple(params) => {
                for param in params.iter() {
                    match &param.type_ {
                        ParamType::PositionalOnly(t)
                        | ParamType::PositionalOrKeyword(t)
                        | ParamType::KeywordOnly(t)
                        | ParamType::Star(StarParamType::ArbitraryLen(t))
                        | ParamType::StarStar(StarStarParamType::ValueType(t)) => {
                            t.search_type_vars(found_type_var)
                        }
                        ParamType::Star(StarParamType::UnpackedTuple(u)) => {
                            u.args.search_type_vars(found_type_var)
                        }
                        ParamType::Star(StarParamType::ParamSpecArgs(u)) => {
                            found_type_var(TypeVarLikeUsage::ParamSpec(u.clone()))
                        }
                        ParamType::StarStar(StarStarParamType::UnpackTypedDict(t)) => {
                            t.search_type_vars(found_type_var)
                        }
                        ParamType::StarStar(StarStarParamType::ParamSpecKwargs(_)) => {
                            // Do nothing here, because we already found it above.
                        }
                    }
                }
            }
            Self::Any(_) | Self::Never(_) => (),
        }
    }

    pub fn find_in_type(&self, db: &Database, check: &mut impl FnMut(&Type) -> bool) -> bool {
        match self {
            Self::Simple(params) => params.iter().any(|param| match &param.type_ {
                ParamType::PositionalOnly(t)
                | ParamType::PositionalOrKeyword(t)
                | ParamType::KeywordOnly(t)
                | ParamType::Star(StarParamType::ArbitraryLen(t))
                | ParamType::StarStar(StarStarParamType::ValueType(t)) => t.find_in_type(db, check),
                ParamType::Star(StarParamType::ParamSpecArgs(_)) => false,
                ParamType::Star(StarParamType::UnpackedTuple(u)) => u.find_in_type(db, check),
                ParamType::StarStar(StarStarParamType::ParamSpecKwargs(_)) => false,
                ParamType::StarStar(StarStarParamType::UnpackTypedDict(td)) => {
                    Type::TypedDict(td.clone()).find_in_type(db, check)
                }
            }),
            Self::Any(_) | Self::Never(_) => false,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CallableContent {
    pub name: Option<DbString>,
    pub class_name: Option<StringSlice>,
    pub defined_at: PointLink,
    pub kind: FunctionKind,
    pub type_vars: TypeVarLikes,
    pub params: CallableParams,
    pub guard: Option<TypeGuardInfo>,
    pub return_type: Type,
    pub is_abstract: bool,
    pub is_final: bool,
    pub no_type_check: bool, // Has a decorator with @typing.no_type_check
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TypeGuardInfo {
    pub type_: Type,
    pub from_type_is: bool, // true when TypeIs[...], false when TypeGuard[...]
}

impl TypeGuardInfo {
    pub fn format(&self, format_data: &FormatData) -> String {
        let name = if self.from_type_is {
            "TypeIs"
        } else {
            "TypeGuard"
        };
        format!("{name}[{}]", self.type_.format(format_data))
    }
}

impl CallableContent {
    pub fn new_simple(
        name: Option<DbString>,
        class_name: Option<StringSlice>,
        defined_at: PointLink,
        type_vars: TypeVarLikes,
        params: CallableParams,
        return_type: Type,
    ) -> Self {
        Self {
            name,
            class_name,
            defined_at,
            kind: FunctionKind::Function {
                had_first_self_or_class_annotation: true,
            },
            type_vars,
            params,
            guard: None,
            return_type,
            is_abstract: false,
            is_final: false,
            no_type_check: false,
        }
    }

    pub fn new_any(type_vars: TypeVarLikes, cause: AnyCause) -> Self {
        Self::new_any_internal(PointLink::new(FileIndex(0), 0), type_vars, cause)
    }

    pub fn name<'x>(&'x self, db: &'x Database) -> &'x str {
        self.name
            .as_ref()
            .map(|n| n.as_str(db))
            .unwrap_or("function")
    }

    fn new_any_internal(defined_at: PointLink, type_vars: TypeVarLikes, cause: AnyCause) -> Self {
        Self {
            name: None,
            class_name: None,
            defined_at,
            kind: FunctionKind::Function {
                had_first_self_or_class_annotation: false,
            },
            type_vars,
            params: CallableParams::Any(cause),
            guard: None,
            is_abstract: false,
            is_final: false,
            no_type_check: false,
            return_type: Type::Any(cause),
        }
    }
    pub fn new_any_with_defined_at(db: &Database, defined_at: PointLink, cause: AnyCause) -> Self {
        Self::new_any_internal(
            defined_at,
            db.python_state.empty_type_var_likes.clone(),
            cause,
        )
    }

    pub fn expect_simple_params(&self) -> &[CallableParam] {
        let CallableParams::Simple(params) = &self.params else {
            unreachable!()
        };
        params
    }

    pub fn remove_first_positional_param(&self) -> Option<Self> {
        let mut c = self.clone();
        c.params = match &self.params {
            CallableParams::Simple(params) => {
                if params.len() == 0 {
                    return None;
                }
                match &params[0].type_ {
                    ParamType::PositionalOnly(_) | ParamType::PositionalOrKeyword(_) => {
                        let mut params = params.to_vec();
                        params.remove(0);
                        CallableParams::Simple(params.into())
                    }
                    ParamType::Star(_) => return Some(c),
                    _ => return None,
                }
            }
            CallableParams::Any(cause) => CallableParams::Any(*cause),
            CallableParams::Never(cause) => CallableParams::Never(*cause),
        };
        Some(c)
    }

    pub fn first_positional_type(&self) -> Option<Type> {
        match &self.params {
            CallableParams::Simple(params) => params.first().and_then(|p| match &p.type_ {
                ParamType::PositionalOnly(t)
                | ParamType::PositionalOrKeyword(t)
                | ParamType::Star(StarParamType::ArbitraryLen(t)) => Some(t.clone()),
                ParamType::Star(StarParamType::UnpackedTuple(tup)) => {
                    let TupleArgs::WithUnpack(w) = &tup.args else {
                        return None;
                    };
                    if let Some(first) = w.before.first() {
                        return Some(first.clone());
                    }
                    Some(Type::Never(NeverCause::Other))
                }
                _ => None,
            }),
            CallableParams::Any(cause) => Some(Type::Any(*cause)),
            CallableParams::Never(cause) => Some(Type::Never(*cause)),
        }
    }

    pub fn second_positional_type(&self) -> Option<Type> {
        match &self.params {
            CallableParams::Simple(params) => {
                let mut iterator = params.iter();
                if let Some(first) = iterator.next() {
                    if let ParamType::Star(StarParamType::ArbitraryLen(t)) = &first.type_ {
                        return Some(t.clone());
                    }
                }
                iterator.next().and_then(|second| match &second.type_ {
                    ParamType::PositionalOnly(t)
                    | ParamType::PositionalOrKeyword(t)
                    | ParamType::Star(StarParamType::ArbitraryLen(t)) => Some(t.clone()),
                    _ => None,
                })
            }
            CallableParams::Any(cause) => Some(Type::Any(*cause)),
            CallableParams::Never(cause) => Some(Type::Never(*cause)),
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
                            && !matches!(&param.type_, ParamType::Star(_) | ParamType::StarStar(_))
                        {
                            return Some(WrongPositionalCount::TooMany);
                        }
                    }
                    None
                }
            },
            CallableParams::Any(_) | CallableParams::Never(_) => None,
        }
    }

    pub fn erase_func_type_vars_for_type<'x>(
        &self,
        db: &Database,
        type_: &'x Type,
    ) -> Cow<'x, Type> {
        if self.type_vars.is_empty() {
            Cow::Borrowed(type_)
        } else {
            let replaced = type_.replace_type_var_likes(db, &mut |usage| {
                if usage.in_definition() == self.defined_at {
                    Some(usage.as_any_generic_item())
                } else {
                    None
                }
            });
            replaced
                .map(Cow::Owned)
                .unwrap_or_else(|| Cow::Borrowed(type_))
        }
    }

    pub(super) fn has_any_internal(
        &self,
        i_s: &InferenceState,
        already_checked: &mut Vec<Rc<RecursiveType>>,
    ) -> bool {
        self.guard
            .as_ref()
            .is_some_and(|guard| guard.type_.has_any_internal(i_s, already_checked))
            || self.return_type.has_any_internal(i_s, already_checked)
            || self.params.has_any_internal(i_s, already_checked)
    }

    pub fn has_self_type(&self, db: &Database) -> bool {
        self.find_in_type(db, &mut |t| matches!(t, Type::Self_))
    }

    pub fn find_in_type(&self, db: &Database, check: &mut impl FnMut(&Type) -> bool) -> bool {
        self.guard
            .as_ref()
            .is_some_and(|guard| guard.type_.find_in_type(db, check))
            || self.return_type.find_in_type(db, check)
            || self.params.find_in_type(db, check)
    }

    pub fn format(&self, format_data: &FormatData) -> String {
        if format_data.style == FormatStyle::MypyRevealType {
            return self.format_pretty(format_data).into();
        }
        let result = if let Some(guard) = self.guard.as_ref() {
            guard.format(format_data).into()
        } else {
            self.return_type.format(format_data)
        };
        let params = self.params.format(format_data, ParamsStyle::CallableParams);
        format!("Callable[{params}, {result}]")
    }

    pub fn format_pretty(&self, format_data: &FormatData) -> Box<str> {
        let avoid_self_annotation = !self.kind.had_first_self_or_class_annotation();
        self.format_pretty_detailed(format_data, avoid_self_annotation, true)
    }

    pub fn format_pretty_detailed(
        &self,
        format_data: &FormatData,
        avoid_self_annotation: bool,
        add_classmethod_param: bool,
    ) -> Box<str> {
        match &self.params {
            CallableParams::Simple(params) => {
                let not_reveal_type = format_data.style != FormatStyle::MypyRevealType;
                let mut params = format_callable_params(
                    format_data,
                    avoid_self_annotation && not_reveal_type,
                    params.iter(),
                    format_data.style != FormatStyle::MypyRevealType,
                );
                if add_classmethod_param
                    && matches!(self.kind, FunctionKind::Classmethod { .. })
                    && not_reveal_type
                {
                    if params.is_empty() {
                        params = "cls".to_string();
                    } else {
                        params = "cls, ".to_string() + &params;
                    }
                }
                self.format_pretty_function_with_params(format_data, &params)
            }
            CallableParams::Any(_) => {
                self.format_pretty_function_with_params(format_data, "*Any, **Any")
            }
            CallableParams::Never(_) => "Never".into(),
        }
    }

    fn format_pretty_function_with_params(
        &self,
        format_data: &FormatData,
        params: &str,
    ) -> Box<str> {
        let name = self
            .name
            .as_ref()
            .and_then(|s| {
                (format_data.style != FormatStyle::MypyRevealType).then(|| s.as_str(format_data.db))
            })
            .unwrap_or("");
        let type_var_string =
            (!self.type_vars.is_empty()).then(|| self.type_vars.format(format_data));
        let type_var_str = type_var_string.as_deref().unwrap_or("");

        if format_data.style != FormatStyle::MypyRevealType
            || !matches!(self.return_type, Type::None)
        {
            let result_string = match self.guard.as_ref() {
                Some(guard) => guard.format(format_data).into(),
                None => self.return_type.format(format_data),
            };
            format!("def {type_var_str}{name}({params}) -> {result_string}").into()
        } else {
            format!("def {type_var_str}{name}({params})").into()
        }
    }

    fn has_self_type_after_first_param(&self, db: &Database) -> bool {
        self.return_type.has_self_type(db)
            || match &self.params {
                CallableParams::Simple(params) => {
                    params_have_self_type_after_self(db, params.iter())
                }
                CallableParams::Any(_) | CallableParams::Never(_) => false,
            }
    }

    pub fn is_typed(&self, skip_first_param: bool) -> bool {
        let has_unannotated = |t: &Type| matches!(t, Type::Any(AnyCause::Unannotated));
        if !has_unannotated(&self.return_type) {
            return true;
        }
        match &self.params {
            CallableParams::Simple(params) => !params
                .iter()
                .skip(skip_first_param.into())
                .all(|t| t.type_.maybe_type().is_some_and(has_unannotated)),
            CallableParams::Any(cause) => !matches!(cause, AnyCause::Unannotated),
            // Should probably never happen?!
            CallableParams::Never(_) => true,
        }
    }

    pub fn search_type_vars<C: FnMut(TypeVarLikeUsage) + ?Sized>(&self, found_type_var: &mut C) {
        self.params.search_type_vars(found_type_var);
        self.return_type.search_type_vars(found_type_var);
        if let Some(guard) = self.guard.as_ref() {
            guard.type_.search_type_vars(found_type_var)
        }
    }
}

pub enum WrongPositionalCount {
    TooMany,
    TooFew,
}

pub fn format_callable_params<'db: 'x, 'x, P: Param<'x>>(
    format_data: &FormatData<'db, '_, '_, '_>,
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
            WrappedParamType::PositionalOnly(t)
            | WrappedParamType::PositionalOrKeyword(t)
            | WrappedParamType::KeywordOnly(t)
            | WrappedParamType::Star(WrappedStar::ArbitraryLen(t))
            | WrappedParamType::StarStar(WrappedStarStar::ValueType(t)) => {
                t.as_ref().map(|t| t.format(format_data))
            }
            WrappedParamType::Star(WrappedStar::ParamSpecArgs(u)) => {
                Some(format!("{}.args", u.param_spec.name(db)).into())
            }
            WrappedParamType::Star(WrappedStar::UnpackedTuple(tup)) => {
                Some(tup.format_with_simplified_unpack(format_data))
            }
            WrappedParamType::StarStar(WrappedStarStar::UnpackTypedDict(td)) => {
                Some(format!("Unpack[{}]", td.format(format_data)).into())
            }
            WrappedParamType::StarStar(WrappedStarStar::ParamSpecKwargs(u)) => {
                Some(format!("{}.kwargs", u.param_spec.name(db)).into())
            }
        };
        let current_kind = p.kind(db);
        let stars = match current_kind {
            ParamKind::Star => "*",
            ParamKind::StarStar => "**",
            _ => "",
        };
        let mut out = if i == 0 && avoid_self_annotation && stars.is_empty() {
            p.name(db).unwrap_or("self").to_owned()
        } else {
            let mut out = if current_kind == ParamKind::PositionalOnly {
                annotation_str.unwrap_or_else(|| Box::from("Any")).into()
            } else if let Some(name) = p.name(db) {
                format!(
                    "{stars}{name}: {}",
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
        if matches!(&specific, WrappedParamType::KeywordOnly(_)) && !had_kwargs_separator {
            had_kwargs_separator = true;
            out = format!("*, {out}");
        }
        had_kwargs_separator |= matches!(specific, WrappedParamType::Star(_));
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

pub fn format_params_as_param_spec(
    format_data: &FormatData,
    params: &[CallableParam],
) -> Option<Box<str>> {
    let mut params_iter = params.iter();
    let last = params_iter.next_back()?;
    let p = last.type_.maybe_param_spec()?;
    params_iter.next_back()?;
    Some(if params.len() == 2 {
        format_data.format_param_spec(p, ParamsStyle::CallableParams)
    } else {
        let name = format_data.format_param_spec(p, ParamsStyle::CallableParamsInner);
        let ps = join_with_commas(params_iter.map(|p| {
            p.type_
                .expect_positional_type_as_ref()
                .format(format_data)
                .into()
        }));
        if name.is_empty() {
            format!("[{ps}]").into()
        } else {
            format!("[{ps}, {name}]").into()
        }
    })
}

pub fn merge_class_type_vars(
    db: &Database,
    callable: Rc<CallableContent>,
    class: Class,
    attribute_class: Class,
    func_class_type: &TypeOrClass,
) -> Rc<CallableContent> {
    let mut attribute_class = attribute_class; // A lifetime issue
    let needs_self_type_variable = callable.has_self_type_after_first_param(db);

    let mut type_vars = callable.type_vars.as_vec();
    let mut self_type_var_usage = None;
    let needs_additional_remap = matches!(attribute_class.generics, Generics::NotDefinedYet)
        && !class.use_cached_type_vars(db).is_empty();
    if needs_self_type_variable {
        let bound = func_class_type.as_type(db);
        /*
        let bound = attribute_class.as_type_with_type_vars_for_not_yet_defined_generics(db);
        let bound = class_t.replace_type_var_likes(db, &mut |usage| {
            (usage.in_definition() == class.node_ref.as_link()).then(|| {
                usage.add_to_index(callable.type_vars.len() as i32 + 1);
                usage.into_generic_item()
                //usage.as_any_generic_item()
            })
        }).unwrap_or(class_t);
        */
        let self_type_var = Rc::new(TypeVar {
            name_string: TypeVarName::Self_,
            kind: TypeVarKind::Bound(bound),
            default: None,
            variance: Variance::Invariant,
        });
        self_type_var_usage = Some(TypeVarUsage::new(
            self_type_var.clone(),
            callable.defined_at,
            type_vars.len().into(),
        ));
        type_vars.push(TypeVarLike::TypeVar(self_type_var));
    } else if needs_additional_remap {
        let attribute_class_type_vars = attribute_class.use_cached_type_vars(db);
        // We actually want to retain generics.
        attribute_class.generics = Generics::Self_ {
            class_definition: attribute_class.node_ref.as_link(),
            type_var_likes: attribute_class_type_vars,
        };
        for type_var in attribute_class_type_vars.iter() {
            type_vars.push(type_var.clone());
        }
    }

    let type_vars = TypeVarLikes::from_vec(type_vars);
    let remap_usage = |usage: TypeVarLikeUsage| {
        if usage.in_definition() == attribute_class.node_ref.as_link() {
            Some(
                type_vars
                    .find(usage.as_type_var_like(), callable.defined_at)?
                    .into_generic_item(),
            )
        } else {
            None
        }
    };
    let mut callable = callable.replace_type_var_likes_and_self(
        db,
        &mut |usage| {
            let in_definition = usage.in_definition();
            // The ? can happen for example if the return value is a Callable with its
            // own type vars.
            let result = maybe_class_usage(db, &attribute_class, &usage)?;
            if !needs_additional_remap {
                return Some(result);
            }
            Some(
                result
                    .replace_type_var_likes_and_self(db, &mut &remap_usage, &|| None)
                    .unwrap_or(result),
            )
        },
        &|| {
            Some(match &self_type_var_usage {
                Some(u) => Type::TypeVar(u.clone()),
                None => {
                    let t = func_class_type.as_type(db);
                    if !needs_additional_remap {
                        return Some(t);
                    }
                    t.replace_type_var_likes(db, &mut &remap_usage).unwrap_or(t)
                }
            })
        },
    );
    callable.type_vars = type_vars;
    Rc::new(callable)
}
