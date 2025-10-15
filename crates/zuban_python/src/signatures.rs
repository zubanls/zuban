use std::sync::Arc;

use parsa_python_cst::{ExpressionPart, SignatureArg, SignatureArgsIterator};

use crate::{
    InputPosition,
    database::Database,
    debug,
    file::{File as _, PythonFile},
    format_data::FormatData,
    goto::{PositionalDocument, with_i_s_non_self},
    inference_state::InferenceState,
    params::Param as _,
    type_::{
        CallableContent, CallableLike, CallableParam, CallableParams, ParamType, ParamTypeDetails,
        Type,
    },
};

struct SignatureInfo<'db> {
    base: ExpressionPart<'db>,
    args: SignatureArgsIterator<'db>,
}

impl<'db> PositionalDocument<'db, SignatureInfo<'db>> {
    pub fn for_signature(
        db: &'db Database,
        file: &'db PythonFile,
        pos: InputPosition,
    ) -> anyhow::Result<Option<Self>> {
        let cursor_position = file.line_column_to_byte(pos)?;
        let Some((scope, base, args)) = file.tree.signature_node(cursor_position.byte) else {
            return Ok(None);
        };
        let result = file.ensure_calculated_diagnostics(db);
        debug!(
            "Signature on position {}->{pos:?} on node {base:?}",
            file.file_path(db),
        );
        debug_assert!(result.is_ok());
        Ok(Some(Self {
            db,
            file,
            scope,
            node: SignatureInfo { base, args },
        }))
    }
}

pub(crate) struct SignatureResolver<'db> {
    infos: PositionalDocument<'db, SignatureInfo<'db>>,
    signatures: Vec<Arc<CallableContent>>,
}

impl<'db> SignatureResolver<'db> {
    pub fn call_signatures(
        db: &'db Database,
        file: &'db PythonFile,
        position: InputPosition,
    ) -> anyhow::Result<Option<CallSignatures<'db>>> {
        let _panic_context = utils::panic_context::enter(format!(
            "completions for {} position {position:?}",
            file.file_path(db)
        ));
        let infos = PositionalDocument::for_signature(db, file, position)?;
        Ok(infos.map(|infos| {
            with_i_s_non_self(db, file, infos.scope, |i_s| {
                let base = file.inference(i_s).infer_expression_part(infos.node.base);
                let mut slf = Self {
                    signatures: Default::default(),
                    infos,
                };
                for t in base.as_cow_type(i_s).iter_with_unpacked_unions(i_s.db) {
                    slf.add_types(i_s, t);
                }
                CallSignatures {
                    db,
                    callables: slf.signatures,
                    args: slf.infos.node.args,
                }
            })
        }))
    }

    fn add_types(&mut self, i_s: &InferenceState, t: &Type) {
        match t.maybe_callable(i_s) {
            Some(CallableLike::Callable(c)) => self.add_callable(c.clone()),
            Some(CallableLike::Overload(o)) => {
                for c in o.iter_functions() {
                    self.add_callable(c.clone())
                }
            }
            None => (),
        }
    }

    fn add_callable(&mut self, callable: Arc<CallableContent>) {
        self.signatures.push(callable)
    }
}

pub struct CallSignatures<'db> {
    db: &'db Database,
    args: SignatureArgsIterator<'db>,
    callables: Vec<Arc<CallableContent>>,
}

impl<'db> CallSignatures<'db> {
    pub fn into_iterator(self) -> impl Iterator<Item = CallSignature> {
        let db = self.db;
        self.callables.into_iter().map(move |callable| {
            let mut is_valid_with_arguments = true;
            let mut current_param = None;

            let mut calc_current_param = |params: &[CallableParam]| {
                let mut expected_positional = 0;
                let mut for_kwarg = None;
                let mut used_kwargs = vec![];
                let mut had_kwargs = false;
                let mut had_star_args = false;
                let mut potential_keyword_starts_with = None;
                for arg in self.args.clone() {
                    potential_keyword_starts_with = None;
                    for_kwarg = None;
                    match arg {
                        SignatureArg::PositionalOrEmptyAfterComma => {
                            expected_positional += 1;
                        }
                        SignatureArg::PositionalOrKeywordName(name) => {
                            expected_positional += 1;
                            potential_keyword_starts_with = Some(name)
                        }
                        SignatureArg::Keyword(name) => {
                            used_kwargs.push(name.as_code());
                            for_kwarg = Some(name);
                            had_kwargs = true;
                        }
                        SignatureArg::StarArgs => had_star_args = true,
                        SignatureArg::StarStarKwargs => {
                            for_kwarg = None;
                            had_kwargs = true
                        }
                    }
                }
                expected_positional += had_star_args as isize;
                debug!(
                    "The call signature arguments are expected_positional: \
                    {expected_positional:?}, for_kwarg: {for_kwarg:?}, used_kwargs: \
                    {used_kwargs:?}, had_kwargs: {had_kwargs:?}, potential_keyword_starts_with: \
                    {potential_keyword_starts_with:?}"
                );
                if let Some(for_kwarg) = for_kwarg {
                    for (i, param) in params.iter().enumerate() {
                        match &param.type_ {
                            ParamType::PositionalOnly(_) | ParamType::Star(_) => continue,
                            ParamType::PositionalOrKeyword(_) | ParamType::KeywordOnly(_) => {
                                if let Some(name) = param.name(db) {
                                    if name == for_kwarg.as_code() {
                                        return Some(i);
                                    }
                                }
                            }
                            ParamType::StarStar(_) => {
                                return Some(i);
                            }
                        }
                    }
                    is_valid_with_arguments = false;
                    None
                } else {
                    for (i, param) in params.iter().enumerate() {
                        match &param.type_ {
                            ParamType::PositionalOnly(_) | ParamType::PositionalOrKeyword(_)
                                if !had_kwargs =>
                            {
                                expected_positional -= 1;
                                if !had_kwargs && expected_positional <= 0 {
                                    return Some(i);
                                }
                            }
                            ParamType::PositionalOnly(_) => {
                                if !had_star_args {
                                    is_valid_with_arguments = false;
                                }
                            }
                            ParamType::PositionalOrKeyword(_) => {
                                if let Some(name) = param.name(db) {
                                    if used_kwargs.contains(&name) {
                                        continue;
                                    }
                                }
                                expected_positional -= 1;
                                if expected_positional <= 0 {
                                    return Some(i);
                                }
                            }
                            ParamType::KeywordOnly(_) => {
                                if let Some(name) = param.name(db) {
                                    if used_kwargs.contains(&name) {
                                        continue;
                                    }
                                    if let Some(potential) = potential_keyword_starts_with {
                                        if name.starts_with(potential) {
                                            return Some(i);
                                        }
                                    } else {
                                        return Some(i);
                                    }
                                }
                            }
                            ParamType::Star(_) => {
                                if !had_kwargs {
                                    return Some(i);
                                }
                                //expected_positional = 0;  ?
                            }
                            ParamType::StarStar(_) => {
                                return Some(i);
                            }
                        }
                    }
                    is_valid_with_arguments = false;
                    None
                }
            };
            let (params, params_label) = match &callable.params {
                CallableParams::Simple(params) => {
                    current_param = calc_current_param(params);
                    let mut label = String::new();
                    // This formatting is a bit different from format_pretty and it's fine to have
                    // it this way, because the user has different needs here. The signature should
                    // be as small as possible and generics are probably not that important.
                    let param_strs = params
                        .iter()
                        .map(|p| {
                            let type_ = match p.type_.details() {
                                ParamTypeDetails::Type(t) => t.format_short(db),
                                ParamTypeDetails::ParamSpecUsage(u) => u.param_spec.name(db).into(),
                                ParamTypeDetails::UnpackedTuple(tup) => {
                                    tup.format(&FormatData::new_short(db))
                                }
                                ParamTypeDetails::UnpackTypedDict(_) => "<UnpackTypedDict>".into(),
                            };
                            if !label.is_empty() {
                                label += ", ";
                            }
                            match &p.type_ {
                                ParamType::Star(_) => label.push('*'),
                                ParamType::StarStar(_) => label += "**",
                                _ => (),
                            }
                            let param_out = if let Some(name) = p.name(db) {
                                label += name;
                                label += ": ";
                                label += &type_;
                                name.into()
                            } else {
                                label += &type_;
                                type_
                            };
                            if p.has_default() {
                                label += " ="
                            }
                            param_out
                        })
                        .collect();
                    (Some(param_strs), label)
                }
                CallableParams::Any(_) => (None, "".into()),
                CallableParams::Never(_) => (Some(vec![]), "*Any, **Any".into()),
            };
            CallSignature {
                label: format!(
                    "({params_label}) -> {}",
                    callable.return_type.format_short(db)
                )
                .into_boxed_str(),
                params,
                is_valid_with_arguments,
                current_param,
            }
        })
    }
}

pub struct CallSignature {
    pub label: Box<str>,
    pub params: Option<Vec<Box<str>>>,
    pub is_valid_with_arguments: bool,
    pub current_param: Option<usize>,
}
