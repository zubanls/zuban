use std::sync::Arc;

use parsa_python_cst::{ExpressionPart, SignatureArgsIterator};

use crate::{
    InputPosition,
    database::Database,
    debug,
    file::{File as _, PythonFile},
    format_data::FormatData,
    goto::{PositionalDocument, with_i_s_non_self},
    inference_state::InferenceState,
    type_::{CallableContent, CallableLike, CallableParams, ParamTypeDetails, Type},
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
        self.callables.into_iter().map(move |callable| {
            let format_data = &FormatData::new_short(self.db);
            for _ in self.args.clone() {
                // TODO
            }
            CallSignature {
                label: callable.format_pretty(format_data),
                params: match &callable.params {
                    CallableParams::Simple(params) => Some(
                        params
                            .iter()
                            .map(|p| {
                                p.name
                                    .as_ref()
                                    .map(|name| name.as_str(self.db).into())
                                    .unwrap_or_else(|| match p.type_.details() {
                                        ParamTypeDetails::Type(t) => t.format(format_data),
                                        ParamTypeDetails::ParamSpecUsage(_) => "<ParamSpec>".into(),
                                        ParamTypeDetails::UnpackedTuple(_) => {
                                            "<UnpackedTuple>".into()
                                        }
                                        ParamTypeDetails::UnpackTypedDict(_) => {
                                            "<UnpackTypedDict>".into()
                                        }
                                    })
                            })
                            .collect(),
                    ),
                    CallableParams::Any(_) => None,
                    CallableParams::Never(_) => Some(vec![]),
                },
                is_valid_with_arguments: true,
                current_param: None,
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
