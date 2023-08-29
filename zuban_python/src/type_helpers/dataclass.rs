use std::rc::Rc;

use parsa_python_ast::AssignmentContent;

use crate::{
    arguments::{Argument, ArgumentKind, Arguments},
    database::{
        CallableContent, CallableParam, CallableParams, Dataclass, DataclassOptions, DbType,
        FunctionKind, ParamSpecific, StringSlice,
    },
    inference_state::InferenceState,
    inferred::Inferred,
    matching::{LookupKind, LookupResult, OnTypeError, ResultContext},
    node_ref::NodeRef,
    type_helpers::Callable,
};

use super::Class;

pub fn execute_dataclass<'db>(
    i_s: &InferenceState<'db, '_>,
    options: Option<DataclassOptions>,
    args: &dyn Arguments<'db>,
    on_type_error: OnTypeError,
) -> Inferred {
    let mut iterator = args.iter();
    if let Some(first) = iterator.next() {
        if matches!(
            first.kind,
            ArgumentKind::Positional { .. } | ArgumentKind::Inferred { .. }
        ) {
            if let Some(x) = iterator.next() {
                todo!()
            }
            if let Some(cls) = first
                .infer(i_s, &mut ResultContext::Unknown)
                .as_type(i_s)
                .maybe_type_of_class(i_s.db)
            {
                let options = options.unwrap_or(Default::default());
                let __init__ = calculate_init_of_dataclass(i_s, cls, options);
                return Inferred::from_type(DbType::Type(Rc::new(DbType::Dataclass(Rc::new(
                    Dataclass {
                        class: cls.node_ref.as_link(),
                        options,
                        // TODO this is quite obviously wrong.
                        __init__,
                    },
                )))));
            } else {
                todo!()
            }
        }
    }
    let mut options = DataclassOptions::default();
    let assign_option = |target: &mut _, arg: Argument<'db, '_>| {
        let result = arg.infer(i_s, &mut ResultContext::ExpectLiteral);
        if let Some(bool_) = result.maybe_bool_literal(i_s) {
            *target = bool_;
        } else {
            todo!()
        }
    };
    for arg in args.iter() {
        if let ArgumentKind::Keyword { key, .. } = &arg.kind {
            match *key {
                "kw_only" => assign_option(&mut options.kw_only, arg),
                _ => todo!("{key}"),
            }
        } else {
            todo!("{:?}", arg)
        }
    }
    Inferred::from_type(DbType::DataclassBuilder(options))
}

pub struct DataclassHelper<'a>(pub &'a Rc<Dataclass>);

impl DataclassHelper<'_> {
    pub fn initialize<'db>(
        &self,
        i_s: &InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError<'db, '_>,
    ) -> Inferred {
        Callable::new(&self.0.__init__, None).execute(i_s, args, on_type_error, result_context);
        Inferred::from_type(DbType::Dataclass(self.0.clone()))
    }

    pub fn lookup(&self, i_s: &InferenceState, from: NodeRef, name: &str) -> LookupResult {
        Class::from_non_generic_link(i_s.db, self.0.class).lookup(
            i_s,
            from,
            name,
            LookupKind::Normal,
        )
    }
}
pub fn calculate_init_of_dataclass(
    i_s: &InferenceState,
    cls: Class,
    options: DataclassOptions,
) -> CallableContent {
    let mut with_indexes = vec![];
    let cls_i_s = i_s.with_class_context(&cls);
    let mut inference = cls.node_ref.file.inference(&cls_i_s);

    let mut kw_only_marker = None;

    for (_, name_index) in unsafe {
        cls.class_storage
            .class_symbol_table
            .iter_on_finished_table()
    } {
        let name = NodeRef::new(cls.node_ref.file, *name_index).as_name();
        if let Some(assignment) = name.maybe_assignment_definition_name() {
            if let AssignmentContent::WithAnnotation(_, annotation, default) = assignment.unpack() {
                inference.cache_assignment_nodes(assignment);
                let t = inference
                    .use_cached_annotation_type(annotation)
                    .into_db_type();
                match t {
                    DbType::Class(c)
                        if c.link == i_s.db.python_state.dataclasses_kw_only_link() =>
                    {
                        kw_only_marker = Some(name_index);
                    }
                    _ => with_indexes.push((
                        *name_index,
                        CallableParam {
                            // TODO the type is wrong
                            param_specific: ParamSpecific::PositionalOrKeyword(t),
                            name: Some(StringSlice::from_name(cls.node_ref.file_index(), name)),
                            has_default: default.is_some(),
                        },
                    )),
                }
            }
        }
    }

    // The name indexes are not guarantueed to be sorted by its order in the tree. We however
    // want the original order in an enum.
    with_indexes.sort_by_key(|w| w.0);

    let mut params = vec![];
    for (node_index, mut param) in with_indexes.into_iter() {
        if options.kw_only || kw_only_marker.is_some_and(|index| node_index > *index) {
            // If it's not positional, it's already a keyword argument
            if let ParamSpecific::PositionalOrKeyword(t) = param.param_specific {
                param.param_specific = ParamSpecific::KeywordOnly(t);
            }
        }
        params.push(param);
    }
    CallableContent {
        name: Some(cls.name_string_slice()),
        class_name: None,
        defined_at: cls.node_ref.as_link(),
        kind: FunctionKind::Function,
        type_vars: i_s.db.python_state.empty_type_var_likes.clone(),
        params: CallableParams::Simple(params.into()),
        result_type: DbType::None,
    }
}
