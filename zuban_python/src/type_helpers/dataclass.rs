use std::rc::Rc;

use parsa_python_ast::{
    AssignmentContent, AssignmentRightSide, ExpressionContent, ExpressionPart, ParamKind,
    PrimaryContent, StarExpressionContent,
};

use crate::{
    arguments::{Argument, ArgumentKind, Arguments, SimpleArguments},
    database::{Database, Specific},
    diagnostics::{Issue, IssueType},
    file::{File, PythonFile},
    inference_state::InferenceState,
    inferred::Inferred,
    matching::{
        calculate_callable_type_vars_and_return, replace_class_type_vars, LookupKind, LookupResult,
        OnTypeError, ResultContext,
    },
    node_ref::NodeRef,
    type_::{
        CallableContent, CallableParam, CallableParams, ClassGenerics, Dataclass, DataclassOptions,
        DbString, DbType, FunctionKind, GenericClass, Literal, LiteralKind, ParamSpecific,
        StringSlice, TupleContent, TypeOrTypeVarTuple, TypeVar, TypeVarKind,
    },
    type_helpers::Callable,
};

use super::{Class, Function, Instance, TypeOrClass};

const ORDER_METHOD_NAMES: [&'static str; 4] = ["__lt__", "__gt__", "__le__", "__ge__"];

pub fn check_dataclass_options<'db>(
    i_s: &InferenceState<'db, '_>,
    args: &SimpleArguments<'db, '_>,
) -> DataclassOptions {
    let mut options = DataclassOptions::default();
    let assign_option = |target: &mut _, arg: Argument<'db, '_>| {
        let result = arg.infer(i_s, &mut ResultContext::Unknown);
        if let Some(bool_) = result.maybe_bool_literal(i_s) {
            *target = bool_;
        } else {
            todo!()
        }
    };
    for arg in args.iter() {
        if let Some(key) = arg.keyword_name(i_s.db) {
            match key {
                "kw_only" => assign_option(&mut options.kw_only, arg),
                "frozen" => assign_option(&mut options.frozen, arg),
                "order" => assign_option(&mut options.order, arg),
                "eq" => assign_option(&mut options.eq, arg),
                "init" => assign_option(&mut options.init, arg),
                "match_args" => assign_option(&mut options.match_args, arg),
                "slots" => assign_option(&mut options.slots, arg),
                _ => (),
            }
        } else {
            todo!("{:?}", arg)
        }
    }
    if !options.eq && options.order {
        options.eq = true;
        args.as_node_ref()
            .add_issue(i_s, IssueType::DataclassOrderEnabledButNotEq);
    }
    options
}

pub struct DataclassHelper<'a>(pub &'a Rc<Dataclass>);

impl<'a> DataclassHelper<'a> {
    pub fn initialize<'db>(
        &self,
        i_s: &InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError<'db, '_>,
    ) -> Inferred {
        let class = self.0.class(i_s.db);
        let __init__ = Dataclass::__init__(self.0, i_s.db);
        let class_generics =
            if !self.0.options.init || class.lookup_symbol(i_s, "__init__").is_some() {
                // If the class has an __init__ method defined, the class itself wins.
                class.execute(i_s, args, result_context, on_type_error);
                return Inferred::from_type(DbType::Dataclass(self.0.clone()));
            } else {
                calculate_callable_type_vars_and_return(
                    i_s,
                    Callable::new(__init__, Some(class)),
                    args.iter(),
                    &|| args.as_node_ref(),
                    false,
                    result_context,
                    Some(on_type_error),
                )
            };
        Inferred::from_type(DbType::Dataclass(if self.0.has_defined_generics() {
            self.0.clone()
        } else {
            Dataclass::new(
                GenericClass {
                    link: self.0.class.link,
                    generics: class_generics.type_arguments_into_class_generics(),
                },
                self.0.options,
            )
        }))
    }

    pub fn lookup_on_type(
        &self,
        i_s: &InferenceState,
        from: NodeRef,
        name: &str,
        kind: LookupKind,
    ) -> LookupResult {
        if name == "__dataclass_fields__" && kind == LookupKind::Normal {
            return LookupResult::UnknownName(Inferred::from_type(
                i_s.db.python_state.dataclass_fields_type.clone(),
            ));
        }
        if self.0.options.order && ORDER_METHOD_NAMES.contains(&name) && kind == LookupKind::Normal
        {
            return self.order_func(i_s, true);
        }
        self.0.class(i_s.db).lookup(i_s, from, name, kind)
    }

    pub fn lookup(&self, i_s: &InferenceState, from: NodeRef, name: &str) -> LookupResult {
        if name == "__dataclass_fields__" {
            return LookupResult::UnknownName(Inferred::from_type(
                i_s.db.python_state.dataclass_fields_type.clone(),
            ));
        } else if name == "__match_args__" && self.0.options.match_args {
            let __init__ = Dataclass::__init__(self.0, i_s.db);
            let tup = Rc::new(TupleContent::new_fixed_length(
                __init__
                    .expect_simple_params()
                    .iter()
                    .take_while(|p| p.param_specific.maybe_positional_db_type().is_some())
                    .map(|p| {
                        TypeOrTypeVarTuple::Type(DbType::Literal(Literal::new(
                            LiteralKind::String(DbString::StringSlice(p.name.unwrap())),
                        )))
                    })
                    .collect(),
            ));
            return LookupResult::UnknownName(Inferred::from_type(DbType::Tuple(tup)));
        }
        if self.0.options.order && ORDER_METHOD_NAMES.contains(&name) {
            return self.order_func(i_s, false);
        }
        if self.0.options.slots {
            todo!()
        }
        Instance::new(self.0.class(i_s.db), None)
            .lookup(i_s, from, name, LookupKind::Normal)
            .and_then(|inf| match inf.as_type(i_s).as_ref() {
                // Init vars are not actually available on the class. They are just passed to __init__
                // and are not class members.
                DbType::Class(c) if c.link == i_s.db.python_state.dataclasses_init_var_link() => {
                    None
                }
                _ => Some(inf),
            })
            .unwrap_or(LookupResult::None)
    }

    pub fn lookup_symbol<'db: 'a>(
        &self,
        i_s: &InferenceState<'db, '_>,
        name: &str,
    ) -> (Option<Class<'a>>, LookupResult) {
        if self.0.options.init && name == "__init__" {
            return (
                None,
                LookupResult::UnknownName(Inferred::from_type(DbType::Callable(Rc::new(
                    Dataclass::__init__(self.0, i_s.db).clone(),
                )))),
            );
        }
        let class = self.0.class(i_s.db);
        (Some(class), class.lookup_symbol(i_s, name))
    }

    fn order_func(&self, i_s: &InferenceState, from_type: bool) -> LookupResult {
        return LookupResult::UnknownName(Inferred::from_type(DbType::Callable(Rc::new(
            CallableContent {
                name: None,
                class_name: None,
                defined_at: self.0.class.link,
                kind: FunctionKind::Function {
                    had_first_self_or_class_annotation: false,
                },
                type_vars: i_s.db.python_state.empty_type_var_likes.clone(),
                params: CallableParams::Simple(Rc::new([CallableParam {
                    param_specific: ParamSpecific::PositionalOnly(DbType::Dataclass(
                        self.0.clone(),
                    )),
                    name: None,
                    has_default: false,
                }])),
                result_type: i_s.db.python_state.bool_db_type(),
            },
        ))));
    }
}

pub fn calculate_init_of_dataclass(db: &Database, dataclass: &Rc<Dataclass>) -> CallableContent {
    let cls = dataclass.class(db);
    let mut with_indexes = vec![];
    let i_s = &InferenceState::new(db);
    let cls_i_s = &i_s.with_class_context(&cls);
    let file = cls.node_ref.file;
    let mut inference = file.inference(&cls_i_s);

    let mut params: Vec<CallableParam> = vec![];

    let add_param = |params: &mut Vec<CallableParam>, new_param: CallableParam| {
        let mut first_kwarg = None;
        for (i, param) in params.iter_mut().enumerate() {
            if first_kwarg.is_none()
                && param.param_specific.param_kind() == ParamKind::KeywordOnly
                && new_param.param_specific.param_kind() == ParamKind::PositionalOrKeyword
            {
                first_kwarg = Some(i);
            }
            if param.name.unwrap().as_str(db) == new_param.name.unwrap().as_str(db) {
                *param = new_param;
                return;
            }
        }
        if let Some(index) = first_kwarg {
            params.insert(index, new_param);
        } else {
            params.push(new_param)
        }
    };

    for (_, c) in cls.mro(db).rev() {
        if let TypeOrClass::Type(t) = c {
            if let DbType::Dataclass(super_dataclass) = t.as_ref() {
                if dataclass.options.frozen != super_dataclass.options.frozen {
                    let arguments = cls.node().arguments().unwrap();
                    NodeRef::new(file, arguments.index()).add_issue(
                        i_s,
                        match dataclass.options.frozen {
                            false => IssueType::DataclassCannotInheritNonFrozenFromFrozen,
                            true => IssueType::DataclassCannotInheritFrozenFromNonFrozen,
                        },
                    );
                }
                let cls = super_dataclass.class(db);
                for param in Dataclass::__init__(super_dataclass, db)
                    .expect_simple_params()
                    .iter()
                {
                    let mut new_param = param.clone();
                    let t = match &mut new_param.param_specific {
                        ParamSpecific::PositionalOrKeyword(t) | ParamSpecific::KeywordOnly(t) => t,
                        _ => unreachable!(),
                    };
                    *t = replace_class_type_vars(db, t, &cls, &|| {
                        DbType::Dataclass(dataclass.clone())
                    });
                    add_param(&mut params, new_param);
                }
            }
        }
    }

    for (_, name_index) in unsafe {
        cls.class_storage
            .class_symbol_table
            .iter_on_finished_table()
    } {
        let name = NodeRef::new(file, *name_index).as_name();
        if let Some(assignment) = name.maybe_assignment_definition_name() {
            if let AssignmentContent::WithAnnotation(_, annotation, right_side) =
                assignment.unpack()
            {
                let field_infos = calculate_field_arg(i_s, file, right_side);
                inference.cache_assignment_nodes(assignment);
                let point = file.points.get(annotation.index());
                if point.maybe_specific() == Some(Specific::AnnotationOrTypeCommentClassVar) {
                    // ClassVar[] are not part of the dataclass.
                    continue;
                }
                let mut t = inference
                    .use_cached_annotation_type(annotation)
                    .into_db_type();
                if let DbType::Class(c) = &t {
                    if c.link == db.python_state.dataclasses_init_var_link() {
                        t = c.class(db).nth_type_argument(db, 0);
                    }
                }
                /*
                TODO?
                if !matches!(dataclass.class.generics, ClassGenerics::NotDefinedYet | ClassGenerics::None) {
                    t = replace_class_type_vars(db, &t, &cls, &|| todo!());
                }
                */
                with_indexes.push((
                    *name_index,
                    t,
                    StringSlice::from_name(cls.node_ref.file_index(), name),
                    field_infos,
                ));
            }
        }
    }

    // The name indexes are not guarantueed to be sorted by its order in the tree. We however
    // want the original order in an enum.
    with_indexes.sort_by_key(|w| w.0);

    let mut had_kw_only_marker = false;
    for (node_index, t, name, field_infos) in with_indexes.into_iter() {
        match t {
            DbType::Class(c) if c.link == db.python_state.dataclasses_kw_only_link() => {
                if had_kw_only_marker {
                    NodeRef::new(file, node_index)
                        .add_issue(i_s, IssueType::DataclassMultipleKwOnly);
                } else {
                    had_kw_only_marker = true;
                }
            }
            _ => {
                let kw_only = field_infos
                    .kw_only
                    .unwrap_or_else(|| dataclass.options.kw_only || had_kw_only_marker);
                if field_infos.init {
                    add_param(
                        &mut params,
                        CallableParam {
                            param_specific: match kw_only {
                                false => ParamSpecific::PositionalOrKeyword(t),
                                true => ParamSpecific::KeywordOnly(t),
                            },
                            name: Some(name),
                            has_default: field_infos.has_default,
                        },
                    );
                }
            }
        }
    }
    let mut latest_default_issue = None;
    for (prev_param, (i, next_param)) in params.iter().zip(params.iter().enumerate().skip(1)) {
        if next_param.param_specific.param_kind() == ParamKind::PositionalOrKeyword
            && prev_param.has_default
            && !next_param.has_default
        {
            if latest_default_issue.is_none() {
                let name = next_param.name.unwrap();
                let issue_type = IssueType::DataclassNoDefaultAfterDefault;
                if name.file_index == file.file_index() {
                    file.add_issue(i_s, Issue::from_string_slice(name, issue_type));
                } else {
                    // The class arguments are always set, because we are working with params from
                    // a different file, which means inheritance.
                    let arguments = cls.node().arguments().unwrap();
                    NodeRef::new(file, arguments.index()).add_issue(i_s, issue_type);
                }
            }
            latest_default_issue = Some(i);
        }
    }
    if let Some(issue_index) = latest_default_issue {
        // Just reset the other params so that we have a valid signature again.
        for param in params[..issue_index].iter_mut() {
            param.has_default = false;
        }
    }
    if dataclass.options.order {
        for method_name in ORDER_METHOD_NAMES {
            if let Some(node_index) = cls
                .class_storage
                .class_symbol_table
                .lookup_symbol(method_name)
            {
                NodeRef::new(file, node_index).add_issue(
                    i_s,
                    IssueType::DataclassCustomOrderMethodNotAllowed { method_name },
                );
            }
        }
    }
    CallableContent {
        name: Some(cls.name_string_slice()),
        class_name: None,
        defined_at: cls.node_ref.as_link(),
        kind: FunctionKind::Function {
            had_first_self_or_class_annotation: true,
        },
        type_vars: match &dataclass.class.generics {
            ClassGenerics::NotDefinedYet => cls.use_cached_type_vars(db).clone(),
            _ => i_s.db.python_state.empty_type_var_likes.clone(),
        },
        params: CallableParams::Simple(params.into()),
        result_type: DbType::Any,
    }
}

struct FieldOptions {
    has_default: bool,
    kw_only: Option<bool>,
    init: bool,
}

fn calculate_field_arg(
    i_s: &InferenceState,
    file: &PythonFile,
    right_side: Option<AssignmentRightSide>,
) -> FieldOptions {
    if let Some(AssignmentRightSide::StarExpressions(star_exprs)) = right_side {
        if let StarExpressionContent::Expression(expr) = star_exprs.unpack() {
            if let ExpressionContent::ExpressionPart(ExpressionPart::Primary(primary)) =
                expr.unpack()
            {
                if let PrimaryContent::Execution(details) = primary.second() {
                    // TODO hack executing this before actually using it, makes sure that we are
                    // not in a class context and it does not cross polute it that way. This should
                    // be cleaned up once the name binder was reworked.
                    Function::new(
                        NodeRef::from_link(i_s.db, i_s.db.python_state.dataclasses_field_link()),
                        None,
                    )
                    .decorated(&InferenceState::new(i_s.db));

                    let left = file.inference(i_s).infer_primary_or_atom(primary.first());
                    if left.maybe_saved_link() == Some(i_s.db.python_state.dataclasses_field_link())
                    {
                        let args = SimpleArguments::new(*i_s, file, primary.index(), details);
                        return field_options_from_args(i_s, args);
                    }
                }
            }
        }
    }
    FieldOptions {
        has_default: right_side.is_some(),
        kw_only: None,
        init: true,
    }
}

fn field_options_from_args<'db>(
    i_s: &InferenceState<'db, '_>,
    args: SimpleArguments<'db, '_>,
) -> FieldOptions {
    let mut options = FieldOptions {
        has_default: false,
        kw_only: None,
        init: true,
    };
    for arg in args.iter() {
        if let Some(key) = arg.keyword_name(i_s.db) {
            match key {
                "default" | "default_factory" => options.has_default = true,
                "kw_only" => {
                    let result = arg.infer(i_s, &mut ResultContext::Unknown);
                    if let Some(bool_) = result.maybe_bool_literal(i_s) {
                        options.kw_only = Some(bool_);
                    } else {
                        todo!()
                    }
                }
                "init" => {
                    let result = arg.infer(i_s, &mut ResultContext::Unknown);
                    if let Some(bool_) = result.maybe_bool_literal(i_s) {
                        options.init = bool_
                    } else {
                        ()
                    }
                }
                _ => (), // Type checking is done in a separate place.
            }
        }
    }
    options
}

pub fn dataclasses_replace<'db>(
    i_s: &InferenceState<'db, '_>,
    args: &dyn Arguments<'db>,
    result_context: &mut ResultContext,
    on_type_error: OnTypeError<'db, '_>,
    bound: Option<&DbType>,
) -> Inferred {
    debug_assert!(bound.is_none());

    let mut arg_iterator = args.iter();
    if let Some(first) = arg_iterator.next() {
        if let ArgumentKind::Positional { node_ref, .. } = &first.kind {
            let inferred = first.infer(i_s, &mut ResultContext::Unknown);
            if run_on_dataclass(
                i_s,
                Some(*node_ref),
                &inferred.as_type(i_s),
                &mut |dataclass| {
                    let mut replace_func = Dataclass::__init__(dataclass, i_s.db).clone();
                    let mut params: Vec<_> = replace_func.expect_simple_params().into();
                    for param in params.iter_mut() {
                        let t = param.param_specific.maybe_db_type().unwrap();
                        param.param_specific = ParamSpecific::KeywordOnly(t.clone());
                        // All normal dataclass arguments are optional, because they can be
                        // overridden or just be left in place. However this is different for
                        // InitVars, which always need to be there. To check if something is an
                        // InitVar, we use this hack and check if the attribute exists on the
                        // dataclass. If not, it's an InitVar.
                        if DataclassHelper(dataclass)
                            .lookup(i_s, args.as_node_ref(), param.name.unwrap().as_str(i_s.db))
                            .is_some()
                        {
                            param.has_default = true;
                        }
                    }
                    params.insert(
                        0,
                        CallableParam {
                            param_specific: ParamSpecific::PositionalOnly(DbType::Any),
                            name: None,
                            has_default: false,
                        },
                    );
                    replace_func.params = CallableParams::Simple(params.into());
                    Callable::new(&replace_func, Some(dataclass.class(i_s.db))).execute_internal(
                        i_s,
                        args,
                        false,
                        on_type_error.with_custom_generate_diagnostic_string(&|_, _| {
                            Some(format!(
                                r#""replace" of "{}""#,
                                dataclass.class(i_s.db).format_short(i_s.db)
                            ))
                        }),
                        &mut ResultContext::Unknown,
                    );
                },
            ) {
                return inferred;
            } else {
                return Inferred::new_any();
            }
            // All other cases are checked by the type checker that uses the typeshed stubs.
        }
    }
    // Execute the original function (in typeshed).
    return i_s.db.python_state.dataclasses_replace().execute(
        i_s,
        args,
        result_context,
        on_type_error,
    );
}

fn run_on_dataclass(
    i_s: &InferenceState,
    from: Option<NodeRef>,
    t: &DbType,
    callback: &mut impl FnMut(&Rc<Dataclass>),
) -> bool {
    // Result type signals if we were successful
    let type_var_error = |tv: &TypeVar| {
        if let Some(from) = from {
            from.add_issue(
                i_s,
                IssueType::DataclassReplaceExpectedDataclassInTypeVarBound {
                    got: tv.name(i_s.db).into(),
                },
            );
        }
        false
    };
    match t {
        DbType::Dataclass(d) => {
            callback(d);
            true
        }
        DbType::Union(u) => u.iter().all(|t| run_on_dataclass(i_s, from, t, callback)),
        DbType::Any => true,
        DbType::TypeVar(tv) => match &tv.type_var.kind {
            TypeVarKind::Bound(bound) => {
                let result = run_on_dataclass(i_s, None, bound, callback);
                if !result {
                    type_var_error(&tv.type_var);
                }
                result
            }
            TypeVarKind::Constraints(_) => todo!(),
            TypeVarKind::Unrestricted => type_var_error(&tv.type_var),
        },
        _ => {
            if let Some(from) = from {
                from.add_issue(
                    i_s,
                    IssueType::DataclassReplaceExpectedDataclass {
                        got: t.format_short(i_s.db),
                    },
                );
            }
            false
        }
    }
}
