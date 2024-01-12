use std::{cell::OnceCell, iter::repeat_with, rc::Rc};

use parsa_python_ast::{
    AssignmentContent, AssignmentRightSide, ExpressionContent, ExpressionPart, NodeIndex,
    ParamKind, PrimaryContent, StarExpressionContent,
};

use super::{
    AnyCause, CallableContent, CallableParam, CallableParams, ClassGenerics, DbString,
    FunctionKind, GenericClass, Literal, LiteralKind, ParamType, StringSlice, Tuple, Type, TypeVar,
    TypeVarKind, TypeVarLike, TypeVarLikes, TypeVarName, TypeVarUsage, Variance,
};
use crate::{
    arguments::{Arg, ArgKind, Args, SimpleArgs},
    database::{Database, Locality, Point, Specific},
    diagnostics::{Issue, IssueType},
    file::{File, PythonFile},
    inference_state::InferenceState,
    inferred::{AttributeKind, Inferred},
    matching::{
        calculate_callable_type_vars_and_return, replace_class_type_vars, LookupKind, LookupResult,
        OnTypeError, ResultContext,
    },
    node_ref::NodeRef,
    python_state::NAME_TO_FUNCTION_DIFF,
    type_::{StarParamType, StarStarParamType},
    type_helpers::{Callable, Class, Function, Instance, LookupDetails, TypeOrClass},
};

const ORDER_METHOD_NAMES: [&'static str; 4] = ["__lt__", "__gt__", "__le__", "__ge__"];

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct DataclassOptions {
    pub init: bool,
    pub eq: bool,
    pub order: bool,
    pub frozen: bool,
    pub match_args: bool,
    pub kw_only: bool,
    pub slots: bool,
    // the keyword arguments `weakref_slot = false` and `repr = true` are ignored here, because
    // they are not relevant for us as a typechecker.
}

impl Default for DataclassOptions {
    fn default() -> Self {
        Self {
            init: true,
            eq: true,
            order: false,
            frozen: false,
            match_args: true,
            kw_only: false,
            slots: false,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Dataclass {
    pub class: GenericClass,
    __init__: OnceCell<CallableContent>,
    __post_init__: OnceCell<CallableContent>,
    pub options: DataclassOptions,
}

impl Dataclass {
    pub fn new(class: GenericClass, options: DataclassOptions) -> Rc<Self> {
        Rc::new(Self {
            class,
            __init__: OnceCell::new(),
            __post_init__: OnceCell::new(),
            options,
        })
    }

    pub fn class<'a>(&'a self, db: &'a Database) -> Class<'a> {
        self.class.class(db)
    }

    pub fn has_defined_generics(&self) -> bool {
        !matches!(self.class.generics, ClassGenerics::NotDefinedYet)
    }

    pub fn expect_calculated_post_init(&self) -> &CallableContent {
        self.__post_init__.get().unwrap()
    }
}

struct InitResult {
    __init__: CallableContent,
    __post_init__: CallableContent,
}

fn calculate_init_of_dataclass(db: &Database, dataclass: &Rc<Dataclass>) -> InitResult {
    let cls = dataclass.class(db);
    let mut with_indexes = vec![];
    let i_s = &InferenceState::new(db);
    let cls_i_s = &i_s.with_class_context(&cls);
    let file = cls.node_ref.file;
    let mut inference = file.inference(&cls_i_s);

    let mut params: Vec<CallableParam> = vec![];
    let mut post_init_params: Vec<CallableParam> = vec![];

    let add_param = |params: &mut Vec<CallableParam>, new_param: CallableParam| {
        let mut first_kwarg = None;
        for (i, param) in params.iter_mut().enumerate() {
            if first_kwarg.is_none()
                && param.type_.param_kind() == ParamKind::KeywordOnly
                && new_param.type_.param_kind() == ParamKind::PositionalOrKeyword
            {
                first_kwarg = Some(i);
            }
            if param.name.as_ref().unwrap().as_str(db)
                == new_param.name.as_ref().unwrap().as_str(db)
            {
                *param = new_param;
                return false;
            }
        }
        if let Some(index) = first_kwarg {
            params.insert(index, new_param);
        } else {
            params.push(new_param)
        }
        true
    };

    let class_symbol_table = &cls.class_storage.class_symbol_table;
    for (_, c) in cls.mro(db).rev() {
        if let TypeOrClass::Type(t) = c {
            if let Type::Dataclass(super_dataclass) = t.as_ref() {
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
                let init = dataclass_init_func(super_dataclass, db);
                let post_init = super_dataclass.__post_init__.get().unwrap();
                for param in init.expect_simple_params().iter() {
                    let mut new_param = param.clone();
                    let t = match &mut new_param.type_ {
                        ParamType::PositionalOrKeyword(t) | ParamType::KeywordOnly(t) => t,
                        // Comes from an incomplete_mro
                        ParamType::Star(_) | ParamType::StarStar(_) => continue,
                        _ => unreachable!(),
                    };
                    *t = replace_class_type_vars(db, t, &cls, &|| {
                        Type::Dataclass(dataclass.clone())
                    });
                    let cloned_name = new_param.name.clone().unwrap();
                    let param_name = cloned_name.as_str(db);
                    if let Some(in_current_class) = class_symbol_table.lookup_symbol(param_name) {
                        let mut n = NodeRef::new(file, in_current_class);
                        if !n
                            .as_name()
                            .name_definition()
                            .unwrap()
                            .maybe_assignment_definition()
                        {
                            if let Some(funcdef) =
                                NodeRef::new(file, in_current_class - NAME_TO_FUNCTION_DIFF)
                                    .maybe_function()
                            {
                                if let Some(decorated) = funcdef.maybe_decorated() {
                                    n = NodeRef::new(file, decorated.index());
                                }
                            }
                            if n.point().calculated()
                                && n.point().maybe_specific() == Some(Specific::DecoratedFunction)
                            {
                                // Mypy adds the issue to the decorator
                            }
                            n.add_issue(
                                i_s,
                                IssueType::DataclassAttributeMayOnlyBeOverriddenByAnotherAttribute,
                            );
                        }
                    }
                    if add_param(&mut params, new_param) {
                        for p in post_init.expect_simple_params() {
                            if p.name.as_ref().unwrap().as_str(db) == param_name {
                                post_init_params.push(p.clone());
                                break;
                            }
                        }
                    }
                }
            }
        }
    }

    struct Annotated {
        name_index: NodeIndex,
        t: Type,
        name: StringSlice,
        field_options: FieldOptions,
        is_init_var: bool, // e.g. InitVar[int]
    }

    for (_, name_index) in unsafe { class_symbol_table.iter_on_finished_table() } {
        let name = NodeRef::new(file, *name_index).as_name();
        if let Some(assignment) = name.maybe_assignment_definition_name() {
            if let AssignmentContent::WithAnnotation(target, annotation, right_side) =
                assignment.unpack()
            {
                inference.ensure_cached_annotation(annotation, right_side.is_some());
                let field_options = calculate_field_arg(i_s, file, right_side);
                let point = file.points.get(annotation.index());
                match point.maybe_specific() {
                    Some(Specific::AnnotationOrTypeCommentClassVar) => {
                        // ClassVar[] are not part of the dataclass.
                        continue;
                    }
                    Some(Specific::TypingTypeAlias) => {
                        NodeRef::new(file, assignment.index())
                            .add_issue(i_s, IssueType::DataclassContainsTypeAlias);
                        continue;
                    }
                    _ => (),
                }
                let mut t = inference
                    .use_cached_annotation_type(annotation)
                    .into_owned();
                let mut is_init_var = false;
                if let Type::Class(c) = &t {
                    if c.link == db.python_state.dataclasses_init_var_link() {
                        t = c.class(db).nth_type_argument(db, 0);
                        is_init_var = true;
                    }
                }
                /*
                TODO?
                if !matches!(dataclass.class.generics, ClassGenerics::NotDefinedYet | ClassGenerics::None) {
                    t = replace_class_type_vars(db, &t, &cls, &|| todo!());
                }
                */
                if let Some(right_side) = right_side {
                    // Since an InitVar is special and actually not checked against defaults, we
                    // need to check for this separately and tell the inference that this was
                    // already done.
                    inference.check_right_side_against_annotation(&t, right_side);
                    inference.assign_for_annotation(
                        annotation,
                        target,
                        NodeRef::new(file, right_side.index()),
                    );
                    file.points
                        .set(assignment.index(), Point::new_node_analysis(Locality::Todo));
                }
                with_indexes.push(Annotated {
                    name_index: *name_index,
                    t,
                    name: StringSlice::from_name(cls.node_ref.file_index(), name),
                    field_options,
                    is_init_var,
                });
            }
        }
    }

    // The name indexes are not guarantueed to be sorted by its order in the tree. We however
    // want the original order in an enum.
    with_indexes.sort_by_key(|w| w.name_index);

    let mut had_kw_only_marker = false;
    for infos in with_indexes.into_iter() {
        match infos.t {
            Type::Class(c) if c.link == db.python_state.dataclasses_kw_only_link() => {
                if had_kw_only_marker {
                    NodeRef::new(file, infos.name_index)
                        .add_issue(i_s, IssueType::DataclassMultipleKwOnly);
                } else {
                    had_kw_only_marker = true;
                }
            }
            _ => {
                let kw_only = infos
                    .field_options
                    .kw_only
                    .unwrap_or_else(|| dataclass.options.kw_only || had_kw_only_marker);
                if infos.is_init_var {
                    post_init_params.push(CallableParam {
                        // This is what Mypy uses, apparently for practical reasons.
                        type_: ParamType::PositionalOrKeyword(infos.t.clone()),
                        name: Some(infos.name.into()),
                        has_default: false,
                    })
                }
                if infos.field_options.init {
                    add_param(
                        &mut params,
                        CallableParam {
                            type_: match kw_only {
                                false => ParamType::PositionalOrKeyword(infos.t),
                                true => ParamType::KeywordOnly(infos.t),
                            },
                            name: Some(infos.name.into()),
                            has_default: infos.field_options.has_default,
                        },
                    );
                }
            }
        }
    }
    let mut latest_default_issue = None;
    for (prev_param, (i, next_param)) in params.iter().zip(params.iter().enumerate().skip(1)) {
        if next_param.type_.param_kind() == ParamKind::PositionalOrKeyword
            && prev_param.has_default
            && !next_param.has_default
        {
            if latest_default_issue.is_none() {
                let name = next_param.name.as_ref().unwrap();
                let issue_type = IssueType::DataclassNoDefaultAfterDefault;
                let DbString::StringSlice(name) = name else {
                    unreachable!();
                };
                if name.file_index == file.file_index() {
                    file.add_issue(i_s, Issue::from_string_slice(*name, issue_type));
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
    if cls.incomplete_mro(i_s.db) {
        params.push(CallableParam {
            type_: ParamType::Star(StarParamType::ArbitraryLen(Type::Any(AnyCause::Todo))),
            name: None,
            has_default: false,
        });
        params.push(CallableParam {
            type_: ParamType::StarStar(StarStarParamType::ValueType(Type::Any(AnyCause::Todo))),
            name: None,
            has_default: false,
        });
    }
    InitResult {
        __init__: CallableContent {
            name: Some(DbString::StringSlice(cls.name_string_slice())),
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
            return_type: Type::Any(AnyCause::Todo),
        },
        __post_init__: CallableContent {
            name: Some(DbString::Static("__post_init__")),
            class_name: None,
            defined_at: cls.node_ref.as_link(),
            kind: FunctionKind::Function {
                had_first_self_or_class_annotation: true,
            },
            type_vars: i_s.db.python_state.empty_type_var_likes.clone(),
            params: CallableParams::Simple(post_init_params.into()),
            return_type: Type::None,
        },
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
                        let args = SimpleArgs::new(*i_s, file, primary.index(), details);
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
    args: SimpleArgs<'db, '_>,
) -> FieldOptions {
    let mut options = FieldOptions {
        has_default: false,
        kw_only: None,
        init: true,
    };
    for arg in args.iter() {
        if matches!(arg.kind, ArgKind::Inferred { .. }) {
            arg.add_issue(i_s, IssueType::DataclassUnpackingKwargsInField);
            continue;
        }
        if let Some(key) = arg.keyword_name(i_s.db) {
            match key {
                "default" | "default_factory" => options.has_default = true,
                "kw_only" => {
                    let result = arg.infer_inferrable(i_s, &mut ResultContext::Unknown);
                    if let Some(bool_) = result.maybe_bool_literal(i_s) {
                        options.kw_only = Some(bool_);
                    } else {
                        todo!()
                    }
                }
                "init" => {
                    let result = arg.infer_inferrable(i_s, &mut ResultContext::Unknown);
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

pub fn check_dataclass_options<'db>(
    i_s: &InferenceState<'db, '_>,
    args: &SimpleArgs<'db, '_>,
) -> DataclassOptions {
    let mut options = DataclassOptions::default();
    let assign_option = |target: &mut _, arg: Arg<'db, '_>| {
        let result = arg.infer_inferrable(i_s, &mut ResultContext::Unknown);
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
        args.add_issue(i_s, IssueType::DataclassOrderEnabledButNotEq);
    }
    options
}

pub(crate) fn dataclasses_replace<'db>(
    i_s: &InferenceState<'db, '_>,
    args: &dyn Args<'db>,
    result_context: &mut ResultContext,
    on_type_error: OnTypeError<'db, '_>,
    bound: Option<&Type>,
) -> Inferred {
    debug_assert!(bound.is_none());

    let mut arg_iterator = args.iter();
    if let Some(first) = arg_iterator.next() {
        if let ArgKind::Positional(positional) = &first.kind {
            let inferred = positional.infer(i_s, &mut ResultContext::Unknown);
            if run_on_dataclass(
                i_s,
                Some(positional.node_ref),
                &inferred.as_cow_type(i_s),
                &mut |dataclass| {
                    let mut replace_func = dataclass_init_func(dataclass, i_s.db).clone();
                    let mut params: Vec<_> = replace_func.expect_simple_params().into();
                    for param in params.iter_mut() {
                        let t = param.type_.maybe_type().unwrap();
                        param.type_ = ParamType::KeywordOnly(t.clone());
                        // All normal dataclass arguments are optional, because they can be
                        // overridden or just be left in place. However this is different for
                        // InitVars, which always need to be there. To check if something is an
                        // InitVar, we use this hack and check if the attribute exists on the
                        // dataclass. If not, it's an InitVar.
                        if lookup_on_dataclass(
                            dataclass,
                            i_s,
                            |issue| args.add_issue(i_s, issue),
                            param.name.as_ref().unwrap().as_str(i_s.db),
                        )
                        .lookup
                        .is_some()
                        {
                            param.has_default = true;
                        }
                    }
                    params.insert(
                        0,
                        CallableParam {
                            type_: ParamType::PositionalOnly(Type::Any(AnyCause::Todo)),
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
                // Error is raised by the type checker
                return Inferred::new_any_from_error();
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
    t: &Type,
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
        Type::Dataclass(d) => {
            callback(d);
            true
        }
        Type::Union(u) => u.iter().all(|t| run_on_dataclass(i_s, from, t, callback)),
        Type::Any(_) => true,
        Type::TypeVar(tv) => match &tv.type_var.kind {
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

pub(crate) fn dataclass_initialize<'db>(
    dataclass: &Rc<Dataclass>,
    i_s: &InferenceState<'db, '_>,
    args: &dyn Args<'db>,
    result_context: &mut ResultContext,
    on_type_error: OnTypeError<'db, '_>,
) -> Inferred {
    let class = dataclass.class(i_s.db);
    let __init__ = dataclass_init_func(dataclass, i_s.db);
    let class_generics =
        if !dataclass.options.init || class.lookup_symbol(i_s, "__init__").is_some() {
            // If the class has an __init__ method defined, the class itself wins.
            class.execute(i_s, args, result_context, on_type_error, true);
            return Inferred::from_type(Type::Dataclass(dataclass.clone()));
        } else {
            calculate_callable_type_vars_and_return(
                i_s,
                Callable::new(__init__, Some(class)),
                args.iter(),
                |issue| args.add_issue(i_s, issue),
                false,
                result_context,
                Some(on_type_error),
            )
        };
    Inferred::from_type(Type::Dataclass(if dataclass.has_defined_generics() {
        dataclass.clone()
    } else {
        Dataclass::new(
            GenericClass {
                link: dataclass.class.link,
                generics: class_generics.type_arguments_into_class_generics(),
            },
            dataclass.options,
        )
    }))
}

pub fn dataclass_init_func<'a>(self_: &'a Rc<Dataclass>, db: &Database) -> &'a CallableContent {
    if self_.__init__.get().is_none() {
        // Cannot use get_or_init, because this might cycle ones for some reasons (see for
        // example the test testDeferredDataclassInitSignatureSubclass)
        let result = calculate_init_of_dataclass(db, self_);
        self_.__init__.set(result.__init__).ok();
        self_.__post_init__.set(result.__post_init__).ok();
    }
    self_.__init__.get().unwrap()
}

pub(crate) fn lookup_on_dataclass_type<'a>(
    self_: &'a Rc<Dataclass>,
    i_s: &'a InferenceState,
    add_issue: impl Fn(IssueType),
    name: &str,
    kind: LookupKind,
) -> LookupDetails<'a> {
    if name == "__dataclass_fields__" && kind == LookupKind::Normal {
        return LookupDetails::new(
            Type::Dataclass(self_.clone()),
            LookupResult::UnknownName(Inferred::from_type(
                i_s.db.python_state.dataclass_fields_type.clone(),
            )),
            AttributeKind::Attribute,
        );
    }
    if self_.options.order && ORDER_METHOD_NAMES.contains(&name) && kind == LookupKind::Normal {
        return LookupDetails::new(
            Type::Dataclass(self_.clone()),
            type_order_func(self_.clone(), i_s),
            AttributeKind::Attribute,
        );
    }
    if name == "__slots__" && self_.options.slots {
        return LookupDetails::new(
            Type::Dataclass(self_.clone()),
            LookupResult::UnknownName(Inferred::from_type(Type::Tuple(Tuple::new_fixed_length(
                repeat_with(|| i_s.db.python_state.str_type())
                    .take(
                        dataclass_init_func(&self_, i_s.db)
                            .expect_simple_params()
                            .len(),
                    )
                    .collect(),
            )))),
            AttributeKind::Attribute,
        );
    }
    self_
        .class(i_s.db)
        .lookup_with_details(i_s, add_issue, name, kind)
}

pub fn lookup_symbol_internal(
    self_: Rc<Dataclass>,
    i_s: &InferenceState<'_, '_>,
    name: &str,
) -> (LookupResult, AttributeKind) {
    if name == "__dataclass_fields__" {
        return (
            LookupResult::UnknownName(Inferred::from_type(
                i_s.db.python_state.dataclass_fields_type.clone(),
            )),
            AttributeKind::ClassVar,
        );
    } else if name == "__match_args__" && self_.options.match_args {
        let __init__ = dataclass_init_func(&self_, i_s.db);
        let tup = Tuple::new_fixed_length(
            __init__
                .expect_simple_params()
                .iter()
                .take_while(|p| p.type_.maybe_positional_type().is_some())
                .map(|p| Type::Literal(Literal::new(LiteralKind::String(p.name.clone().unwrap()))))
                .collect(),
        );
        return (
            LookupResult::UnknownName(Inferred::from_type(Type::Tuple(tup))),
            AttributeKind::DefMethod,
        );
    }
    if self_.options.order && ORDER_METHOD_NAMES.contains(&name) {
        return (order_func(self_.clone(), i_s), AttributeKind::DefMethod);
    }
    if self_.options.slots {
        todo!()
    }
    if self_.options.init && name == "__init__" {
        return (
            LookupResult::UnknownName(Inferred::from_type(Type::Callable(Rc::new(
                dataclass_init_func(&self_, i_s.db).clone(),
            )))),
            AttributeKind::DefMethod,
        );
    }
    (LookupResult::None, AttributeKind::Attribute)
}

pub fn lookup_dataclass_symbol<'db: 'a, 'a>(
    self_: &'a Rc<Dataclass>,
    i_s: &InferenceState<'db, '_>,
    name: &str,
) -> (Option<Class<'a>>, LookupResult) {
    let result = lookup_symbol_internal(self_.clone(), i_s, name).0;
    if result.is_some() {
        return (None, result);
    }
    let class = self_.class(i_s.db);
    (Some(class), class.lookup_symbol(i_s, name))
}

pub(crate) fn lookup_on_dataclass<'a>(
    self_: &'a Rc<Dataclass>,
    i_s: &'a InferenceState,
    add_issue: impl Fn(IssueType),
    name: &str,
) -> LookupDetails<'a> {
    let (result, attr_kind) = lookup_symbol_internal(self_.clone(), i_s, name);
    if result.is_some() {
        return LookupDetails::new(Type::Dataclass(self_.clone()), result, attr_kind);
    }
    let mut lookup_details = Instance::new(self_.class(i_s.db), None).lookup_with_details(
        i_s,
        add_issue,
        name,
        LookupKind::Normal,
    );
    lookup_details.lookup = lookup_details
        .lookup
        .and_then(|inf| match inf.as_cow_type(i_s).as_ref() {
            // Init vars are not actually available on the class. They are just passed to __init__
            // and are not class members.
            Type::Class(c) if c.link == i_s.db.python_state.dataclasses_init_var_link() => None,
            _ => Some(inf),
        })
        .unwrap_or(LookupResult::None);
    lookup_details
}

fn order_func(self_: Rc<Dataclass>, i_s: &InferenceState) -> LookupResult {
    return LookupResult::UnknownName(Inferred::from_type(Type::Callable(Rc::new(
        CallableContent {
            name: None,
            class_name: None,
            defined_at: self_.class.link,
            kind: FunctionKind::Function {
                had_first_self_or_class_annotation: false,
            },
            type_vars: i_s.db.python_state.empty_type_var_likes.clone(),
            params: CallableParams::Simple(Rc::new([CallableParam {
                type_: ParamType::PositionalOnly(Type::Dataclass(self_)),
                name: None,
                has_default: false,
            }])),
            return_type: i_s.db.python_state.bool_type(),
        },
    ))));
}

fn type_order_func(self_: Rc<Dataclass>, i_s: &InferenceState) -> LookupResult {
    let type_var = Rc::new(TypeVar {
        name_string: TypeVarName::Self_,
        kind: TypeVarKind::Unrestricted,
        variance: Variance::Invariant,
    });
    let tv_usage = TypeVarUsage {
        type_var: type_var.clone(),
        index: 0.into(),
        in_definition: self_.class.link,
    };
    return LookupResult::UnknownName(Inferred::from_type(Type::Callable(Rc::new(
        CallableContent {
            name: None,
            class_name: None,
            defined_at: self_.class.link,
            kind: FunctionKind::Function {
                had_first_self_or_class_annotation: false,
            },
            type_vars: TypeVarLikes::new(Rc::new([TypeVarLike::TypeVar(type_var)])),
            params: CallableParams::Simple(Rc::new([
                CallableParam {
                    type_: ParamType::PositionalOnly(Type::TypeVar(tv_usage.clone())),
                    name: Some(DbString::Static("self")),
                    has_default: false,
                },
                CallableParam {
                    type_: ParamType::PositionalOnly(Type::TypeVar(tv_usage)),
                    name: Some(DbString::Static("other")),
                    has_default: false,
                },
            ])),
            return_type: i_s.db.python_state.bool_type(),
        },
    ))));
}
