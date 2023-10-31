use std::{cell::OnceCell, rc::Rc};

use parsa_python_ast::{
    AssignmentContent, AssignmentRightSide, ExpressionContent, ExpressionPart, ParamKind,
    PrimaryContent, StarExpressionContent,
};

use crate::{
    arguments::{Arguments, SimpleArguments},
    database::{Database, Specific},
    diagnostics::{Issue, IssueType},
    file::{File, PythonFile},
    inference_state::InferenceState,
    matching::{replace_class_type_vars, ResultContext},
    node_ref::NodeRef,
    type_helpers::{Class, Function, TypeOrClass},
};

use super::{
    CallableContent, CallableParam, CallableParams, ClassGenerics, DbString, FunctionKind,
    GenericClass, ParamSpecific, StringSlice, Type,
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
    pub options: DataclassOptions,
}

impl Dataclass {
    pub fn new(class: GenericClass, options: DataclassOptions) -> Rc<Self> {
        Rc::new(Self {
            class,
            __init__: OnceCell::new(),
            options,
        })
    }

    pub fn class<'a>(&'a self, db: &'a Database) -> Class<'a> {
        self.class.class(db)
    }

    pub fn has_defined_generics(&self) -> bool {
        !matches!(self.class.generics, ClassGenerics::NotDefinedYet)
    }

    pub fn __init__<'a>(self_: &'a Rc<Self>, db: &Database) -> &'a CallableContent {
        if self_.__init__.get().is_none() {
            // Cannot use get_or_init, because this might cycle ones for some reasons (see for
            // example the test testDeferredDataclassInitSignatureSubclass)
            self_
                .__init__
                .set(calculate_init_of_dataclass(db, self_))
                .ok();
        }
        self_.__init__.get().unwrap()
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
            if param.name.as_ref().unwrap().as_str(db)
                == new_param.name.as_ref().unwrap().as_str(db)
            {
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
                        Type::Dataclass(dataclass.clone())
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
                    .into_owned();
                if let Type::Class(c) = &t {
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
            Type::Class(c) if c.link == db.python_state.dataclasses_kw_only_link() => {
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
                            name: Some(name.into()),
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
    CallableContent {
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
        result_type: Type::Any,
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
