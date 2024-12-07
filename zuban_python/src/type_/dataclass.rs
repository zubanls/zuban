use std::{
    cell::OnceCell,
    hash::{Hash, Hasher},
    iter::repeat_with,
    rc::Rc,
};

use parsa_python_cst::{
    ArgumentsDetails, AssignmentContent, AssignmentRightSide, ExpressionContent, ExpressionPart,
    NodeIndex, ParamKind, PrimaryContent, StarExpressionContent, StarLikeExpression,
};

use super::{
    AnyCause, CallableContent, CallableParam, CallableParams, ClassGenerics, DbString,
    GenericClass, Literal, LiteralKind, LookupResult, ParamType, StarParamType, StarStarParamType,
    StringSlice, Tuple, Type, TypeVar, TypeVarKind, TypeVarLike, TypeVarLikes, TypeVarName,
    TypeVarUsage, Variance,
};
use crate::{
    arguments::{Arg, ArgKind, Args, SimpleArgs},
    database::{Database, Locality, Point, PointLink, Specific},
    diagnostics::{Issue, IssueKind},
    file::PythonFile,
    inference_state::InferenceState,
    inferred::{AttributeKind, Inferred},
    matching::{
        calculate_callable_type_vars_and_return, maybe_class_usage, replace_class_type_vars,
        Generics, LookupKind, OnTypeError, ResultContext,
    },
    new_class,
    node_ref::NodeRef,
    python_state::NAME_TO_FUNCTION_DIFF,
    type_::CallableLike,
    type_helpers::{
        Callable, Class, ClassLookupOptions, Instance, InstanceLookupOptions, LookupDetails,
        TypeOrClass,
    },
};

type FieldSpecifiers = Rc<[PointLink]>;

const ORDER_METHOD_NAMES: [&str; 4] = ["__lt__", "__gt__", "__le__", "__ge__"];

#[derive(Clone, Eq)]
pub struct Dataclass {
    pub class: GenericClass,
    inits: OnceCell<Inits>,
    pub options: DataclassOptions,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DataclassOptions {
    pub init: bool,
    pub eq: bool,
    pub order: bool,
    // dataclass_transform can cause states that are undefined, see
    // testDataclassTransformDirectMetaclassNeitherFrozenNorNotFrozen
    pub frozen: Option<bool>,
    pub match_args: bool,
    pub kw_only: bool,
    pub slots: bool,
    pub transform_field_specifiers: Option<FieldSpecifiers>,
    // the keyword arguments `weakref_slot = false` and `repr = true` are ignored here, because
    // they are not relevant for us as a typechecker.
}

impl Default for DataclassOptions {
    fn default() -> Self {
        Self {
            init: true,
            eq: true,
            order: false,
            frozen: Some(false),
            match_args: true,
            kw_only: false,
            slots: false,
            transform_field_specifiers: None,
        }
    }
}

impl DataclassOptions {
    pub fn assign_keyword_arg_to_dataclass_options<'db>(
        &mut self,
        i_s: &InferenceState,
        key: &str,
        arg: &Arg<'db, '_>,
    ) {
        let assign_option = |target: &mut _, arg: &Arg<'db, '_>| {
            let result = arg.infer_inferrable(i_s, &mut ResultContext::Unknown);
            if let Some(bool_) = result.maybe_bool_literal(i_s) {
                *target = bool_;
            } else {
                let key = arg.keyword_name(i_s.db).unwrap().into();
                arg.add_issue(i_s, IssueKind::ArgumentMustBeTrueOrFalse { key })
            }
        };
        match key {
            "kw_only" => assign_option(&mut self.kw_only, arg),
            "frozen" => {
                let mut new_frozen = false;
                assign_option(&mut new_frozen, arg);
                self.frozen = Some(new_frozen);
            }
            "order" => assign_option(&mut self.order, arg),
            "eq" => assign_option(&mut self.eq, arg),
            "init" => assign_option(&mut self.init, arg),
            "match_args" => assign_option(&mut self.match_args, arg),
            "slots" => assign_option(&mut self.slots, arg),
            // The other names should not go through while type checking
            _ => (),
        }
    }
}

impl std::fmt::Debug for Dataclass {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        // We don't want to display inits, since it can contain an Rc of the dataclass.
        f.debug_struct("Dataclass")
            .field("class", &self.class)
            .field("options", &self.options)
            .finish()
    }
}

impl PartialEq for Dataclass {
    fn eq(&self, other: &Self) -> bool {
        // This should not compare inits, because it might recurse
        self.class == other.class && self.options == other.options
    }
}

impl Hash for Dataclass {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.class.hash(state);
    }
}

impl Dataclass {
    pub fn new(class: GenericClass, options: DataclassOptions) -> Rc<Self> {
        Rc::new(Self {
            class,
            inits: OnceCell::new(),
            options,
        })
    }

    pub fn new_uninitialized(
        link: PointLink,
        type_vars: &TypeVarLikes,
        options: DataclassOptions,
    ) -> Rc<Self> {
        Self::new(
            GenericClass {
                link,
                generics: if type_vars.is_empty() {
                    ClassGenerics::None
                } else {
                    ClassGenerics::NotDefinedYet
                },
            },
            options,
        )
    }

    pub fn class<'a>(&'a self, db: &'a Database) -> Class<'a> {
        self.class.class(db)
    }

    pub fn as_base_class<'a>(&'a self, db: &'a Database, generics: Generics<'a>) -> Class<'a> {
        let remap = match &self.class.generics {
            ClassGenerics::List(list) => Some(list),
            ClassGenerics::None => None,
            _ => unreachable!(),
        };
        Class::from_position(NodeRef::from_link(db, self.class.link), generics, remap)
    }

    pub fn has_defined_generics(&self) -> bool {
        !matches!(self.class.generics, ClassGenerics::NotDefinedYet)
    }

    pub fn expect_calculated_post_init(&self) -> &CallableContent {
        &self.inits.get().unwrap().__post_init__
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Inits {
    __init__: CallableContent,
    __post_init__: CallableContent,
}

fn calculate_init_of_dataclass(db: &Database, dataclass: &Rc<Dataclass>) -> Inits {
    let cls = dataclass.class(db);
    let mut with_indexes = vec![];
    let i_s = &InferenceState::new(db);
    let cls_i_s = &i_s.with_class_context(&cls);
    let file = cls.node_ref.file;
    let inference = file.inference(cls_i_s);

    let mut params: Vec<CallableParam> = vec![];
    let mut post_init_params: Vec<CallableParam> = vec![];

    let add_param = |params: &mut Vec<CallableParam>, mut new_param: CallableParam| {
        let mut first_kwarg = None;
        if !matches!(
            dataclass.class.generics,
            ClassGenerics::None | ClassGenerics::NotDefinedYet
        ) {
            // We need to remap generics in case of inheritance or more complex types.
            match &mut new_param.type_ {
                ParamType::PositionalOrKeyword(t) | ParamType::KeywordOnly(t) => {
                    if let Some(new_t) = t.replace_type_var_likes(i_s.db, &mut |usage| {
                        maybe_class_usage(db, &cls, &usage)
                    }) {
                        *t = new_t
                    }
                }
                _ => unreachable!(),
            }
        }
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
                if let Some((frozen1, frozen2)) =
                    dataclass.options.frozen.zip(super_dataclass.options.frozen)
                {
                    if frozen1 != frozen2 {
                        let arguments = cls.node().arguments().unwrap();
                        NodeRef::new(file, arguments.index()).add_issue(
                            i_s,
                            match frozen1 {
                                false => IssueKind::DataclassCannotInheritNonFrozenFromFrozen,
                                true => IssueKind::DataclassCannotInheritFrozenFromNonFrozen,
                            },
                        );
                    }
                }
                let cls = super_dataclass.class(db);
                let init = dataclass_init_func(super_dataclass, db);
                let post_init = &super_dataclass.inits.get().unwrap().__post_init__;
                for param in init.expect_simple_params().iter() {
                    let mut new_param = param.clone();
                    let t = match &mut new_param.type_ {
                        ParamType::PositionalOrKeyword(t) | ParamType::KeywordOnly(t) => t,
                        // Comes from an incomplete_mro
                        ParamType::Star(_) | ParamType::StarStar(_) => continue,
                        _ => unreachable!(),
                    };
                    *t = replace_class_type_vars(db, t, &cls, &|| {
                        Some(Type::Dataclass(dataclass.clone()))
                    })
                    .into_owned();
                    let cloned_name = new_param.name.clone().unwrap();
                    let param_name = cloned_name.as_str(db);
                    if let Some(in_current_class) = class_symbol_table.lookup_symbol(param_name) {
                        let mut n = NodeRef::new(file, in_current_class);
                        if n.as_name()
                            .name_def()
                            .unwrap()
                            .maybe_assignment_definition()
                            .is_none()
                        {
                            if let Some(funcdef) =
                                NodeRef::new(file, in_current_class - NAME_TO_FUNCTION_DIFF)
                                    .maybe_function()
                            {
                                if let Some(decorated) = funcdef.maybe_decorated() {
                                    n = NodeRef::new(file, decorated.index());
                                }
                            }
                            n.add_issue(
                                i_s,
                                IssueKind::DataclassAttributeMayOnlyBeOverriddenByAnotherAttribute,
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
        name: DbString,
        field_options: FieldOptions,
        is_init_var: bool, // e.g. InitVar[int]
    }

    for (_, name_index) in class_symbol_table.iter() {
        let name = NodeRef::new(file, *name_index).as_name();
        if let Some(assignment) = name.maybe_assignment_definition_name() {
            if let AssignmentContent::WithAnnotation(target, annotation, right_side) =
                assignment.unpack()
            {
                inference.ensure_cached_annotation(annotation, right_side.is_some());
                let field_options = calculate_field_arg(i_s, file, right_side, &dataclass.options);
                let point = file.points.get(annotation.index());
                match point.maybe_specific() {
                    Some(Specific::AnnotationOrTypeCommentClassVar) => {
                        // ClassVar[] are not part of the dataclass.
                        continue;
                    }
                    Some(Specific::AnnotationTypeAlias) => {
                        NodeRef::new(file, assignment.index())
                            .add_issue(i_s, IssueKind::DataclassContainsTypeAlias);
                        continue;
                    }
                    Some(Specific::AnnotationOrTypeCommentFinal) => {
                        if !file
                            .points
                            .get(annotation.expression().index())
                            .calculated()
                        {
                            let annotation_ref = NodeRef::new(file, annotation.index());
                            inference.fill_potentially_unfinished_final_or_class_var(
                                annotation_ref,
                                right_side,
                            );
                            if right_side.is_some_and(|right_side| !right_side.is_literal_value()) {
                                annotation_ref
                                    .add_issue(i_s, IssueKind::NeedTypeArgumentForFinalInDataclass)
                            }
                        }
                    }
                    _ => (),
                }
                let mut t = inference
                    .use_cached_annotation_type(annotation)
                    .into_owned();
                let mut is_init_var = false;
                if let Type::Class(c) = &t {
                    if c.class(i_s.db).node_ref.is_name_defined_in_module(
                        i_s.db,
                        "dataclasses",
                        "InitVar",
                    ) {
                        t = c.class(db).nth_type_argument(db, 0);
                        is_init_var = true;
                    }
                }
                /*
                TODO?
                if !matches!(dataclass.class.generics, ClassGenerics::NotDefinedYet | ClassGenerics::None) {
                    t = replace_class_type_vars(db, &t, &cls, &|| );
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
                    file.points.set(
                        assignment.index(),
                        Point::new_specific(Specific::Analyzed, Locality::Todo),
                    );
                }
                let name = field_options.alias_name.clone().unwrap_or_else(|| {
                    DbString::StringSlice(StringSlice::from_name(cls.node_ref.file_index(), name))
                });
                with_indexes.push(Annotated {
                    name_index: *name_index,
                    t,
                    name,
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
            Type::Class(c)
                if c.class(i_s.db).node_ref.is_name_defined_in_module(
                    i_s.db,
                    "dataclasses",
                    "KW_ONLY",
                ) =>
            {
                if had_kw_only_marker {
                    NodeRef::new(file, infos.name_index)
                        .add_issue(i_s, IssueKind::DataclassMultipleKwOnly);
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
                        name: Some(infos.name.clone()),
                        has_default: false,
                    })
                }
                if infos.field_options.init {
                    let mut t = infos.t;
                    let has_default = infos.field_options.has_default;
                    // Descriptors are assigned to in __init__, see
                    // https://github.com/microsoft/pyright/issues/3245
                    // Both Mypy and Pyright handle dataclass_transform always, which is
                    // questionable, since it doesn't appear in the PEP, but we just imitate that.
                    if has_default || dataclass.options.transform_field_specifiers.is_some() {
                        set_descriptor_update_for_init(i_s, &mut t)
                    }
                    add_param(
                        &mut params,
                        CallableParam {
                            type_: match kw_only {
                                false => ParamType::PositionalOrKeyword(t),
                                true => ParamType::KeywordOnly(t),
                            },
                            name: Some(infos.name),
                            has_default,
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
                let issue_type = IssueKind::DataclassNoDefaultAfterDefault;
                let DbString::StringSlice(name) = name else {
                    unreachable!();
                };
                if name.file_index == file.file_index {
                    file.add_issue(
                        i_s,
                        Issue::from_start_stop(name.start, name.end, issue_type),
                    );
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
                    IssueKind::DataclassCustomOrderMethodNotAllowed { method_name },
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
    Inits {
        __init__: CallableContent::new_simple(
            Some(DbString::StringSlice(cls.name_string_slice())),
            None,
            cls.node_ref.as_link(),
            match &dataclass.class.generics {
                ClassGenerics::NotDefinedYet => cls.use_cached_type_vars(db).clone(),
                _ => i_s.db.python_state.empty_type_var_likes.clone(),
            },
            CallableParams::new_simple(params.into()),
            Type::Any(AnyCause::Todo),
        ),
        __post_init__: CallableContent::new_simple(
            Some(DbString::Static("__post_init__")),
            None,
            cls.node_ref.as_link(),
            i_s.db.python_state.empty_type_var_likes.clone(),
            CallableParams::new_simple(post_init_params.into()),
            Type::None,
        ),
    }
}

fn set_descriptor_update_for_init(i_s: &InferenceState, t: &mut Type) {
    let Some(cls) = t.maybe_class(i_s.db) else {
        return;
    };
    let lookup = cls
        .lookup(i_s, "__set__", ClassLookupOptions::new(&|_| ()))
        .lookup;
    let Some(inf) = lookup.maybe_inferred() else {
        return;
    };
    // TODO Currently overloads arg ignored, but theoretically we should
    // support this as well.
    if let Some(CallableLike::Callable(c)) = inf.as_cow_type(i_s).maybe_callable(i_s) {
        if let CallableParams::Simple(s) = &c.params {
            if let Some(third_param) = s.get(2) {
                if let ParamType::PositionalOnly(new) | ParamType::PositionalOrKeyword(new) =
                    &third_param.type_
                {
                    *t = new.clone();
                    return;
                }
            }
        }
    }
    *t = Type::Any(AnyCause::Internal);
}

struct FieldOptions {
    has_default: bool,
    kw_only: Option<bool>,
    init: bool,
    // These are only used within dataclass_transform
    alias_name: Option<DbString>,
}

impl Default for FieldOptions {
    fn default() -> Self {
        Self {
            has_default: false,
            kw_only: None,
            init: true,
            alias_name: None,
        }
    }
}

fn calculate_field_arg(
    i_s: &InferenceState,
    file: &PythonFile,
    right_side: Option<AssignmentRightSide>,
    options: &DataclassOptions,
) -> FieldOptions {
    if let Some(AssignmentRightSide::StarExpressions(star_exprs)) = right_side {
        if let StarExpressionContent::Expression(expr) = star_exprs.unpack() {
            if let ExpressionContent::ExpressionPart(ExpressionPart::Primary(primary)) =
                expr.unpack()
            {
                if let PrimaryContent::Execution(details) = primary.second() {
                    let left = file.inference(i_s).infer_primary_or_atom(primary.first());
                    if let Some(specifiers) = &options.transform_field_specifiers {
                        for specifier in specifiers.iter() {
                            if left.maybe_saved_link() == Some(*specifier) {
                                return field_options_from_args(
                                    i_s,
                                    file,
                                    primary.index(),
                                    details,
                                    true,
                                );
                            }
                        }
                    } else if left.is_name_defined_in_module(i_s.db, "dataclasses", "field") {
                        return field_options_from_args(i_s, file, primary.index(), details, false);
                    }
                }
            }
        }
    }
    FieldOptions {
        has_default: right_side.is_some(),
        ..Default::default()
    }
}

fn field_options_from_args(
    i_s: &InferenceState,
    file: &PythonFile,
    primary_index: NodeIndex,
    details: ArgumentsDetails,
    in_dataclass_transform: bool,
) -> FieldOptions {
    let args = SimpleArgs::new(*i_s, file, primary_index, details);
    let mut options = FieldOptions::default();
    for arg in args.iter(i_s.mode) {
        if matches!(arg.kind, ArgKind::Inferred { .. }) {
            arg.add_issue(i_s, IssueKind::DataclassUnpackingKwargsInField);
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
                        arg.add_issue(
                            i_s,
                            IssueKind::ArgumentMustBeTrueOrFalse { key: key.into() },
                        )
                    }
                }
                "init" => {
                    let result = arg.infer_inferrable(i_s, &mut ResultContext::Unknown);
                    if let Some(bool_) = result.maybe_bool_literal(i_s) {
                        options.init = bool_
                    } else {
                        arg.add_issue(
                            i_s,
                            IssueKind::ArgumentMustBeTrueOrFalse { key: key.into() },
                        )
                    }
                }
                "alias" if in_dataclass_transform => {
                    let result = arg.infer_inferrable(i_s, &mut ResultContext::Unknown);
                    if let Some(alias) = result.maybe_string_literal(i_s) {
                        options.alias_name = Some(alias);
                    } else {
                        arg.add_issue(
                            i_s,
                            IssueKind::DataclassTransformFieldAliasParamMustBeString,
                        )
                    }
                }
                "factory" if in_dataclass_transform => options.has_default = true,
                _ => (), // Type checking is done in a separate place.
            }
        }
    }
    options
}

pub fn check_dataclass_options(
    i_s: &InferenceState,
    file: &PythonFile,
    primary_index: NodeIndex,
    details: ArgumentsDetails,
    default_options: DataclassOptions,
) -> DataclassOptions {
    let mut options = default_options;
    let args = SimpleArgs::new(*i_s, file, primary_index, details);
    for arg in args.iter(i_s.mode) {
        if let Some(key) = arg.keyword_name(i_s.db) {
            options.assign_keyword_arg_to_dataclass_options(i_s, key, &arg);
        } else {
            arg.add_issue(i_s, IssueKind::UnexpectedArgumentTo { name: "dataclass" })
        }
    }
    if !options.eq && options.order {
        options.eq = true;
        args.add_issue(i_s, IssueKind::DataclassOrderEnabledButNotEq);
    }
    options
}

pub(crate) fn dataclasses_replace<'db>(
    i_s: &InferenceState<'db, '_>,
    args: &dyn Args<'db>,
    result_context: &mut ResultContext,
    on_type_error: OnTypeError,
    bound: Option<&Type>,
) -> Inferred {
    debug_assert!(bound.is_none());

    let mut arg_iterator = args.iter(i_s.mode);
    if let Some(first) = arg_iterator.next() {
        if let ArgKind::Positional(positional) = &first.kind {
            let inferred = positional.infer(&mut ResultContext::Unknown);
            let successful = run_on_dataclass(
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
                    replace_func.params = CallableParams::new_simple(params.into());
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
                        None,
                    );
                },
            );
            if successful {
                return inferred;
            } else {
                // Error is raised by the type checker
                return Inferred::new_any_from_error();
            }
            // All other cases are checked by the type checker that uses the typeshed stubs.
        }
    }
    // Execute the original function (in typeshed).
    return i_s.db.python_state.dataclasses_replace(i_s).execute(
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
                IssueKind::DataclassReplaceExpectedDataclassInTypeVarBound {
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
            TypeVarKind::Constraints(_) => unimplemented!(),
            TypeVarKind::Unrestricted => type_var_error(&tv.type_var),
        },
        _ => {
            if let Some(from) = from {
                from.add_issue(
                    i_s,
                    IssueKind::DataclassReplaceExpectedDataclass {
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
    on_type_error: OnTypeError,
) -> Inferred {
    let class = dataclass.class(i_s.db);
    let __init__ = dataclass_init_func(dataclass, i_s.db);
    let class_generics =
        if !dataclass.options.init || class.lookup_symbol(i_s, "__init__").is_some() {
            // If the class has an __init__ method defined, the class itself wins.
            let result = class.execute(i_s, args, result_context, on_type_error, true);
            return Inferred::from_type(
                result
                    .as_cow_type(i_s)
                    .iter_with_unpacked_unions(i_s.db)
                    .map(|t| {
                        // Since we use the dataclass's class, we need to remap if that is the type
                        // that is returned.
                        match t {
                            Type::Class(c) if c.link == dataclass.class.link => Type::Dataclass(
                                Dataclass::new(c.clone(), dataclass.options.clone()),
                            ),
                            _ => t.clone(),
                        }
                    })
                    .collect(),
            );
        } else {
            calculate_callable_type_vars_and_return(
                i_s,
                Callable::new(__init__, Some(class)),
                args.iter(i_s.mode),
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
                generics: class_generics.type_arguments_into_class_generics(i_s.db),
            },
            dataclass.options.clone(),
        )
    }))
}

pub fn dataclass_init_func<'a>(self_: &'a Rc<Dataclass>, db: &Database) -> &'a CallableContent {
    if self_.inits.get().is_none() {
        // Cannot use get_or_init, because this might recurse for some reasons (check for
        // example the test testDeferredDataclassInitSignatureSubclass)
        self_.inits.set(calculate_init_of_dataclass(db, self_)).ok();
    }
    &self_.inits.get().unwrap().__init__
}

pub(crate) fn lookup_on_dataclass_type<'a>(
    in_type: &Rc<Type>,
    dataclass: &'a Rc<Dataclass>,
    i_s: &'a InferenceState,
    add_issue: impl Fn(IssueKind),
    name: &str,
    kind: LookupKind,
) -> LookupDetails<'a> {
    if name == "__dataclass_fields__" && kind == LookupKind::Normal {
        let t = if dataclass.options.transform_field_specifiers.is_some() {
            // For dataclass_transform the values are always Any
            new_class!(
                i_s.db.python_state.dict_node_ref().as_link(),
                i_s.db.python_state.str_type(),
                Type::Any(AnyCause::Internal),
            )
        } else {
            i_s.db.python_state.dataclass_fields_type.clone()
        };
        return LookupDetails::new(
            Type::Dataclass(dataclass.clone()),
            LookupResult::UnknownName(Inferred::from_type(t)),
            AttributeKind::Attribute,
        );
    }
    if dataclass.options.order && ORDER_METHOD_NAMES.contains(&name) && kind == LookupKind::Normal {
        return LookupDetails::new(
            Type::Dataclass(dataclass.clone()),
            type_order_func(dataclass.clone(), i_s),
            AttributeKind::Attribute,
        );
    }
    if name == "__slots__" && dataclass.options.slots {
        return LookupDetails::new(
            Type::Dataclass(dataclass.clone()),
            LookupResult::UnknownName(Inferred::from_type(Type::Tuple(Tuple::new_fixed_length(
                repeat_with(|| i_s.db.python_state.str_type())
                    .take(
                        dataclass_init_func(dataclass, i_s.db)
                            .expect_simple_params()
                            .len(),
                    )
                    .collect(),
            )))),
            AttributeKind::Attribute,
        );
    }
    dataclass.class(i_s.db).lookup(
        i_s,
        name,
        ClassLookupOptions::new(&add_issue)
            .with_kind(kind)
            .with_as_type_type(&|| Type::Type(in_type.clone())),
    )
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
            AttributeKind::DefMethod { is_final: false },
        );
    }
    if self_.options.order && ORDER_METHOD_NAMES.contains(&name) {
        return (
            order_func(self_.clone(), i_s),
            AttributeKind::DefMethod { is_final: false },
        );
    }
    if self_.options.init && name == "__init__" {
        return (
            LookupResult::UnknownName(Inferred::from_type(Type::Callable(Rc::new(
                dataclass_init_func(&self_, i_s.db).clone(),
            )))),
            AttributeKind::DefMethod { is_final: false },
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
    add_issue: impl Fn(IssueKind),
    name: &str,
) -> LookupDetails<'a> {
    let (result, attr_kind) = lookup_symbol_internal(self_.clone(), i_s, name);
    if result.is_some() {
        return LookupDetails::new(Type::Dataclass(self_.clone()), result, attr_kind);
    }
    let mut lookup_details = Instance::new(self_.class(i_s.db), None).lookup(
        i_s,
        name,
        InstanceLookupOptions::new(&add_issue)
            .with_as_self_instance(&|| Type::Dataclass(self_.clone())),
    );
    lookup_details.lookup = lookup_details
        .lookup
        .and_then(|inf| match inf.as_cow_type(i_s).as_ref() {
            // Init vars are not actually available on the class. They are just passed to __init__
            // and are not class members.
            Type::Class(c)
                if c.class(i_s.db).node_ref.is_name_defined_in_module(
                    i_s.db,
                    "dataclasses",
                    "InitVar",
                ) =>
            {
                None
            }
            _ => Some(inf),
        })
        .unwrap_or(LookupResult::None);
    lookup_details
}

fn order_func(self_: Rc<Dataclass>, i_s: &InferenceState) -> LookupResult {
    LookupResult::UnknownName(Inferred::from_type(Type::Callable(Rc::new(
        CallableContent::new_simple(
            None,
            None,
            self_.class.link,
            i_s.db.python_state.empty_type_var_likes.clone(),
            CallableParams::new_simple(Rc::new([CallableParam {
                type_: ParamType::PositionalOnly(Type::Dataclass(self_)),
                name: None,
                has_default: false,
            }])),
            i_s.db.python_state.bool_type(),
        ),
    ))))
}

fn type_order_func(self_: Rc<Dataclass>, i_s: &InferenceState) -> LookupResult {
    let type_var = Rc::new(TypeVar {
        name_string: TypeVarName::Self_,
        kind: TypeVarKind::Unrestricted,
        default: None,
        variance: Variance::Invariant,
    });
    let tv_usage = TypeVarUsage::new(type_var.clone(), self_.class.link, 0.into());
    LookupResult::UnknownName(Inferred::from_type(Type::Callable(Rc::new(
        CallableContent::new_simple(
            None,
            None,
            self_.class.link,
            TypeVarLikes::new(Rc::new([TypeVarLike::TypeVar(type_var)])),
            CallableParams::new_simple(Rc::new([
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
            i_s.db.python_state.bool_type(),
        ),
    ))))
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DataclassTransformObj {
    pub eq_default: bool,
    pub order_default: bool,
    pub kw_only_default: bool,
    pub frozen_default: bool,
    pub field_specifiers: FieldSpecifiers,
    // Whether it was use before a def foo()
    pub executed_by_function: bool,
}

impl Default for DataclassTransformObj {
    fn default() -> Self {
        Self {
            eq_default: true,
            order_default: false,
            kw_only_default: false,
            frozen_default: false,
            field_specifiers: Rc::default(),
            executed_by_function: false,
        }
    }
}

impl DataclassTransformObj {
    pub(crate) fn from_args<'db>(i_s: &InferenceState<'db, '_>, args: &dyn Args<'db>) -> Self {
        // Checks dataclass_transform(...)
        let mut options = Self::default();
        let assign_option = |target: &mut _, arg: Arg<'db, '_>| {
            let result = arg.infer_inferrable(i_s, &mut ResultContext::Unknown);
            if let Some(bool_) = result.maybe_bool_literal(i_s) {
                *target = bool_;
            } else {
                let key = arg.keyword_name(i_s.db).unwrap().into();
                arg.add_issue(i_s, IssueKind::ArgumentMustBeTrueOrFalse { key });
            }
        };
        for arg in args.iter(i_s.mode) {
            if let Some(key) = arg.keyword_name(i_s.db) {
                match key {
                    "eq_default" => assign_option(&mut options.eq_default, arg),
                    "order_default" => assign_option(&mut options.order_default, arg),
                    "kw_only_default" => assign_option(&mut options.kw_only_default, arg),
                    "frozen_default" => assign_option(&mut options.frozen_default, arg),
                    "field_specifiers" => fill_dataclass_transform_field_specifiers(
                        i_s,
                        arg,
                        &mut options.field_specifiers,
                    ),
                    _ => arg.add_issue(
                        i_s,
                        IssueKind::DataclassTransformUnknownParam { name: key.into() },
                    ),
                }
            } else {
                todo!()
                //arg.add_issue(i_s, IssueKind::UnexpectedArgumentTo { name: "dataclass_transform" })
            }
        }
        options
    }

    pub(crate) fn as_dataclass_options(&self) -> DataclassOptions {
        DataclassOptions {
            eq: self.eq_default,
            order: self.order_default,
            kw_only: self.kw_only_default,
            frozen: Some(self.frozen_default),
            transform_field_specifiers: Some(self.field_specifiers.clone()),
            ..Default::default()
        }
    }
}

fn fill_dataclass_transform_field_specifiers(
    i_s: &InferenceState,
    arg: Arg,
    field_specifiers: &mut Rc<[PointLink]>,
) {
    let check =
        || -> Result<Rc<[_]>, IssueKind> {
            if let ArgKind::Keyword(kwarg) = &arg.kind {
                if let Some(tuple) = kwarg.expression.maybe_tuple() {
                    return tuple.iter().map(|s| {
                    if let StarLikeExpression::NamedExpression(ne) = s {
                        let inf = kwarg.node_ref.file.inference(i_s).infer_named_expression(ne);
                        if let Some(from) = inf.maybe_saved_node_ref(i_s.db) {
                            if from.maybe_function().is_some() {
                                return Ok(from.as_link())
                            }
                        }
                    }
                    Err(IssueKind::DataclassTransformFieldSpecifiersMustOnlyContainIdentifiers)
                }).collect();
                }
            }
            Err(IssueKind::DataclassTransformFieldSpecifiersMustBeTuple)
        };
    match check() {
        Ok(new_specifiers) => *field_specifiers = new_specifiers,
        Err(issue) => arg.add_issue(i_s, issue),
    }
}
