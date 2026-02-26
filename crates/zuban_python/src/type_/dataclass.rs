use std::{
    hash::{Hash, Hasher},
    iter::repeat_with,
    sync::{Arc, OnceLock},
};

use parsa_python_cst::{
    ArgumentsDetails, AssignmentContent, AssignmentRightSide, ExpressionContent, ExpressionPart,
    NodeIndex, ParamKind, Primary, PrimaryContent, StarExpressionContent,
};
use utils::FastHashMap;

use super::{
    AnyCause, CallableContent, CallableParam, CallableParams, ClassGenerics, DbString,
    GenericClass, Literal, LiteralKind, LookupResult, NeverCause, ParamType, StringSlice, Tuple,
    Type, TypeVar, TypeVarKind, TypeVarKindInfos, TypeVarLike, TypeVarLikes, TypeVarUsage,
};
use crate::{
    arguments::{ArgKind, Args, CombinedArgs, KnownArgsWithCustomAddIssue, SimpleArgs},
    database::{Database, Locality, Point, PointLink, Specific},
    debug,
    diagnostics::{Issue, IssueKind},
    file::{ClassNodeRef, PythonFile},
    inference_state::InferenceState,
    inferred::{AttributeKind, Inferred},
    matching::{
        Generics, LookupKind, OnTypeError, calc_callable_type_vars, maybe_class_usage,
        replace_class_type_vars,
    },
    new_class,
    node_ref::NodeRef,
    python_state::NAME_TO_FUNCTION_DIFF,
    recoverable_error,
    result_context::ResultContext,
    type_::{CallableLike, ReplaceTypeVarLikes, callable::add_any_params_to_params},
    type_helpers::{
        Callable, Class, ClassLookupOptions, InstanceLookupOptions, LookupDetails, OverloadResult,
        OverloadedFunction, TypeOrClass,
    },
    utils::debug_indent,
};

type FieldSpecifiers = Arc<[PointLink]>;
type ConverterFields = FastHashMap<String, DataclassTransformConversion>;

const ORDER_METHOD_NAMES: [&str; 4] = ["__lt__", "__gt__", "__le__", "__ge__"];

#[derive(Clone, Eq)]
pub(crate) struct Dataclass {
    pub class: GenericClass,
    inits: OnceLock<Inits>,
    pub options: DataclassOptions,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DataclassOptions {
    pub init: bool,
    pub eq: bool,
    pub order: bool,
    // dataclass_transform can cause states that are undefined, see
    // testDataclassTransformDirectMetaclassNeitherFrozenNorNotFrozen
    pub frozen: Option<bool>,
    pub match_args: bool,
    pub kw_only: bool,
    pub slots: bool,
    pub unsafe_hash: bool,
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
            unsafe_hash: false,
            transform_field_specifiers: None,
        }
    }
}

impl std::fmt::Debug for Dataclass {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        // We don't want to display inits, since it can contain an Arc of the dataclass.
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
    pub fn new(class: GenericClass, options: DataclassOptions) -> Arc<Self> {
        Arc::new(Self {
            class,
            inits: OnceLock::new(),
            options,
        })
    }

    pub fn new_uninitialized(
        link: PointLink,
        type_vars: &TypeVarLikes,
        options: DataclassOptions,
    ) -> Arc<Self> {
        Self::new(
            GenericClass {
                link,
                generics: if type_vars.is_empty() {
                    ClassGenerics::new_none()
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
            ClassGenerics::None { .. } => None,
            _ => unreachable!(),
        };
        Class::from_position(
            ClassNodeRef::from_link(db, self.class.link),
            generics,
            remap,
        )
    }

    pub fn has_defined_generics(&self) -> bool {
        !matches!(self.class.generics, ClassGenerics::NotDefinedYet)
    }

    pub fn expect_calculated_post_init(&self) -> &CallableContent {
        &self.inits.get().unwrap().__post_init__
    }

    pub fn is_dataclass_transform(&self) -> bool {
        self.options.transform_field_specifiers.is_some()
    }

    pub fn lookup<'dataclass>(
        db: &Database,
        dataclass: &'dataclass Arc<Dataclass>,
        name: &str,
    ) -> Option<&'dataclass CallableParam> {
        dataclass_init_func(dataclass, db)
            .expect_simple_params()
            .iter()
            .find(|p| p.name.as_ref().is_some_and(|n| n.as_str(db) == name))
    }

    pub fn has_slot<'dataclass>(
        db: &Database,
        dataclass: &'dataclass Arc<Dataclass>,
        name: &str,
    ) -> bool {
        Self::lookup(db, dataclass, name).is_some()
            || dataclass_inits(dataclass, db)
                .non_init_fields
                .iter()
                .any(|f| f.as_str(db) == name)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Inits {
    __init__: CallableContent,
    __post_init__: CallableContent,
    converter_fields: ConverterFields,
    non_init_fields: Box<[DbString]>,
}

fn calculate_init_of_dataclass(db: &Database, dataclass: &Arc<Dataclass>) -> Inits {
    let cls = dataclass.class(db);
    let mut with_indexes = vec![];
    let file = cls.node_ref.file;
    let i_s = &InferenceState::new(db, file);
    let cls_i_s = &i_s.with_class_context(&cls);
    let inference = file.inference(cls_i_s);

    let mut params: Vec<CallableParam> = vec![];
    let mut post_init_params: Vec<CallableParam> = vec![];
    let mut converter_fields = ConverterFields::default();

    let mut add_param = |mut new_param: CallableParam| {
        let mut first_kwarg = None;
        if !matches!(
            dataclass.class.generics,
            ClassGenerics::None { .. } | ClassGenerics::NotDefinedYet
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
        if let TypeOrClass::Type(t) = c
            && let Type::Dataclass(super_dataclass) = t.as_ref()
        {
            if let Some((frozen1, frozen2)) =
                dataclass.options.frozen.zip(super_dataclass.options.frozen)
                && frozen1 != frozen2
            {
                let arguments = cls.node().arguments().unwrap();
                NodeRef::new(file, arguments.index()).add_issue(
                    i_s,
                    match frozen1 {
                        false => IssueKind::DataclassCannotInheritNonFrozenFromFrozen,
                        true => IssueKind::DataclassCannotInheritFrozenFromNonFrozen,
                    },
                );
            }
            let cls = super_dataclass.class(db);
            let init = dataclass_init_func(super_dataclass, db);
            let post_init = &super_dataclass.expect_calculated_post_init();
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
                    if n.expect_name()
                        .name_def()
                        .unwrap()
                        .maybe_assignment_definition()
                        .is_none()
                    {
                        if let Some(funcdef) =
                            NodeRef::new(file, in_current_class - NAME_TO_FUNCTION_DIFF)
                                .maybe_function()
                            && let Some(decorated) = funcdef.maybe_decorated()
                        {
                            n = NodeRef::new(file, decorated.index());
                        }
                        n.add_issue(
                            i_s,
                            IssueKind::DataclassAttributeMayOnlyBeOverriddenByAnotherAttribute,
                        );
                    }
                }
                if add_param(new_param) {
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

    struct Annotated {
        name_index: NodeIndex,
        t: Type,
        name: DbString,
        field_options: FieldOptions,
        is_init_var: bool, // e.g. InitVar[int]
    }

    for (_, name_index) in class_symbol_table.iter() {
        let name = NodeRef::new(file, *name_index).expect_name();
        if let Some(assignment) = name.maybe_assignment_definition_name()
            && let AssignmentContent::WithAnnotation(target, annotation, right_side) =
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
            if let Type::Class(c) = &t
                && c.class(i_s.db).node_ref.is_name_defined_in_module(
                    i_s.db,
                    "dataclasses",
                    "InitVar",
                )
            {
                t = c.class(db).nth_type_argument(db, 0);
                is_init_var = true;
            }
            /*
            TODO?
            if !matches!(dataclass.class.generics, ClassGenerics::NotDefinedYet | ClassGenerics::None) {
                t = replace_class_type_vars(db, &t, &cls, &|| );
            }
            */
            if is_init_var && let Some(right_side) = right_side {
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

    // The name indexes are not guarantueed to be sorted by its order in the tree. We however
    // want the original order in an enum.
    with_indexes.sort_by_key(|w| w.name_index);

    let mut non_init_fields = vec![];
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
                let mut t = infos.t;
                if let Some(conv) = infos.field_options.converter {
                    converter_fields.insert(
                        infos.name.as_str(i_s.db).into(),
                        DataclassTransformConversion { from: conv.clone() },
                    );
                    t = conv;
                }
                if infos.is_init_var {
                    post_init_params.push(CallableParam::new(
                        // This is what Mypy uses, apparently for practical reasons.
                        infos.name.clone(),
                        ParamType::PositionalOrKeyword(t.clone()),
                    ))
                }
                if infos.field_options.init {
                    let has_default = infos.field_options.has_default;
                    // Descriptors are assigned to in __init__, see
                    // https://github.com/microsoft/pyright/issues/3245
                    // Both Mypy and Pyright handle dataclass_transform always, which is
                    // questionable, since it doesn't appear in the PEP, but we just imitate that.
                    if has_default || dataclass.is_dataclass_transform() {
                        set_descriptor_update_for_init(i_s, &mut t)
                    }
                    add_param(CallableParam {
                        type_: match kw_only {
                            false => ParamType::PositionalOrKeyword(t),
                            true => ParamType::KeywordOnly(t),
                        },
                        name: Some(infos.name),
                        has_default,
                        might_have_type_vars: true,
                    });
                } else {
                    non_init_fields.push(infos.name)
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
                    file.maybe_add_issue(
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
        add_any_params_to_params(&mut params);
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
        converter_fields,
        non_init_fields: non_init_fields.into_boxed_slice(),
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
    if let Some(CallableLike::Callable(c)) = inf.as_cow_type(i_s).maybe_callable(i_s)
        && let CallableParams::Simple(s) = &c.params
        && let Some(third_param) = s.get(2)
        && let ParamType::PositionalOnly(new) | ParamType::PositionalOrKeyword(new) =
            &third_param.type_
    {
        *t = new.clone();
        return;
    }
    *t = Type::Any(AnyCause::Internal);
}

struct FieldOptions {
    has_default: bool,
    kw_only: Option<bool>,
    init: bool,
    // These are only used within dataclass_transform
    alias_name: Option<DbString>,
    converter: Option<Type>,
}

impl Default for FieldOptions {
    fn default() -> Self {
        Self {
            has_default: false,
            kw_only: None,
            init: true,
            alias_name: None,
            converter: None,
        }
    }
}

fn calculate_field_arg(
    i_s: &InferenceState,
    file: &PythonFile,
    right_side: Option<AssignmentRightSide>,
    options: &DataclassOptions,
) -> FieldOptions {
    if let Some(AssignmentRightSide::StarExpressions(star_exprs)) = right_side
        && let StarExpressionContent::Expression(expr) = star_exprs.unpack()
        && let ExpressionContent::ExpressionPart(ExpressionPart::Primary(primary)) = expr.unpack()
    {
        let node_ref = NodeRef::new(file, primary.index());
        debug_assert!(!node_ref.point().calculated());
        if node_ref.point().calculating() {
            // TODO what should we do here in this recursion?
            return Default::default();
        }
        node_ref.set_point(Point::new_calculating());
        let result = calculate_field_arg_inner(i_s, file, primary, options);
        debug_assert!(node_ref.point().calculating());
        node_ref.set_point(Point::new_uncalculated());
        if let Some(result) = result {
            return result;
        }
    }
    FieldOptions {
        has_default: right_side.is_some(),
        ..Default::default()
    }
}

fn calculate_field_arg_inner(
    i_s: &InferenceState,
    file: &PythonFile,
    primary: Primary,
    options: &DataclassOptions,
) -> Option<FieldOptions> {
    let PrimaryContent::Execution(details) = primary.second() else {
        return None;
    };
    let left = file.inference(i_s).infer_primary_or_atom(primary.first());
    if let Some(specifiers) = &options.transform_field_specifiers {
        for specifier in specifiers.iter() {
            if left.maybe_saved_link() == Some(*specifier) {
                let mut options = FieldOptions::default();
                apply_default_options_from_dataclass_transform_field(
                    i_s,
                    left,
                    &mut options,
                    &SimpleArgs::from_primary(*i_s, file, primary),
                );
                return Some(field_options_from_args(
                    i_s,
                    file,
                    primary.index(),
                    details,
                    true,
                    options,
                ));
            }
        }
    } else if left.is_name_defined_in_module(i_s.db, "dataclasses", "field") {
        return Some(field_options_from_args(
            i_s,
            file,
            primary.index(),
            details,
            false,
            FieldOptions::default(),
        ));
    }
    None
}

fn field_options_from_args(
    i_s: &InferenceState,
    file: &PythonFile,
    primary_index: NodeIndex,
    details: ArgumentsDetails,
    in_dataclass_transform: bool,
    mut options: FieldOptions,
) -> FieldOptions {
    let args = SimpleArgs::new(*i_s, file, primary_index, details);
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
                "converter" => {
                    let result = arg.infer_inferrable(i_s, &mut ResultContext::Unknown);
                    let mut converter = match result.as_cow_type(i_s).maybe_callable(i_s) {
                        Some(CallableLike::Callable(c)) => c.first_positional_type(),
                        Some(CallableLike::Overload(overload)) => {
                            Some(Type::simplified_union_from_iterators(
                                i_s,
                                overload.iter_functions().map(|func| {
                                    func.first_positional_type().unwrap_or(Type::ERROR)
                                }),
                            ))
                        }
                        None => None, // TODO
                    };
                    if let Some(c) = converter.as_ref() {
                        // TODO We avoid generics here, is this correct? It feels like we should
                        // type check them, but that gets extremely complicated quickly.
                        if let new @ Some(_) = c.replace_type_var_likes(i_s.db, &mut |usage| {
                            Some(usage.as_any_generic_item())
                        }) {
                            converter = new;
                        }
                    }
                    options.converter = converter;
                }
                _ => (), // Type checking is done in a separate place.
            }
        }
    }
    options
}

fn apply_default_options_from_dataclass_transform_field<'db>(
    i_s: &InferenceState<'db, '_>,
    inferred_field: Inferred,
    options: &mut FieldOptions,
    args: &dyn Args<'db>,
) {
    let mut apply_from_callable = |c: &CallableContent| {
        if let Some(func) = NodeRef::from_link(i_s.db, c.defined_at).maybe_function() {
            for p in func.params().iter() {
                // Currently this is only applied for init in Mypy.
                if p.name_def().as_code() == "init"
                    && let Some(default) = p.default()
                    && let Some(b) = default.maybe_simple_bool()
                {
                    options.init = b;
                }
            }
        }
    };
    match inferred_field.as_cow_type(i_s).maybe_callable(i_s) {
        Some(CallableLike::Callable(c)) => apply_from_callable(&c),
        Some(CallableLike::Overload(o)) => {
            if let OverloadResult::Single(c) = OverloadedFunction::new(&o, None)
                .find_matching_function(
                    i_s,
                    args,
                    false,
                    None,
                    false,
                    &mut ResultContext::Unknown,
                    None,
                    OnTypeError::new(&|_, _, _, _| ()),
                    &|_, _| Type::Never(NeverCause::Other),
                )
            {
                apply_from_callable(c.content)
            }
        }
        None => (),
    }
}

pub(crate) fn dataclasses_replace<'db>(
    i_s: &InferenceState<'db, '_>,
    args: &dyn Args<'db>,
    result_context: &mut ResultContext,
    on_type_error: OnTypeError,
    bound: Option<&Type>,
) -> Inferred {
    let mut arg_iterator = args.iter(i_s.mode);

    let inf = bound.map(|t| Inferred::from_type(t.clone())).or_else(|| {
        let first = arg_iterator.next()?;
        if let ArgKind::Positional(positional) = &first.kind {
            Some(positional.infer(&mut ResultContext::Unknown))
        } else {
            None
        }
    });
    let Some(inf) = inf else {
        // Execute the original function (in typeshed).
        // These cases are checked by the type checker that use the typeshed stubs.
        return i_s.db.python_state.dataclasses_replace().execute(
            i_s,
            args,
            result_context,
            on_type_error,
        );
    };
    let successful = run_on_dataclass_for_replace(
        i_s,
        Some(&|issue| args.add_issue(i_s, issue)),
        &inf.as_cow_type(i_s),
        &mut |dataclass| {
            let mut replace_func = dataclass_init_func(dataclass, i_s.db).clone();
            let mut params: Vec<_> = replace_func.expect_simple_params().into();
            for param in params.iter_mut() {
                // All normal dataclass arguments are optional, because they can be
                // overridden or just be left in place. However this is different for
                // InitVars, which always need to be there. To check if something is an
                // InitVar, we use this hack and check if the attribute exists on the
                // dataclass. If not, it's an InitVar.
                if let Some(name) = param.name.as_ref() {
                    // All params that have no name should be *args, **kwargs in case of an
                    // incomplete MRO.

                    let t = param.type_.maybe_type().unwrap();
                    param.type_ = ParamType::KeywordOnly(t.clone());
                    if lookup_on_dataclass(
                        dataclass,
                        i_s,
                        |issue| args.add_issue(i_s, issue),
                        name.as_str(i_s.db),
                    )
                    .lookup
                    .is_some()
                    {
                        param.has_default = true;
                    }
                }
            }
            params.insert(
                0,
                CallableParam::new_anonymous(ParamType::PositionalOnly(Type::Any(AnyCause::Todo))),
            );
            replace_func.params = CallableParams::new_simple(params.into());
            let arg;
            let known;
            let add_issue = &|issue| args.add_issue(i_s, issue);
            Callable::new(&replace_func, Some(dataclass.class(i_s.db))).execute_internal(
                i_s,
                if bound.is_some() {
                    known = KnownArgsWithCustomAddIssue::new(&inf, add_issue);
                    arg = CombinedArgs::new(&known, args);
                    &arg
                } else {
                    args
                },
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
        inf
    } else {
        // Error is raised by the type checker
        Inferred::new_any_from_error()
    }
}

fn run_on_dataclass_for_replace(
    i_s: &InferenceState,
    add_issue: Option<&dyn Fn(IssueKind)>,
    t: &Type,
    callback: &mut impl FnMut(&Arc<Dataclass>),
) -> bool {
    // Result type signals if we were successful
    let type_var_error = |tv: &TypeVar| {
        if let Some(add_issue) = add_issue {
            add_issue(IssueKind::DataclassReplaceExpectedDataclassInTypeVarBound {
                got: tv.name(i_s.db).into(),
            });
        }
        false
    };
    match t {
        Type::Dataclass(d) => {
            callback(d);
            true
        }
        Type::Union(u) => u
            .iter()
            .all(|t| run_on_dataclass_for_replace(i_s, add_issue, t, callback)),
        Type::Any(_) => true,
        Type::TypeVar(tv) => match tv.type_var.kind(i_s.db) {
            TypeVarKind::Bound(bound) => {
                let result = run_on_dataclass_for_replace(i_s, None, bound, callback);
                if !result {
                    type_var_error(&tv.type_var);
                }
                result
            }
            TypeVarKind::Constraints(_) => unimplemented!(),
            TypeVarKind::Unrestricted => type_var_error(&tv.type_var),
        },
        Type::Self_ => {
            if let Some(t) = i_s.current_type() {
                run_on_dataclass_for_replace(i_s, add_issue, &t, callback)
            } else {
                recoverable_error!("Proper self type expected in dataclass replace");
                false
            }
        }
        _ => {
            if let Some(add_issue) = add_issue {
                add_issue(IssueKind::DataclassReplaceExpectedDataclass {
                    got: t.format_short(i_s.db),
                });
            }
            false
        }
    }
}

pub(crate) fn dataclass_initialize<'db>(
    dataclass: &Arc<Dataclass>,
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
            calc_callable_type_vars(
                i_s,
                Callable::new(__init__, Some(class)),
                args.iter(i_s.mode),
                |issue| args.add_issue(i_s, issue),
                false,
                result_context,
                Some(&|| {
                    if matches!(dataclass.class.generics, ClassGenerics::NotDefinedYet) {
                        let type_vars = dataclass.class(i_s.db).use_cached_type_vars(i_s.db);
                        if !type_vars.is_empty() {
                            // Generics that are not defined yet generally resolve to Any, which is
                            // not what we want here. The Self that we want to receive here should
                            // have the exact same generics than this one.
                            let mut dc = dataclass.as_ref().clone();
                            dc.class.generics = ClassGenerics::List(
                                type_vars.as_self_generic_list(dataclass.class.link),
                            );

                            return Some(Type::Dataclass(Arc::new(dc)));
                        }
                    }
                    Some(Type::Dataclass(dataclass.clone()))
                }),
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

fn dataclass_inits<'a>(self_: &'a Arc<Dataclass>, db: &Database) -> &'a Inits {
    ensure_calculated_dataclass(self_, db);
    &self_.inits.get().unwrap()
}

pub fn dataclass_init_func<'a>(self_: &'a Arc<Dataclass>, db: &Database) -> &'a CallableContent {
    &dataclass_inits(self_, db).__init__
}

pub fn dataclass_converter_fields_lookup<'a>(
    self_: &'a Arc<Dataclass>,
    db: &Database,
    name: &str,
) -> Option<&'a DataclassTransformConversion> {
    ensure_calculated_dataclass(self_, db);
    self_.inits.get().unwrap().converter_fields.get(name)
}

pub fn ensure_calculated_dataclass(self_: &Arc<Dataclass>, db: &Database) {
    if self_.inits.get().is_none() {
        debug!("Calculate dataclass {}", self_.class(db).name());
        let indent = debug_indent();
        // Cannot use get_or_init, because this might recurse for some reasons (check for
        // example the test testDeferredDataclassInitSignatureSubclass)
        if self_
            .inits
            .set(calculate_init_of_dataclass(db, self_))
            .is_err()
        {
            recoverable_error!(
                "Looped dataclass initialization for {:?}",
                self_.class(db).name()
            );
        }
        drop(indent);
        debug!("Finished calculating dataclass {}", self_.class(db).name());
    }
}

pub fn dataclass_post_init_func<'a>(
    self_: &'a Arc<Dataclass>,
    db: &Database,
) -> &'a CallableContent {
    &dataclass_inits(self_, db).__post_init__
}

pub(crate) fn lookup_on_dataclass_type<'a>(
    in_type: &Arc<Type>,
    dataclass: &'a Arc<Dataclass>,
    i_s: &'a InferenceState,
    add_issue: impl Fn(IssueKind),
    name: &str,
    kind: LookupKind,
) -> LookupDetails<'a> {
    if name == "__dataclass_fields__" {
        let t = if dataclass.is_dataclass_transform() {
            // For dataclass_transform the values are always Any
            new_class!(
                i_s.db.python_state.dict_node_ref().as_link(),
                i_s.db.python_state.str_type(),
                Type::Any(AnyCause::Internal),
            )
        } else {
            i_s.db.python_state.dataclass_fields_type.clone()
        };
        LookupDetails::new(
            Type::Dataclass(dataclass.clone()),
            LookupResult::UnknownName(Inferred::from_type(t)),
            AttributeKind::Attribute,
        )
    } else if dataclass.options.order
        && ORDER_METHOD_NAMES.contains(&name)
        && kind == LookupKind::Normal
    {
        LookupDetails::new(
            Type::Dataclass(dataclass.clone()),
            type_order_func(dataclass.clone(), i_s),
            AttributeKind::Attribute,
        )
    } else if name == "__slots__" && dataclass.options.slots {
        LookupDetails::new(
            Type::Dataclass(dataclass.clone()),
            slots_as_lookup_result(dataclass, i_s.db),
            AttributeKind::Attribute,
        )
    } else if name == "__match_args__" && dataclass.options.match_args {
        let (lookup, attr_kind) = dunder_match_args_tuple(dataclass.clone(), i_s);
        LookupDetails::new(Type::Dataclass(dataclass.clone()), lookup, attr_kind)
    } else {
        dataclass.class(i_s.db).lookup(
            i_s,
            name,
            ClassLookupOptions::new(&add_issue)
                .with_kind(kind)
                .with_as_type_type(&|| Type::Type(in_type.clone())),
        )
    }
}

fn slots_as_lookup_result(self_: &Arc<Dataclass>, db: &Database) -> LookupResult {
    LookupResult::UnknownName(Inferred::from_type(Type::Tuple(Tuple::new_fixed_length(
        repeat_with(|| db.python_state.str_type())
            .take(dataclass_init_func(self_, db).expect_simple_params().len())
            .collect(),
    ))))
}

fn lookup_symbol_internal(
    self_: Arc<Dataclass>,
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
        return dunder_match_args_tuple(self_, i_s);
    }
    if self_.options.order && ORDER_METHOD_NAMES.contains(&name) {
        return (
            order_func(self_.clone(), i_s),
            AttributeKind::DefMethod { is_final: false },
        );
    }
    if self_.options.init && name == "__init__" {
        return (
            LookupResult::UnknownName(Inferred::from_type(Type::Callable(Arc::new(
                dataclass_init_func(&self_, i_s.db).clone(),
            )))),
            AttributeKind::DefMethod { is_final: false },
        );
    }
    if self_.options.slots && name == "__slots__" {
        return (
            slots_as_lookup_result(&self_, i_s.db),
            AttributeKind::Attribute,
        );
    }
    (LookupResult::None, AttributeKind::Attribute)
}

fn dunder_match_args_tuple(
    self_: Arc<Dataclass>,
    i_s: &InferenceState<'_, '_>,
) -> (LookupResult, AttributeKind) {
    let __init__ = dataclass_init_func(&self_, i_s.db);
    let tup = Tuple::new_fixed_length(
        __init__
            .expect_simple_params()
            .iter()
            .take_while(|p| p.type_.maybe_positional_type().is_some())
            .map(|p| Type::Literal(Literal::new(LiteralKind::String(p.name.clone().unwrap()))))
            .collect(),
    );
    (
        LookupResult::UnknownName(Inferred::from_type(Type::Tuple(tup))),
        AttributeKind::DefMethod { is_final: false },
    )
}

pub fn lookup_dataclass_symbol<'db: 'a, 'a>(
    self_: &'a Arc<Dataclass>,
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
    self_: &'a Arc<Dataclass>,
    i_s: &'a InferenceState,
    add_issue: impl Fn(IssueKind),
    name: &str,
) -> LookupDetails<'a> {
    if self_.options.frozen == Some(true)
        && let Some(param) = Dataclass::lookup(i_s.db, self_, name)
    {
        return LookupDetails::new(
            Type::Dataclass(self_.clone()),
            LookupResult::UnknownName(Inferred::from_type(
                param.type_.maybe_type().unwrap().clone(),
            )),
            AttributeKind::Property {
                setter_type: None,
                is_final: false,
                is_abstract: true,
            },
        );
    }
    let (result, attr_kind) = lookup_symbol_internal(self_.clone(), i_s, name);
    let class = self_.class(i_s.db);
    if result.is_some() && !class.lookup_symbol(i_s, name).is_some() {
        return LookupDetails::new(Type::Dataclass(self_.clone()), result, attr_kind);
    }
    let mut lookup_options = InstanceLookupOptions::new(&add_issue);
    if name == "__hash__" && !self_.options.unsafe_hash && !self_.options.frozen.unwrap_or_default()
    {
        lookup_options = lookup_options.without_object();
    }
    let mut lookup_details = class.instance().lookup(
        i_s,
        name,
        lookup_options.with_as_self_instance(&|| Type::Dataclass(self_.clone())),
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

fn order_func(self_: Arc<Dataclass>, i_s: &InferenceState) -> LookupResult {
    LookupResult::UnknownName(Inferred::from_type(Type::Callable(Arc::new(
        CallableContent::new_simple(
            None,
            None,
            self_.class.link,
            i_s.db.python_state.empty_type_var_likes.clone(),
            CallableParams::new_simple(Arc::new([CallableParam::new_anonymous(
                ParamType::PositionalOnly(Type::Dataclass(self_)),
            )])),
            i_s.db.python_state.bool_type(),
        ),
    ))))
}

fn type_order_func(self_: Arc<Dataclass>, i_s: &InferenceState) -> LookupResult {
    let type_var = Arc::new(TypeVar::new_self(TypeVarKindInfos::Unrestricted));
    let tv_usage = TypeVarUsage::new(type_var.clone(), self_.class.link, 0.into());
    LookupResult::UnknownName(Inferred::from_type(Type::Callable(Arc::new(
        CallableContent::new_simple(
            None,
            None,
            self_.class.link,
            TypeVarLikes::new(Arc::new([TypeVarLike::TypeVar(type_var)])),
            CallableParams::new_simple(Arc::new([
                CallableParam::new(
                    DbString::Static("self"),
                    ParamType::PositionalOnly(Type::TypeVar(tv_usage.clone())),
                ),
                CallableParam::new(
                    DbString::Static("other"),
                    ParamType::PositionalOnly(Type::TypeVar(tv_usage)),
                ),
            ])),
            i_s.db.python_state.bool_type(),
        ),
    ))))
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct DataclassTransformObj {
    pub eq_default: bool,
    pub order_default: bool,
    pub kw_only_default: bool,
    pub frozen_default: bool,
    pub field_specifiers: FieldSpecifiers,
}

impl Default for DataclassTransformObj {
    fn default() -> Self {
        Self {
            eq_default: true,
            order_default: false,
            kw_only_default: false,
            frozen_default: false,
            field_specifiers: Arc::default(),
        }
    }
}

impl DataclassTransformObj {
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DataclassTransformConversion {
    pub from: Type,
}
