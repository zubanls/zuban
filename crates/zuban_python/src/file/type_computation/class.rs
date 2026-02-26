use std::{
    borrow::Cow,
    sync::{Arc, Mutex, OnceLock},
};

use parsa_python_cst::{
    ArgOrComprehension, Argument, ArgumentsDetails, Assignment, AssignmentContent,
    AsyncStmtContent, AtomContent, ClassDef, Decorated, Decoratee, Expression, ExpressionContent,
    ExpressionPart, Kwarg, Name, NodeIndex, Primary, PrimaryContent, StarLikeExpression,
    StmtLikeContent, StmtLikeIterator, Target, TrivialBodyState, TypeLike,
};
use utils::FastHashSet;

use crate::{
    database::{
        BaseClass, ClassInfos, ClassKind, ClassStorage, ComplexPoint, Database,
        DeferredTypedDictMembers, Locality, MetaclassState, ParentScope, Point, PointLink,
        ProtocolMember, Specific, TypedDictArgs, TypedDictDefinition,
    },
    debug,
    diagnostics::IssueKind,
    file::{
        OtherDefinitionIterator, PythonFile, TypeVarCallbackReturn, TypeVarFinder,
        name_resolution::{NameResolution, PointResolution},
        type_computation::{InvalidVariableType, TypeContent},
        use_cached_annotation_type,
        utils::should_add_deprecated,
    },
    inference_state::InferenceState,
    node_ref::NodeRef,
    python_state::{NAME_TO_CLASS_DIFF, NAME_TO_FUNCTION_DIFF},
    type_::{
        AnyCause, CallableContent, CallableParam, CallableParams, ClassGenerics, Dataclass,
        DataclassOptions, DataclassTransformObj, DbString, Enum, EnumMemberAlias,
        EnumMemberDefinition, ExtraItemsType, FunctionKind, GenericClass, NamedTuple, ParamType,
        ReplaceTypeVarLikes, StringSlice, Tuple, Type, TypeVarLike, TypeVarLikes, TypeVarVariance,
        TypedDict, TypedDictMember, TypedDictMembers, Variance,
    },
    type_helpers::{Class, FirstParamProperties, Function},
    utils::{debug_indent, join_with_commas},
};

use super::{
    CalculatedBaseClass, FuncNodeRef, Lookup, TypeComputation, TypeComputationOrigin,
    named_tuple::start_namedtuple_params,
    typed_dict::{TypedDictMemberGatherer, check_typed_dict_arguments},
};

// Save the ClassInfos on the class keyword
pub(crate) const CLASS_TO_CLASS_INFO_DIFFERENCE: i64 = 1;
// Save the type vars on `(` or `:` or `type_params` after the name
const CLASS_TO_TYPE_VARS_DIFFERENCE: i64 = NAME_TO_CLASS_DIFF as i64 + 1;

pub(crate) const ORDERING_METHODS: [&str; 4] = ["__lt__", "__le__", "__gt__", "__ge__"];

const EXCLUDED_PROTOCOL_ATTRIBUTES: [&str; 11] = [
    "__abstractmethods__",
    "__annotations__",
    "__dict__",
    "__doc__",
    "__init__",
    "__module__",
    "__new__",
    "__slots__",
    "__subclasshook__",
    "__weakref__",
    "__class_getitem__",
];

const NAMEDTUPLE_PROHIBITED_NAMES: [&str; 12] = [
    // Copied from Mypy
    "__new__",
    "__init__",
    "__slots__",
    "__getnewargs__",
    "_fields",
    "_field_defaults",
    "_field_types",
    "_make",
    "_replace",
    "_asdict",
    "_source",
    "__annotations__",
];

#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) struct ClassNodeRef<'file>(NodeRef<'file>);

impl<'db: 'file, 'file> ClassNodeRef<'file> {
    #[inline]
    pub fn new(file: &'file PythonFile, node_index: NodeIndex) -> Self {
        Self::from_node_ref(NodeRef::new(file, node_index))
    }

    #[inline]
    pub fn from_link(db: &'file Database, link: PointLink) -> Self {
        Self::from_node_ref(NodeRef::from_link(db, link))
    }

    #[inline]
    pub fn from_node_ref(node_ref: NodeRef<'file>) -> Self {
        debug_assert!(node_ref.maybe_class().is_some(), "{node_ref:?}");
        Self(node_ref)
    }

    pub fn into_node_ref(self) -> NodeRef<'file> {
        self.into()
    }

    #[inline]
    pub fn to_db_lifetime(self, db: &Database) -> ClassNodeRef<'_> {
        ClassNodeRef(self.0.to_db_lifetime(db))
    }

    pub fn node(&self) -> ClassDef<'file> {
        ClassDef::by_index(&self.0.file.tree, self.0.node_index)
    }

    pub fn name(&self) -> &'file str {
        self.node().name().as_str()
    }

    pub fn name_string_slice(&self) -> StringSlice {
        let name = self.node().name();
        StringSlice::new(self.0.file_index(), name.start(), name.end())
    }

    #[inline]
    fn class_info_node_ref(&self) -> NodeRef<'file> {
        self.0.add_to_node_index(CLASS_TO_CLASS_INFO_DIFFERENCE)
    }

    pub fn incomplete_mro(&self, db: &Database) -> bool {
        self.use_cached_class_infos(db).incomplete_mro
    }

    pub fn is_calculating_class_infos(&self) -> bool {
        self.class_info_node_ref().point().calculating()
    }

    pub fn use_cached_class_infos(&self, db: &'db Database) -> &'db ClassInfos {
        self.maybe_cached_class_infos(db)
            .unwrap_or_else(|| panic!("Tried to use uncalculated class infos for {}", self.name()))
    }

    pub fn maybe_cached_class_infos(&self, db: &'db Database) -> Option<&'db ClassInfos> {
        let node_ref = self.class_info_node_ref();
        if !node_ref.point().calculated() {
            return None;
        }
        match node_ref.to_db_lifetime(db).maybe_complex().unwrap() {
            ComplexPoint::ClassInfos(class_infos) => Some(class_infos),
            _ => unreachable!(),
        }
    }

    pub(crate) fn add_issue_on_name(&self, db: &Database, kind: IssueKind) {
        NodeRef::new(self.file, self.node_index).add_type_issue(db, kind)
    }

    #[inline]
    fn type_vars_node_ref(&self) -> NodeRef<'file> {
        self.0.add_to_node_index(CLASS_TO_TYPE_VARS_DIFFERENCE)
    }

    pub fn type_vars(&self, i_s: &InferenceState<'db, '_>) -> &'file TypeVarLikes {
        let node_ref = self.type_vars_node_ref();
        let point = node_ref.point();
        if point.calculated() {
            return TypeVarLikes::load_saved_type_vars(i_s.db, node_ref);
        }
        let node = self.node();
        let type_var_likes = if let Some(type_params) = node.type_params() {
            self.file
                .name_resolution_for_types(i_s)
                .compute_type_params_definition(i_s.as_parent_scope(), type_params, false)
        } else {
            let mut found = TypeVarFinder::find_class_type_vars(i_s, self);
            if found.is_empty() && i_s.db.project.should_infer_untyped_params() {
                let storage = self.class_storage();
                if let Some(name_index) = storage.class_symbol_table.lookup_symbol("__init__")
                    && let Some(func) = NodeRef::new(self.file, name_index)
                        .expect_name()
                        .name_def()
                        .unwrap()
                        .maybe_name_of_func()
                {
                    // Only generate type vars for classes that are not typed at all and have
                    // initialization params.
                    if !func.is_typed() && func.params().iter().nth(1).is_some() {
                        found = TypeVarLikes::new_untyped_params(func, true)
                    }
                }
            }
            found
        };

        if type_var_likes.is_empty() {
            node_ref.set_point(Point::new_specific(Specific::Analyzed, Locality::Todo));
        } else {
            node_ref.insert_complex(ComplexPoint::TypeVarLikes(type_var_likes), Locality::Todo);
        }
        self.type_vars(i_s)
    }

    pub fn use_cached_type_vars(&self, db: &'file Database) -> &'file TypeVarLikes {
        TypeVarLikes::load_saved_type_vars(db, self.type_vars_node_ref())
    }

    pub fn class_link_in_mro(&self, db: &Database, link: PointLink) -> bool {
        if self.0.as_link() == link {
            return true;
        }
        let class_infos = self.use_cached_class_infos(db);
        class_infos.mro.iter().any(|b| match &b.type_ {
            Type::Class(c) => link == c.link,
            t => t
                .inner_generic_class_with_db(db)
                .is_some_and(|c| c.node_ref.as_link() == link),
        })
    }

    pub fn maybe_typed_dict_definition(&self) -> Option<&TypedDictDefinition> {
        NodeRef::new(self.file, self.node().name_def().index())
            .maybe_complex()
            .and_then(|c| match c {
                ComplexPoint::TypedDictDefinition(tdd) => Some(tdd),
                _ => None,
            })
    }

    pub fn class_storage(&self) -> &'file ClassStorage {
        let complex = self.maybe_complex().unwrap_or_else(|| {
            panic!(
                "Node {:?} ({}:{}) is not a complex class",
                self.file.tree.debug_info(self.node_index),
                self.file_index(),
                self.node_index
            )
        });
        match complex {
            ComplexPoint::Class(c) => c,
            _ => unreachable!("Probably an issue with indexing: {complex:?}"),
        }
    }

    pub fn infer_variance_of_type_params(self, db: &Database, check_narrowed: bool) {
        // To avoid recursions, we add calculating to the : node on class.
        let colon_ref = NodeRef::new(self.file, self.node().block().index() - 1);
        let point = colon_ref.point();
        if point.calculating() || point.calculated() {
            return;
        }
        colon_ref.set_point(Point::new_calculating());

        let type_var_likes = self.use_cached_type_vars(db);
        let class = Class::with_self_generics(db, self);
        debug!(
            "Infer variances of TypeVars in {}",
            ClassInitializer::from_node_ref(self).qualified_name(db)
        );
        let _indent = debug_indent();
        for (name, lazy_variance) in class.use_cached_class_infos(db).variance_map.iter() {
            let type_var_index = type_var_likes
                .iter()
                .position(|tvl| {
                    if let TypeVarLike::TypeVar(tv) = tvl {
                        tv.name == *name
                    } else {
                        false
                    }
                })
                .unwrap();
            lazy_variance.get_or_init(|| {
                debug!("Infer variance for TypeVar #{type_var_index:?}");
                let indent = debug_indent();
                let variance =
                    class.infer_variance_for_index(db, type_var_index.into(), check_narrowed);
                drop(indent);
                debug!("Variance for TypeVar #{type_var_index:?} inferred as {variance:?}");
                variance
            });
        }
        colon_ref.set_point(Point::new_specific(Specific::Analyzed, Locality::Todo));
    }

    pub fn add_issue_if_deprecated(
        self,
        db: &Database,
        on_name: Option<NodeRef>,
        add_issue: impl FnOnce(IssueKind),
    ) {
        let class = ClassInitializer::from_node_ref(self);
        class.ensure_calculated_class_infos(db);
        if let Some(reason) = class
            .maybe_cached_class_infos(db)
            .and_then(|c| c.deprecated_reason.as_ref())
        {
            if should_add_deprecated(db, *self, on_name) {
                // The error was already added on the from ... import
                return;
            }
            add_issue(IssueKind::Deprecated {
                identifier: format!("class {}", class.qualified_name(db)).into(),
                reason: reason.clone(),
            })
        }
    }
}

impl<'a> std::ops::Deref for ClassNodeRef<'a> {
    type Target = NodeRef<'a>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl std::cmp::PartialEq<NodeRef<'_>> for ClassNodeRef<'_> {
    fn eq(&self, other: &NodeRef) -> bool {
        self.0 == *other
    }
}

impl<'a> From<ClassNodeRef<'a>> for NodeRef<'a> {
    fn from(value: ClassNodeRef<'a>) -> Self {
        value.0
    }
}

impl<'a> std::ops::Deref for ClassInitializer<'a> {
    type Target = ClassNodeRef<'a>;

    fn deref(&self) -> &Self::Target {
        &self.node_ref
    }
}

#[derive(Clone, Copy)]
pub(crate) struct ClassInitializer<'a> {
    pub node_ref: ClassNodeRef<'a>,
    pub class_storage: &'a ClassStorage,
}

impl<'db: 'a, 'a> ClassInitializer<'a> {
    pub fn new(node_ref: ClassNodeRef<'a>, class_storage: &'a ClassStorage) -> Self {
        Self {
            node_ref,
            class_storage,
        }
    }

    pub fn from_node_ref(node_ref: ClassNodeRef<'a>) -> Self {
        Self::new(node_ref, node_ref.class_storage())
    }

    pub fn from_link(db: &'a Database, link: PointLink) -> Self {
        Self::from_node_ref(ClassNodeRef::from_link(db, link))
    }

    pub fn qualified_name(&self, db: &Database) -> String {
        self.class_storage
            .parent_scope
            .qualified_name(db, self.node_ref.0, self.name())
    }

    pub(crate) fn maybe_type_var_like_in_parent(
        &self,
        db: &Database,
        type_var: &TypeVarLike,
    ) -> Option<TypeVarCallbackReturn> {
        match self.class_storage.parent_scope {
            ParentScope::Module => None,
            ParentScope::Class(node_index) => {
                let parent_class =
                    Self::from_node_ref(ClassNodeRef::new(self.node_ref.file, node_index));
                parent_class.find_type_var_like_including_ancestors(db, type_var, true)
            }
            ParentScope::Function(node_index) => {
                Function::new_with_unknown_parent(db, NodeRef::new(self.node_ref.file, node_index))
                    .find_type_var_like_including_ancestors(db, type_var, false)
            }
        }
    }

    pub(crate) fn find_type_var_like_including_ancestors(
        &self,
        db: &Database,
        type_var_like: &TypeVarLike,
        class_seen: bool,
    ) -> Option<TypeVarCallbackReturn> {
        if let Some(tvl) = self
            .use_cached_type_vars(db)
            .find(type_var_like, self.node_ref.as_link())
        {
            if class_seen {
                return Some(TypeVarCallbackReturn::AddIssue(
                    IssueKind::TypeVarLikeBoundByOuterClass {
                        type_var_like: type_var_like.clone(),
                    },
                ));
            }
            return Some(TypeVarCallbackReturn::TypeVarLike(tvl));
        }
        self.maybe_type_var_like_in_parent(db, type_var_like)
    }

    fn has_a_total_ordering_method_in_mro(&self, db: &Database, mro: &[BaseClass]) -> bool {
        for n in ORDERING_METHODS {
            if self
                .class_storage
                .class_symbol_table
                .lookup_symbol(n)
                .is_some()
            {
                return true;
            }
            for b in mro {
                if let Type::Class(c) = &b.type_
                    && c.class(db)
                        .class_storage
                        .class_symbol_table
                        .lookup_symbol(n)
                        .is_some()
                {
                    return true;
                }
            }
        }
        false
    }

    pub fn ensure_calculated_class_infos(&self, db: &Database) {
        if self.node_ref.class_info_node_ref().point().calculated() {
            return;
        }
        InferenceState::run_with_parent_scope(
            db,
            self.node_ref.file,
            self.class_storage.parent_scope,
            |i_s| {
                debug!("Calculate class infos for {}", self.name());
                let _indent = debug_indent();
                self.insert_class_infos(&i_s)
            },
        )
    }

    fn insert_class_infos(&self, i_s: &InferenceState) {
        let node_ref = self.node_ref.class_info_node_ref();
        debug_assert!(
            NodeRef::new(node_ref.file, self.node().name_def().index())
                .point()
                .calculated()
        );

        node_ref.set_point(Point::new_calculating());
        let db = i_s.db;

        let type_vars = self.type_vars(i_s);

        let mut was_dataclass = None;
        let mut is_final = false;
        let mut total_ordering = false;
        let mut is_runtime_checkable = false;
        let mut dataclass_transform = None;
        let mut deprecated_reason = None;
        if let Some(decorated) = self.node().maybe_decorated() {
            let name_resolution = self.node_ref.file.name_resolution_for_types(i_s);
            let mut dataclass_options = None;
            for decorator in decorated.decorators().iter() {
                let expr = decorator.named_expression().expression();
                if let ExpressionContent::ExpressionPart(ExpressionPart::Primary(primary)) =
                    expr.unpack()
                    && let PrimaryContent::Execution(exec) = primary.second()
                {
                    match name_resolution.lookup_type_primary_or_atom_if_only_names(primary.first())
                    {
                        Some(Lookup::T(TypeContent::InvalidVariable(
                            InvalidVariableType::Function { node_ref },
                        ))) => {
                            if node_ref.is_name_defined_in_module(db, "dataclasses", "dataclass") {
                                dataclass_options = Some(check_dataclass_options(
                                    db,
                                    self.node_ref.file,
                                    exec,
                                    DataclassOptions::default(),
                                ));
                            } else if let Some(d) = maybe_dataclass_transform_func(db, node_ref) {
                                dataclass_options = Some(check_dataclass_options(
                                    db,
                                    self.node_ref.file,
                                    exec,
                                    d.as_dataclass_options(),
                                ));
                            }
                        }
                        Some(Lookup::T(TypeContent::SpecialCase(
                            Specific::TypingDataclassTransform,
                        ))) => {
                            let d = name_resolution.insert_dataclass_transform(primary, exec);
                            dataclass_transform = Some(Box::new(d.clone()));
                        }
                        Some(Lookup::T(TypeContent::Class { node_ref, .. }))
                            if Some(*node_ref) == db.python_state.deprecated() =>
                        {
                            deprecated_reason =
                                Some(self.file.inference(i_s).infer_deprecated_reason(decorator));
                        }
                        _ => (),
                    }
                    continue;
                }
                if let Some(Lookup::T(TypeContent::InvalidVariable(
                    InvalidVariableType::Function { node_ref },
                ))) = name_resolution.lookup_type_expr_if_only_names(expr)
                {
                    if node_ref.is_name_defined_in_module(db, "dataclasses", "dataclass") {
                        dataclass_options = Some(DataclassOptions::default());
                    } else if node_ref == db.python_state.typing_final() {
                        is_final = true;
                    } else if node_ref == db.python_state.total_ordering_node_ref() {
                        total_ordering = true;
                    } else if node_ref == db.python_state.runtime_checkable_node_ref()
                        || node_ref
                            == db
                                .python_state
                                .typing_extensions_runtime_checkable_node_ref()
                    {
                        is_runtime_checkable = true;
                    } else if let Some(d) = maybe_dataclass_transform_func(db, node_ref) {
                        dataclass_options = Some(d.as_dataclass_options());
                    }
                }
            }
            if let Some(dataclass_options) = dataclass_options {
                let dataclass = Dataclass::new_uninitialized(
                    self.node_ref.as_link(),
                    type_vars,
                    dataclass_options,
                );
                was_dataclass = Some(dataclass);
            }
        }

        let (mut class_infos, typed_dict_options) = self.calculate_class_infos(i_s, type_vars);
        if let Some(dataclass) = &was_dataclass {
            // It is possible that there was a dataclass_transform in the metaclass
            let _ = class_infos
                .undefined_generics_type
                .set(Arc::new(Type::Dataclass(dataclass.clone())));
            if let Some(was) = match class_infos.kind {
                ClassKind::Normal => None,
                ClassKind::Protocol => Some("A Protocol"),
                ClassKind::Enum => Some("An Enum"),
                ClassKind::TypedDict => Some("A TypedDict"),
                ClassKind::Tuple => Some("A Tuple"),
                ClassKind::NamedTuple => Some("A NamedTuple"),
            } {
                NodeRef::new(self.node_ref.file, self.node().name_def().index())
                    .add_type_issue(db, IssueKind::DataclassCannotBe { kind: was.into() });
            }
            class_infos.kind = ClassKind::Normal;
        }
        if dataclass_transform.is_some() {
            class_infos.dataclass_transform = dataclass_transform;
        }
        if total_ordering && !self.has_a_total_ordering_method_in_mro(db, &class_infos.mro) {
            // If there is no corresponding method, we just ignore the MRO
            NodeRef::new(self.node_ref.file, self.node().name_def().index())
                .add_type_issue(db, IssueKind::TotalOrderingMissingMethod);
            total_ordering = false;
        }
        class_infos.is_final |= is_final;
        class_infos.total_ordering = total_ordering;
        class_infos.deprecated_reason = deprecated_reason;

        if class_infos.kind == ClassKind::Protocol {
            class_infos.is_runtime_checkable = is_runtime_checkable;
        } else {
            if is_runtime_checkable {
                self.add_issue_on_name(
                    db,
                    IssueKind::RuntimeCheckableCanOnlyBeUsedWithProtocolClasses,
                );
            }
            class_infos.is_runtime_checkable = true;
        }

        if is_final && !class_infos.abstract_attributes.is_empty() {
            self.add_issue_on_name(
                db,
                IssueKind::FinalClassHasAbstractAttributes {
                    class_name: self.qualified_name(db).into(),
                    attributes: join_abstract_attributes(db, &class_infos.abstract_attributes),
                },
            );
        }

        if let MetaclassState::Some(link) = class_infos.metaclass
            && Class::from_undefined_generics(db, link)
                .class_link_in_mro(db, db.python_state.enum_meta_link())
        {
            if !self.use_cached_type_vars(db).is_empty_or_untyped() {
                self.add_issue_on_name(db, IssueKind::EnumCannotBeGeneric);
            }
            class_infos.kind = ClassKind::Enum;
            let (members, aliases) = self.enum_members(db);
            if !members.is_empty() {
                let enum_ = Enum::new(
                    DbString::StringSlice(self.name_string_slice()),
                    self.node_ref.as_link(),
                    self.node_ref.as_link(),
                    self.class_storage.parent_scope,
                    members,
                    aliases,
                    OnceLock::new(),
                );
                let enum_type = Arc::new(Type::Enum(enum_.clone()));
                // In case enum is combined with dataclass, just let the dataclass win
                let _ = class_infos.undefined_generics_type.set(enum_type.clone());
            }
        }
        let mut was_typed_dict = None;
        if let Some(typed_dict_options) = typed_dict_options {
            let td = TypedDict::new_class_definition(
                self.name_string_slice(),
                self.node_ref.as_link(),
                type_vars.clone(),
                is_final,
            );
            // In case TypedDict is combined with dataclass, just let the dataclass win
            let _ = class_infos
                .undefined_generics_type
                .set(Arc::new(Type::TypedDict(td.clone())));
            NodeRef::new(self.node_ref.file, self.node().name_def().index()).insert_complex(
                ComplexPoint::TypedDictDefinition(TypedDictDefinition::new(
                    td.clone(),
                    typed_dict_options.clone(),
                )),
                Locality::ImplicitExtern,
            );
            was_typed_dict = Some((td, typed_dict_options));
        }

        if type_vars.is_empty()
            && i_s.db.project.should_infer_untyped_params()
            && matches!(class_infos.kind, ClassKind::Normal)
            && was_dataclass.is_none()
            && class_infos.dataclass_transform.is_none()
        {
            // TODO this is a weird place to put it, we also override type vars here and it's
            // especially questionable that we inherit from the first type vars and not from the
            // same class that has the __init__/__new__ that the rest of our logic uses. However
            // it's kind of hard to unite these pieces, because of different layers of
            // abstractions.
            for base in class_infos.mro.iter_mut() {
                if base.is_direct_base
                    && let Type::Class(c) = &mut base.type_
                {
                    let base_class = c.class(db);
                    let base_type_vars = base_class.type_vars(i_s);
                    if base_type_vars.has_from_untyped_params() {
                        self.type_vars_node_ref().insert_complex(
                            ComplexPoint::TypeVarLikes(base_type_vars.clone()),
                            Locality::Todo,
                        );
                        c.generics = ClassGenerics::List(
                            base_type_vars.as_self_generic_list(self.as_link()),
                        );
                        break;
                    }
                }
            }
        }

        node_ref.insert_complex(ComplexPoint::ClassInfos(class_infos), Locality::Todo);
        debug_assert!(node_ref.point().calculated());

        // Now that the class has been saved, we can use it like an actual class. We have to do
        // some member initialization things with TypedDicts, Enums, etc.
        let class = Class::with_undefined_generics(self.node_ref);
        if let Some(td) = was_typed_dict {
            initialize_typed_dict_members(db, &class, td);
        } else {
            // Change the methods that are actually changed by Python to be classmethods.
            for name in ["__init_subclass__", "__class_getitem__"] {
                if let Some(node_index) = self.class_storage.class_symbol_table.lookup_symbol(name)
                {
                    let file = self.node_ref.file;
                    if let Some(func_def) = NodeRef::new(file, node_index).maybe_name_of_function()
                    {
                        let node_ref = NodeRef::new(file, func_def.index());
                        let func = Function::new(node_ref, Some(class));
                        func.ensure_cached_func(i_s);
                        let mut c = func.as_callable(i_s, FirstParamProperties::None);
                        if func_def.maybe_decorated().is_some() {
                            debug!("Make method a classmethod: {name}");
                        } else {
                            if !c.kind.had_first_self_or_class_annotation() {
                                let params = &mut c.params;
                                let CallableParams::Simple(ps) = params else {
                                    unreachable!()
                                };
                                *ps = ps
                                    .iter()
                                    .enumerate()
                                    .map(|(i, p)| {
                                        let mut p = p.clone();
                                        if let Some(t) = p.type_.maybe_positional_type()
                                            && i == 0
                                        {
                                            p.type_ = ParamType::PositionalOnly(Type::Type(
                                                Arc::new(t.clone()),
                                            ));
                                        }
                                        p
                                    })
                                    .collect();
                            }
                            c.kind = FunctionKind::Classmethod {
                                had_first_self_or_class_annotation: true,
                            };
                            node_ref.insert_type(Type::Callable(Arc::new(c)));
                        }
                    }
                }
            }
        }
        debug!("Finished calculating class infos for {}", self.name());
    }

    fn calculate_class_infos(
        &self,
        i_s: &InferenceState<'db, '_>,
        type_vars: &TypeVarLikes,
    ) -> (Box<ClassInfos>, Option<TypedDictArgs>) {
        // Calculate all type vars beforehand
        let db = i_s.db;

        let mut bases: Vec<Type> = vec![];
        let mut incomplete_mro = false;
        let mut class_kind = ClassKind::Normal;
        let mut typed_dict_options = None;
        let mut had_new_typed_dict = false;
        let mut is_new_named_tuple = false;
        let mut metaclass = MetaclassState::None;
        let mut has_slots = self.class_storage.slots.is_some();
        let mut is_final = false;
        let mut dataclass_transform = None;
        let mut promote_to = None;
        let undefined_generics_type = OnceLock::new();
        let set_type_to_dataclass = |dc: &DataclassTransformObj, set_frozen_state_unknown: bool| {
            let mut options = dc.as_dataclass_options();
            if set_frozen_state_unknown {
                options.frozen = None;
            }
            if let Some(args) = self.node().arguments() {
                for arg in args.iter() {
                    if let Argument::Keyword(kw) = arg {
                        options.assign_keyword_arg_to_dataclass_options(db, self.node_ref.file, kw);
                    }
                    // If another option is present, just ignore it. It is either checked by
                    // __init_subclass__ or it's a complex metaclass and we're screwed.
                }
            }
            undefined_generics_type
                .set(Arc::new(Type::Dataclass(Dataclass::new_uninitialized(
                    self.node_ref.as_link(),
                    type_vars,
                    options,
                ))))
                // Errors are ignored for now, whatever was first takes precedence.
                .ok();
        };
        let arguments = self.node().arguments();
        if let Some(arguments) = arguments {
            let has_type_params = self.node().type_params().is_some();
            // Check metaclass before checking all the arguments, because it has a preference over
            // the metaclasses of the subclasses.
            #[allow(clippy::mutable_key_type)]
            let mut unbound_type_vars = FastHashSet::default();
            for argument in arguments.iter() {
                if let Argument::Keyword(kwarg) = argument {
                    let (name, expr) = kwarg.unpack();
                    if name.as_str() == "metaclass" {
                        let node_ref = NodeRef::new(self.node_ref.file, expr.index());
                        let meta_base = TypeComputation::new(
                            i_s,
                            self.node_ref.file,
                            self.node_ref.as_link(),
                            &mut |_, _: &_, tvl: TypeVarLike, _, _: Name| {
                                if has_type_params {
                                    // This can happen if two type var likes are used.
                                    unbound_type_vars.insert(tvl);
                                    TypeVarCallbackReturn::AnyDueToError
                                } else {
                                    TypeVarCallbackReturn::NotFound {
                                        allow_late_bound_callables: false,
                                    }
                                }
                            },
                            TypeComputationOrigin::BaseClass,
                        )
                        .compute_base_class(expr);
                        let mut add_meta = |link| {
                            let c = ClassInitializer::from_link(db, link);
                            if c.is_calculating_class_infos() {
                                NodeRef::new(self.node_ref.file, name.index()).add_type_issue(
                                    db,
                                    IssueKind::CyclicDefinition {
                                        name: c.name().into(),
                                    },
                                );
                                metaclass = MetaclassState::Unknown;
                            } else if c.incomplete_mro(db)
                                || c.class_link_in_mro(
                                    db,
                                    db.python_state.bare_type_node_ref().as_link(),
                                )
                            {
                                Self::update_metaclass(
                                    i_s,
                                    node_ref,
                                    &mut metaclass,
                                    MetaclassState::Some(link),
                                );
                                if let Some(infos) = c.maybe_cached_class_infos(db)
                                    && let Some(dt) = &infos.dataclass_transform
                                {
                                    set_type_to_dataclass(dt, true);
                                    dataclass_transform = infos.dataclass_transform.clone();
                                }
                            } else {
                                node_ref
                                    .add_type_issue(db, IssueKind::MetaclassMustInheritFromType);
                            }
                        };
                        match meta_base {
                            CalculatedBaseClass::Type(Type::Class(GenericClass {
                                link,
                                generics: ClassGenerics::None { .. },
                            })) => add_meta(link),
                            CalculatedBaseClass::Type(t)
                                if t.maybe_class(db).is_some_and(|cls| {
                                    cls.type_vars(i_s).has_from_untyped_params()
                                }) =>
                            {
                                add_meta(t.maybe_class(db).unwrap().as_link())
                            }
                            CalculatedBaseClass::Unknown => {
                                if node_ref.file.flags(db).disallow_subclassing_any {
                                    NodeRef::new(self.node_ref.file, kwarg.index()).add_type_issue(
                                        db,
                                        IssueKind::DisallowedAnyMetaclass {
                                            class: expr.as_code().into(),
                                        },
                                    );
                                }
                                metaclass = MetaclassState::Unknown
                            }
                            _ => {
                                debug!("Invalid metaclass: {meta_base:?}");
                                node_ref.add_type_issue(db, IssueKind::InvalidMetaclass);
                            }
                        }
                    }
                }
            }

            // Calculate the type var remapping
            for argument in arguments.iter() {
                if let Argument::Positional(n) = argument {
                    let base = TypeComputation::new(
                        i_s,
                        self.node_ref.file,
                        self.node_ref.as_link(),
                        &mut |_, _: &_, type_var_like: TypeVarLike, _, _: Name| {
                            if let Some(usage) =
                                type_vars.find(&type_var_like, self.node_ref.as_link())
                            {
                                TypeVarCallbackReturn::TypeVarLike(usage)
                            } else if let Some(usage) =
                                self.maybe_type_var_like_in_parent(db, &type_var_like)
                            {
                                usage
                            } else if has_type_params {
                                // This can happen if two type var likes are used.
                                unbound_type_vars.insert(type_var_like);
                                TypeVarCallbackReturn::AnyDueToError
                            } else {
                                TypeVarCallbackReturn::NotFound {
                                    allow_late_bound_callables: false,
                                }
                            }
                        },
                        TypeComputationOrigin::BaseClass,
                    )
                    .compute_base_class(n.expression());
                    match base {
                        CalculatedBaseClass::Type(t) => {
                            if let Some(name) = bases
                                .iter()
                                .find_map(|base| base.check_duplicate_base_class(db, &t))
                            {
                                NodeRef::new(self.node_ref.file, n.index())
                                    .add_type_issue(db, IssueKind::DuplicateBaseClass { name });
                                incomplete_mro = true;
                                continue;
                            }
                            bases.push(t);
                            let class = match &bases.last().unwrap() {
                                Type::Class(c) => {
                                    let c = Self::from_link(db, c.link);
                                    if let Some(cached) = c.maybe_cached_class_infos(db) {
                                        if let new_promote @ Some(_) = cached.promote_to() {
                                            promote_to = new_promote;
                                        }
                                        if cached.kind != ClassKind::Normal
                                            && class_kind == ClassKind::Normal
                                            && !matches!(cached.kind, ClassKind::Protocol)
                                        {
                                            class_kind = cached.kind;
                                        }
                                    }
                                    Some(c)
                                }
                                Type::Tuple(_) => {
                                    if class_kind == ClassKind::Normal {
                                        class_kind = ClassKind::Tuple;
                                    } else {
                                        debug!("TODO Tuple overwrite with other");
                                    }
                                    None
                                }
                                Type::Dataclass(d) => Some(Self::from_link(db, d.class.link)),
                                Type::TypedDict(typed_dict) => {
                                    let options = check_typed_dict_arguments(
                                        i_s,
                                        self.file,
                                        arguments.iter(),
                                        true,
                                        |issue| {
                                            NodeRef::new(self.node_ref.file, n.index())
                                                .add_type_issue(db, issue)
                                        },
                                    );
                                    if typed_dict_options.is_none() {
                                        typed_dict_options = Some(options);
                                    }
                                    class_kind = ClassKind::TypedDict;
                                    if typed_dict.is_final {
                                        NodeRef::new(self.node_ref.file, n.index()).add_type_issue(
                                            db,
                                            IssueKind::CannotInheritFromFinalClass {
                                                class_name: Box::from(
                                                    typed_dict.name.unwrap().as_str(db),
                                                ),
                                            },
                                        );
                                    }
                                    continue;
                                }
                                _ => unreachable!(),
                            };
                            if let Some(class) = class {
                                if class.is_calculating_class_infos() {
                                    let name = Box::<str>::from(class.name());
                                    bases.pop();
                                    incomplete_mro = true;
                                    NodeRef::new(self.node_ref.file, n.index())
                                        .add_type_issue(db, IssueKind::CyclicDefinition { name });
                                } else {
                                    let cached_class_infos = class.use_cached_class_infos(db);
                                    if cached_class_infos.is_final {
                                        is_final = cached_class_infos.is_final;
                                        NodeRef::new(self.node_ref.file, n.index()).add_type_issue(
                                            db,
                                            IssueKind::CannotInheritFromFinalClass {
                                                class_name: Box::from(class.name()),
                                            },
                                        );
                                    }
                                    incomplete_mro |= cached_class_infos.incomplete_mro;
                                    has_slots |= cached_class_infos.has_slots;
                                    // For now simply ignore all metaclasses in builtins, see
                                    // also:
                                    // https://github.com/python/typeshed/issues/13466
                                    // https://github.com/python/mypy/issues/15870#issuecomment-1681373243
                                    if class.node_ref.file_index()
                                        != db.python_state.builtins().file_index
                                    {
                                        Self::update_metaclass(
                                            i_s,
                                            NodeRef::new(self.node_ref.file, n.index()),
                                            &mut metaclass,
                                            cached_class_infos.metaclass,
                                        );
                                    }
                                    match &cached_class_infos.kind {
                                        ClassKind::NamedTuple => {
                                            if matches!(
                                                class_kind,
                                                ClassKind::Normal | ClassKind::NamedTuple
                                            ) {
                                                class_kind = ClassKind::NamedTuple;
                                            } else {
                                                debug!("TODO NamedTuple overwrite with other");
                                                class_kind = ClassKind::NamedTuple;
                                            }
                                        }
                                        ClassKind::TypedDict => unreachable!(),
                                        _ => (),
                                    }
                                    if let Some(dt) = &cached_class_infos.dataclass_transform {
                                        // Metaclasses don't inherit the dataclass_transform
                                        // state. See e.g. testDataclassTransformViaSubclassOfMetaclass
                                        if !class.class_link_in_mro(
                                            db,
                                            db.python_state.bare_type_node_ref().as_link(),
                                        ) {
                                            dataclass_transform = Some(dt.clone());
                                            set_type_to_dataclass(dt, false)
                                        }
                                    }
                                }
                            }
                        }
                        // TODO this might overwrite other class types
                        CalculatedBaseClass::Protocol { with_brackets } => {
                            if has_type_params && with_brackets {
                                NodeRef::new(self.node_ref.file, n.index()).add_type_issue(
                                    db,
                                    IssueKind::ProtocolWithTypeParamsNoBracketsExpected,
                                );
                            }
                            class_kind = ClassKind::Protocol;
                            metaclass = MetaclassState::Some(db.python_state.abc_meta_link())
                        }
                        CalculatedBaseClass::NamedTuple(named_tuple) => {
                            let named_tuple =
                                named_tuple.clone_with_new_init_class(self.name_string_slice());
                            bases.push(Type::NamedTuple(named_tuple));
                            class_kind = ClassKind::NamedTuple;
                        }
                        CalculatedBaseClass::NewNamedTuple => {
                            is_new_named_tuple = true;
                            let named_tuple = self.named_tuple_from_class(db);
                            bases.push(Type::NamedTuple(named_tuple));
                            class_kind = ClassKind::NamedTuple;
                        }
                        CalculatedBaseClass::TypedDict => {
                            if had_new_typed_dict {
                                NodeRef::new(self.node_ref.file, n.index()).add_type_issue(
                                    db,
                                    IssueKind::DuplicateBaseClass {
                                        name: "TypedDict".into(),
                                    },
                                );
                            } else {
                                had_new_typed_dict = true;
                                class_kind = ClassKind::TypedDict;
                                let options = check_typed_dict_arguments(
                                    i_s,
                                    self.file,
                                    arguments.iter(),
                                    true,
                                    |issue| {
                                        NodeRef::new(self.node_ref.file, n.index())
                                            .add_type_issue(db, issue)
                                    },
                                );
                                if typed_dict_options.is_none() {
                                    typed_dict_options = Some(options);
                                }
                            }
                        }
                        CalculatedBaseClass::Generic => {
                            if has_type_params {
                                NodeRef::new(self.node_ref.file, n.index()).add_type_issue(
                                    db,
                                    IssueKind::GenericWithTypeParamsIsRedundant,
                                );
                            }
                        }
                        CalculatedBaseClass::Unknown => {
                            if self.node_ref.file.flags(db).disallow_subclassing_any {
                                NodeRef::new(self.node_ref.file, n.index()).add_type_issue(
                                    db,
                                    IssueKind::DisallowedAnySubclass {
                                        class: n.as_code().into(),
                                    },
                                );
                            }
                            incomplete_mro = true;
                        }
                        CalculatedBaseClass::InvalidEnum(enum_) => {
                            let name = enum_.name.as_str(db);
                            NodeRef::new(self.node_ref.file, n.index()).add_type_issue(
                                db,
                                IssueKind::EnumWithMembersNotExtendable { name: name.into() },
                            );
                            if enum_.class(db).use_cached_class_infos(db).is_final {
                                NodeRef::new(self.node_ref.file, n.index()).add_type_issue(
                                    db,
                                    IssueKind::CannotInheritFromFinalClass {
                                        class_name: Box::from(name),
                                    },
                                );
                            }
                            incomplete_mro = true;
                        }
                        CalculatedBaseClass::Invalid => {
                            NodeRef::new(self.node_ref.file, n.index())
                                .add_type_issue(db, IssueKind::InvalidBaseClass);
                            incomplete_mro = true;
                        }
                        CalculatedBaseClass::TypeAliasSyntax => {
                            NodeRef::new(self.node_ref.file, n.index())
                                .add_type_issue(db, IssueKind::TypeAliasSyntaxInBaseClassIsInvalid);
                            incomplete_mro = true;
                        }
                    };
                }
            }
            for type_var_like in unbound_type_vars.into_iter() {
                NodeRef::new(self.node_ref.file, arguments.index()).add_type_issue(
                    db,
                    IssueKind::TypeParametersShouldBeDeclared { type_var_like },
                );
            }
        }
        match class_kind {
            ClassKind::TypedDict => {
                if bases.iter().any(|t| !matches!(t, Type::TypedDict(_))) {
                    NodeRef::new(self.node_ref.file, arguments.unwrap().index())
                        .add_type_issue(db, IssueKind::TypedDictBasesMustBeTypedDicts);
                }
            }
            ClassKind::Protocol => {
                if bases.iter().any(|t| {
                    t.maybe_class(db).is_none_or(|cls| {
                        !cls.is_protocol(db) && cls.node_ref != db.python_state.object_node_ref()
                    })
                }) {
                    NodeRef::new(self.node_ref.file, arguments.unwrap().index())
                        .add_type_issue(db, IssueKind::BasesOfProtocolMustBeProtocol);
                }
            }
            _ => (),
        }
        if is_new_named_tuple && bases.len() > 1 {
            NodeRef::new(self.node_ref.file, arguments.unwrap().index())
                .add_type_issue(db, IssueKind::NamedTupleShouldBeASingleBase);
        }

        let (mro, linearizable) = linearize_mro_and_return_linearizable(db, &bases);
        if !linearizable {
            NodeRef::new(self.node_ref.file, self.node().arguments().unwrap().index())
                .add_type_issue(
                    db,
                    IssueKind::InconsistentMro {
                        name: self.name().into(),
                    },
                );
        }

        let mut found_tuple_like = None;
        for base in mro.iter() {
            if matches!(base.type_, Type::Tuple(_) | Type::NamedTuple(_)) {
                if let Some(found_tuple_like) = found_tuple_like {
                    if found_tuple_like != &base.type_ {
                        NodeRef::new(self.node_ref.file, arguments.unwrap().index())
                            .add_type_issue(db, IssueKind::IncompatibleBaseTuples);
                    }
                } else {
                    found_tuple_like = Some(&base.type_);
                }
            }
        }
        let protocol_members = if class_kind == ClassKind::Protocol {
            self.gather_protocol_members()
        } else {
            Default::default()
        };
        let abstract_attributes =
            self.calculate_abstract_attributes(db, &metaclass, &class_kind, &mro);
        (
            Box::new(ClassInfos {
                mro,
                metaclass,
                incomplete_mro,
                kind: class_kind,
                has_slots,
                protocol_members,
                is_final,
                in_django_stubs: Default::default(),
                variance_map: type_vars
                    .iter()
                    .filter_map(|tvl| match tvl {
                        TypeVarLike::TypeVar(tv) if tv.variance == TypeVarVariance::Inferred => {
                            Some((tv.name, OnceLock::new()))
                        }
                        _ => None,
                    })
                    .collect(),
                total_ordering: false,
                promote_to: Mutex::new(promote_to),
                is_runtime_checkable: true,
                abstract_attributes,
                deprecated_reason: None,
                dataclass_transform,
                undefined_generics_type,
            }),
            typed_dict_options,
        )
    }

    fn update_metaclass(
        i_s: &InferenceState<'db, '_>,
        node_ref: NodeRef,
        current: &mut MetaclassState,
        new: MetaclassState,
    ) {
        match new {
            MetaclassState::None => (),
            MetaclassState::Unknown => {
                if *current == MetaclassState::None {
                    *current = MetaclassState::Unknown
                }
            }
            MetaclassState::Some(link2) => match current {
                MetaclassState::Some(link1) => {
                    let t1 = Type::Class(GenericClass {
                        link: *link1,
                        generics: ClassGenerics::new_none(),
                    });
                    let t2 = Type::Class(GenericClass {
                        link: link2,
                        generics: ClassGenerics::new_none(),
                    });
                    if !t1.is_simple_sub_type_of(i_s, &t2).bool() {
                        if t2.is_simple_sub_type_of(i_s, &t1).bool() {
                            *current = new
                        } else {
                            node_ref.add_type_issue(i_s.db, IssueKind::MetaclassConflict);
                        }
                    }
                }
                _ => *current = new,
            },
        }
    }

    fn enum_members(&self, db: &Database) -> (Box<[EnumMemberDefinition]>, Box<[EnumMemberAlias]>) {
        let mut members = vec![];
        let mut aliases = vec![];
        let mut name_indexes = vec![];
        for (name, name_index) in self.class_storage.class_symbol_table.iter() {
            // It seems like Enums treat private, "dunder" and "sunder" names special.
            // See also https://github.com/python/cpython/blob/4701ff92d747002d04b67688c7a581b1952773ac/Lib/enum.py#L353-L385
            if name.starts_with('_') && (name.ends_with('_') || name.starts_with("__")) {
                if name == "__members__" {
                    let name_node_ref = NodeRef::new(self.node_ref.file, *name_index);
                    if !name_node_ref
                        .expect_name()
                        .is_assignment_annotation_without_definition()
                    {
                        name_node_ref.add_type_issue(db, IssueKind::EnumMembersAttributeOverwritten)
                    }
                }
                continue;
            }
            name_indexes.push(name_index);
        }

        // The name indexes are not guarantueed to be sorted by its order in the tree. We however
        // want the original order in an enum.
        name_indexes.sort();

        let search_decorated_for =
            |maybe_decorated: Option<Decorated>, check_against: Option<NodeRef>| {
                (|| {
                    let check_against = check_against?;
                    maybe_decorated?.decorators().iter().find_map(|decorator| {
                        match self
                            .file
                            .name_resolution_for_types(&InferenceState::from_class(
                                db,
                                &Class::from_non_generic_node_ref(self.node_ref),
                            ))
                            .lookup_decorator_if_only_names(decorator)?
                        {
                            Lookup::T(TypeContent::Class { node_ref, .. }) => {
                                Some(node_ref == check_against)
                            }
                            _ => None,
                        }
                    })
                })()
                .unwrap_or_default()
            };
        for &name_index in name_indexes {
            let name_node_ref = NodeRef::new(self.node_ref.file, name_index);
            if let Some(func) = name_node_ref
                .add_to_node_index(-(NAME_TO_FUNCTION_DIFF as i64))
                .maybe_function()
            {
                // Search for @enum.member
                if !search_decorated_for(
                    func.maybe_decorated(),
                    db.python_state.enum_member_node_ref(),
                ) {
                    continue;
                }
            }
            let name = name_node_ref.expect_name();
            let mut value_ref = name_node_ref;
            let point = name_node_ref.point();
            if let Some(assignment) = name.maybe_assignment_definition_name() {
                if let AssignmentContent::WithAnnotation(_, annotation, Some(_)) =
                    assignment.unpack()
                {
                    // TODO this check is wrong and should do name resolution correctly.
                    // However it is not that easy to do name resolution correctly, because the
                    // class is not ready to do name resolution. We probably have to move this
                    // check into EnumMemberDefinition calculation.
                    // Mypy allows this, so we should probably as well (and enum members are
                    // final anyway, so this is just redundance.
                    if annotation.expression().as_code() != "Final" {
                        NodeRef::new(self.node_ref.file, point.node_index())
                            .add_type_issue(db, IssueKind::EnumMemberAnnotationDisallowed);
                    }
                }
                match self.maybe_valid_enum_member_assignment(
                    db,
                    name_node_ref,
                    assignment,
                    &mut aliases,
                ) {
                    Some(ValidEnumMemberAssignment::Valid) => {}
                    Some(ValidEnumMemberAssignment::SubExpression(expr)) => {
                        value_ref = NodeRef::new(self.file, expr.index())
                    }
                    None => continue,
                }
            // Check if classes have an @nonmember
            } else if let Some(cls) = name_node_ref
                .add_to_node_index(-(NAME_TO_CLASS_DIFF as i64))
                .maybe_class()
                && search_decorated_for(
                    cls.maybe_decorated(),
                    db.python_state.enum_nonmember_node_ref(),
                )
            {
                continue;
            }

            debug_assert!(point.is_name_of_name_def_like(), "{point:?}");
            if point.node_index() != name_index {
                NodeRef::new(self.node_ref.file, point.node_index()).add_type_issue(
                    db,
                    IssueKind::EnumReusedMemberName {
                        enum_name: self.name().into(),
                        member_name: name_node_ref.as_code().into(),
                    },
                )
            }

            // TODO An enum member is never a descriptor. (that's how 3.10 does it). Here we
            // however only filter for functions and ignore decorators.
            members.push(EnumMemberDefinition::new(
                StringSlice::from_name(self.node_ref.file_index(), name).into(),
                Some(value_ref.as_link()),
            ))
        }
        (members.into_boxed_slice(), aliases.into_boxed_slice())
    }

    fn maybe_valid_enum_member_assignment(
        &self,
        db: &Database,
        name_node_ref: NodeRef,
        assignment: Assignment<'a>,
        aliases: &mut Vec<EnumMemberAlias>,
    ) -> Option<ValidEnumMemberAssignment<'a>> {
        if let Some(right) = assignment.right_side() {
            if let Some(expr) = right.maybe_simple_expression() {
                let cls = &Class::from_non_generic_node_ref(self.node_ref);
                let i_s = &InferenceState::from_class(db, cls);
                let name_resolution = self.file.name_resolution_for_types(i_s);
                match expr.unpack() {
                    ExpressionContent::Lambda(_) => return None,
                    ExpressionContent::ExpressionPart(ExpressionPart::Primary(primary)) => {
                        if let Some(non_member_ref) = db.python_state.enum_nonmember_node_ref() {
                            if let PrimaryContent::Execution(args) = primary.second()
                                && let Some(Lookup::T(TypeContent::Class { node_ref, .. })) =
                                    name_resolution
                                        .lookup_type_primary_or_atom_if_only_names(primary.first())
                            {
                                let node_ref = node_ref.into_node_ref();
                                if node_ref == non_member_ref {
                                    return None;
                                } else if Some(node_ref) == db.python_state.enum_member_node_ref() {
                                    if let Some(named_expr) = args.maybe_single_positional() {
                                        return Some(ValidEnumMemberAssignment::SubExpression(
                                            named_expr.expression(),
                                        ));
                                    }
                                } else if node_ref == db.python_state.classmethod_node_ref()
                                    || node_ref == db.python_state.staticmethod_node_ref()
                                {
                                    return None;
                                }
                            }
                        }
                    }
                    _ => (),
                }
                // Find aliases that link to other members
                if let Some(AtomContent::Name(n)) = expr.maybe_unpacked_atom()
                    && let PointResolution::NameDef {
                        node_ref: points_to,
                        ..
                    } = name_resolution.resolve_name_without_narrowing(n)
                    && points_to.file.file_index == self.file.file_index
                {
                    let class_node = self.node();
                    if points_to.node_index > class_node.index()
                        && points_to.node_index <= class_node.block().last_leaf_index()
                    {
                        let name = name_node_ref.expect_name();
                        aliases.push(EnumMemberAlias::new(
                            StringSlice::from_name(self.node_ref.file_index(), name).into(),
                            StringSlice::from_name(
                                self.node_ref.file_index(),
                                points_to.expect_name_def().name(),
                            )
                            .into(),
                        ));
                        return None;
                    }
                }
            }
            Some(ValidEnumMemberAssignment::Valid)
        } else {
            None
        }
    }

    fn named_tuple_from_class(&self, db: &Database) -> Arc<NamedTuple> {
        let name = self.name_string_slice();
        Arc::new(NamedTuple::new(
            name,
            self.initialize_named_tuple_class_members(db, name),
        ))
    }

    fn initialize_named_tuple_class_members(
        &self,
        db: &Database,
        name: StringSlice,
    ) -> CallableContent {
        let mut vec = start_namedtuple_params(db);
        let file = self.node_ref.file;
        let cls = Class::with_undefined_generics(self.node_ref);
        let i_s = &InferenceState::new(db, file).with_class_context(&cls);
        find_stmt_named_tuple_types(i_s, file, &mut vec, self.node().block().iter_stmt_likes());
        for (name, index) in self.class_storage.class_symbol_table.iter() {
            if NAMEDTUPLE_PROHIBITED_NAMES.contains(&name) {
                NodeRef::new(self.node_ref.file, *index).add_type_issue(
                    db,
                    IssueKind::NamedTupleInvalidAttributeOverride { name: name.into() },
                )
            }
        }
        CallableContent::new_simple(
            Some(DbString::StringSlice(name)),
            None,
            self.node_ref.as_link(),
            self.use_cached_type_vars(db).clone(),
            CallableParams::new_simple(Arc::from(vec)),
            Type::Self_,
        )
    }

    fn gather_protocol_members(&self) -> Box<[ProtocolMember]> {
        let mut protocol_members = vec![];
        for (name, &name_index) in self.class_storage.class_symbol_table.iter() {
            if EXCLUDED_PROTOCOL_ATTRIBUTES.contains(&name) {
                continue;
            }
            let file = self.node_ref.file;
            let name_node_ref = NodeRef::new(file, name_index);
            // is_abstract is not properly inferred here. This is basically only heuristics,
            // because that's probably good enough for now.
            let mut is_abstract = !file.is_stub()
                && self
                    .class_storage
                    .self_symbol_table
                    .lookup_symbol(name)
                    .is_none();
            let variance = match name_node_ref.expect_name().expect_type() {
                TypeLike::ImportFromAsName(_) | TypeLike::DottedAsName(_) => continue,
                TypeLike::Function(func) => {
                    let p = name_node_ref.point();
                    debug_assert!(p.is_name_of_name_def_like(), "{p:?}");
                    if p.node_index() == name_index {
                        is_abstract &= match func.trivial_body_state() {
                            TrivialBodyState::Known(k) => k,
                            TrivialBodyState::RaiseExpr(expression) => {
                                // TODO this is currently a heuristic to avoid using inference
                                // in Function::has_trivial_body()
                                let code = expression.as_code();
                                ["NotImplementedError", "NotImplementedError()"].contains(&code)
                            }
                        };
                    } else {
                        let mut has_overload = false;
                        let mut has_non_overload = false;
                        for index in OtherDefinitionIterator::new(&file.points, name_index) {
                            let n = NodeRef::new(self.node_ref.file, index);
                            if let Some(func) = n.maybe_name_of_function() {
                                let mut found_overload = false;
                                if let Some(func) = func.maybe_decorated() {
                                    for decorator in func.decorators().iter() {
                                        if matches!(
                                            decorator.named_expression().expression().as_code(),
                                            "overload" | "typing.overload"
                                        ) {
                                            found_overload = true;
                                        }
                                    }
                                }
                                if found_overload {
                                    has_overload = true;
                                } else {
                                    has_non_overload = true;
                                }
                            }
                        }
                        // While this is just a heuristic, I'm pretty sure that this is good enough
                        // for almost all cases, because people would need to do some weird
                        // aliasing for this to break. Additionally not a lot of people are even
                        // inheriting from protocols (except the stdlib ones that don't use
                        // overload implementations AFAIK and would use @overload anyway).
                        is_abstract &= !(has_overload && has_non_overload);
                    }
                    Variance::Covariant
                }
                TypeLike::Assignment(assignment) => {
                    is_abstract &= !matches!(
                        assignment.unpack(),
                        AssignmentContent::Normal(..)
                            | AssignmentContent::WithAnnotation(_, _, Some(_)),
                    );
                    Variance::Invariant
                }
                TypeLike::ClassDef(_) => Variance::Covariant,
                _ => Variance::Invariant,
            };
            protocol_members.push(ProtocolMember {
                name_index,
                variance,
                is_abstract,
            })
        }
        protocol_members.sort_by_key(|member| member.name_index);
        protocol_members.into()
    }

    fn calculate_abstract_attributes(
        &self,
        db: &Database,
        metaclass: &MetaclassState,
        class_kind: &ClassKind,
        mro: &[BaseClass],
    ) -> Box<[PointLink]> {
        let mut result = vec![];
        for &n in self.class_storage.abstract_attributes.iter() {
            result.push(PointLink::new(self.node_ref.file_index(), n))
        }
        let mut maybe_add = |link, name, mro_index| {
            if self
                .class_storage
                .class_symbol_table
                .lookup_symbol(name)
                .is_none()
                && !result
                    .iter()
                    .any(|&l| NodeRef::from_link(db, l).as_code() == name)
            {
                for base in &mro[..mro_index] {
                    if let Type::Class(c) = &base.type_ {
                        let class = c.class(db);
                        if class
                            .class_storage
                            .class_symbol_table
                            .lookup_symbol(name)
                            .is_some()
                        {
                            return;
                        }
                    }
                }
                result.push(link)
            }
        };
        for (i, base) in mro.iter().enumerate() {
            if let Type::Class(c) = &base.type_ {
                let class = c.class(db);
                let class_infos = class.use_cached_class_infos(db);
                if base.is_direct_base {
                    for &link in class_infos.abstract_attributes.iter() {
                        let name = NodeRef::from_link(db, link).as_code();
                        maybe_add(link, name, i)
                    }
                    if !matches!(class_kind, ClassKind::Protocol) {
                        for protocol_member in class_infos.protocol_members.iter() {
                            if !protocol_member.is_abstract {
                                continue;
                            }
                            let link = PointLink::new(c.link.file, protocol_member.name_index);
                            let name = class
                                .node_ref
                                .file
                                .tree
                                .code_of_index(protocol_member.name_index);
                            if self
                                .class_storage
                                .self_symbol_table
                                .lookup_symbol(name)
                                .is_none()
                            {
                                maybe_add(link, name, i);
                            }
                        }
                    }
                }
            }
        }
        // Mypy sorts these alphanumerically
        result.sort_by_key(|&l| NodeRef::from_link(db, l).as_code());
        if self.class_storage.abstract_attributes.is_empty()
            && !result.is_empty()
            && self.node_ref.file.is_stub()
        {
            let has_abc_meta_metaclass = || match metaclass {
                MetaclassState::Some(link) => ClassInitializer::from_link(db, *link)
                    .class_link_in_mro(db, db.python_state.abc_meta_link()),
                _ => false,
            };
            if !has_abc_meta_metaclass() {
                self.add_issue_on_name(
                    db,
                    IssueKind::ClassNeedsAbcMeta {
                        class_name: self.qualified_name(db).into(),
                        attributes: join_abstract_attributes(db, &result),
                    },
                )
            }
        }
        result.into()
    }
}

fn initialize_typed_dict_members(db: &Database, cls: &Class, td_infos: DeferredTypedDictMembers) {
    let typed_dict_definition = cls.maybe_typed_dict_definition().unwrap();
    let mut typed_dict_members = TypedDictMemberGatherer::default();
    let mut extra_items = None;
    let args = cls.node().arguments();
    if let Some(args) = args {
        for (i, base) in cls
            .use_cached_class_infos(db)
            .mro
            .iter()
            .rev()
            .filter(|t| t.is_direct_base)
            .enumerate()
        {
            if let Type::TypedDict(td) = &base.type_ {
                let node_ref = NodeRef::new(cls.node_ref.file, args.iter().nth(i).unwrap().index());
                if !td.has_calculated_members(db) {
                    let super_cls = ClassInitializer::from_link(db, td.defined_at);
                    let tdd = super_cls.maybe_typed_dict_definition().unwrap();
                    tdd.deferred_subclass_member_initializations
                        .write()
                        .unwrap()
                        .push(td_infos.clone());
                    debug!(
                        "Defer typed dict member initialization for {:?} after {:?}",
                        cls.name(),
                        super_cls.name(),
                    );
                    return;
                };
                let m = td.members(db);
                if m.extra_items.is_some() {
                    extra_items = m.extra_items.clone()
                }
                typed_dict_members.merge(db, node_ref, &m.named);
            }
        }
    }
    debug!("Start TypedDict members calculation for {:?}", cls.name());
    let file = cls.node_ref.file;
    let i_s = &InferenceState::new(db, file).with_class_context(cls);
    find_stmt_typed_dict_types(
        i_s,
        file,
        &mut typed_dict_members,
        cls.node().block().iter_stmt_likes(),
        &typed_dict_definition.initialization_args,
        extra_items.as_ref(),
    );
    let initialization_args = &td_infos.1;
    let add = |issue| NodeRef::new(file, args.unwrap().index()).add_type_issue(db, issue);
    if let Some(old) = &extra_items {
        match initialization_args.closed {
            Some(true) if !old.read_only && !old.t.is_never() => {
                add(IssueKind::TypedDictCannotUseCloseIfSuperClassExtraItemsNonReadOnly)
            }
            Some(false) if old.t.is_never() => {
                add(IssueKind::TypedDictCannotUseCloseFalseIfSuperClassClosed)
            }
            Some(false) => add(IssueKind::TypedDictCannotUseCloseFalseIfSuperClassHasExtraItems),
            _ => (),
        }
    }
    if let Some(new) = file
        .name_resolution_for_types(i_s)
        .compute_class_typed_dict_extra_items(initialization_args)
    {
        if let Some(old) = &extra_items {
            // Closed was already handled above
            if !initialization_args.closed.is_some() {
                if old.read_only {
                    if !old.t.is_simple_super_type_of(i_s, &new.t).bool() {
                        add(IssueKind::TypedDictExtraItemsNonReadOnlyChangeDisallowed);
                    }
                } else {
                    add(IssueKind::TypedDictExtraItemsNonReadOnlyChangeDisallowed);
                }
            }
        }
        extra_items = Some(new)
    }

    debug!("End TypedDict members calculation for {:?}", cls.name());
    td_infos.0.late_initialization_of_members(TypedDictMembers {
        named: typed_dict_members.into_boxed_slice(),
        extra_items,
    });
    loop {
        let mut borrowed = typed_dict_definition
            .deferred_subclass_member_initializations
            .write()
            .unwrap();
        let Some(deferred) = borrowed.pop() else {
            break;
        };
        drop(borrowed);
        // TODO is this initialization correct?
        let cls = Class::from_undefined_generics(db, deferred.0.defined_at);
        debug!(
            "Calculate TypedDict members for deferred subclass {:?}",
            cls.name()
        );
        initialize_typed_dict_members(db, &cls, deferred)
    }
}

fn find_stmt_typed_dict_types(
    i_s: &InferenceState,
    file: &PythonFile,
    vec: &mut TypedDictMemberGatherer,
    stmt_likes: StmtLikeIterator,
    initialization_args: &TypedDictArgs,
    extra_items: Option<&ExtraItemsType>,
) {
    let db = i_s.db;
    for stmt_like in stmt_likes {
        match stmt_like.node {
            StmtLikeContent::Assignment(assignment) => match assignment.unpack() {
                AssignmentContent::WithAnnotation(Target::Name(name_def), annot, right_side) => {
                    if right_side.is_some() {
                        NodeRef::new(file, assignment.index())
                            .add_type_issue(db, IssueKind::TypedDictInvalidMemberRightSide);
                    }
                    if let Err(issue) = vec.add(
                        i_s,
                        file.name_resolution_for_types(i_s)
                            .compute_class_typed_dict_member(
                                initialization_args,
                                StringSlice::from_name(file.file_index, name_def.name()),
                                annot,
                            ),
                        extra_items,
                    ) {
                        NodeRef::new(file, assignment.index()).add_type_issue(db, issue);
                    }
                }
                AssignmentContent::Normal(targets, _) => {
                    NodeRef::new(file, assignment.index())
                        .add_type_issue(db, IssueKind::TypedDictInvalidMember);
                    for target in targets {
                        if let Target::Name(name_def) = target {
                            // Add those names regardless, because an error was already added.
                            vec.add(
                                i_s,
                                TypedDictMember {
                                    type_: Type::Any(AnyCause::Todo),
                                    required: true,
                                    name: StringSlice::from_name(file.file_index, name_def.name()),
                                    read_only: false,
                                },
                                extra_items,
                            )
                            .ok();
                        }
                    }
                }
                _ => NodeRef::new(file, assignment.index())
                    .add_type_issue(db, IssueKind::TypedDictInvalidMember),
            },
            StmtLikeContent::Error(_)
            | StmtLikeContent::PassStmt(_)
            | StmtLikeContent::StarExpressions(_) => (),
            _ => NodeRef::new(file, stmt_like.parent_index)
                .add_type_issue(db, IssueKind::TypedDictInvalidMember),
        }
    }
}

fn find_stmt_named_tuple_types(
    i_s: &InferenceState,
    file: &PythonFile,
    vec: &mut Vec<CallableParam>,
    stmts: StmtLikeIterator,
) {
    let db = i_s.db;
    for stmt_like in stmts {
        match stmt_like.node {
            StmtLikeContent::Assignment(assignment) => match assignment.unpack() {
                AssignmentContent::WithAnnotation(Target::Name(name), annot, default) => {
                    if default.is_none() && vec.last().is_some_and(|last| last.has_default) {
                        NodeRef::new(file, assignment.index())
                            .add_type_issue(db, IssueKind::NamedTupleNonDefaultFieldFollowsDefault);
                        continue;
                    }
                    file.name_resolution_for_types(i_s)
                        .ensure_cached_named_tuple_annotation(annot);
                    let t = use_cached_annotation_type(db, file, annot).into_owned();
                    if name.as_code().starts_with('_') {
                        NodeRef::new(file, name.index()).add_type_issue(
                            db,
                            IssueKind::NamedTupleNameCannotStartWithUnderscore {
                                field_name: name.as_code().into(),
                            },
                        )
                    } else {
                        vec.push(CallableParam {
                            type_: ParamType::PositionalOrKeyword(t),
                            has_default: default.is_some(),
                            name: Some(StringSlice::from_name(file.file_index, name.name()).into()),
                            might_have_type_vars: true,
                        })
                    }
                }
                _ => {
                    // Mypy disallows this, but the conformance tests do not.
                    if db.mypy_compatible() {
                        NodeRef::new(file, assignment.index())
                            .add_type_issue(db, IssueKind::InvalidStmtInNamedTuple)
                    }
                }
            },
            StmtLikeContent::AsyncStmt(async_stmt)
                if matches!(async_stmt.unpack(), AsyncStmtContent::FunctionDef(_)) => {}
            StmtLikeContent::Decorated(dec)
                if matches!(
                    dec.decoratee(),
                    Decoratee::FunctionDef(_) | Decoratee::AsyncFunctionDef(_)
                ) => {}
            StmtLikeContent::FunctionDef(_)
            | StmtLikeContent::PassStmt(_)
            | StmtLikeContent::StarExpressions(_) => (),
            _ => NodeRef::new(file, stmt_like.parent_index)
                .add_type_issue(db, IssueKind::InvalidStmtInNamedTuple),
        }
    }
}

#[derive(Clone)]
struct BaseToBeAdded<'a> {
    t: Cow<'a, Type>,
    needs_remapping: bool,
}

#[derive(Debug, PartialEq)]
enum BaseKind {
    Class(PointLink),
    Dataclass(PointLink),
    NamedTuple(Arc<NamedTuple>),
    TypedDict(Arc<TypedDict>),
    Tuple(Arc<Tuple>),
    Type,
    Enum,
}

fn to_base_kind(t: &Type) -> BaseKind {
    match t {
        Type::Class(c) => BaseKind::Class(c.link),
        Type::Type(_) => BaseKind::Type,
        Type::Tuple(tup) => BaseKind::Tuple(tup.clone()),
        Type::Dataclass(d) => BaseKind::Dataclass(d.class.link),
        Type::TypedDict(d) => BaseKind::TypedDict(d.clone()),
        Type::NamedTuple(nt) => BaseKind::NamedTuple(nt.clone()),
        Type::Enum(_) => BaseKind::Enum,
        Type::NewType(n) => to_base_kind(&n.type_),
        _ => unreachable!("{t:?}"),
    }
}

pub fn linearize_mro_and_return_linearizable(
    db: &Database,
    bases: &[Type],
) -> (Box<[BaseClass]>, bool) {
    let mut mro: Vec<BaseClass> = vec![];

    let object = db.python_state.object_type();
    let mut linearizable = true;
    if let Some(index) = bases.iter().position(|base| base == &object) {
        // Instead of adding object to each iterator (because in our mro, object is not saved), we
        // just check for object in bases here. If it's not in the last position it's wrong.
        if index != bases.len() - 1 {
            debug!("Non-linearizable, because object is not in the last position");
            linearizable = false;
        }
    }
    let to_base_class = |base_index: usize,
                         is_direct_base,
                         new_base: &BaseToBeAdded,
                         allowed_to_use: &mut usize| {
        BaseClass {
            type_: if new_base.needs_remapping {
                new_base
                    .t
                    .replace_type_var_likes(db, &mut |usage| {
                        Some(match &bases[base_index] {
                            Type::Tuple(tup) => tup
                                .class(db)
                                .generics
                                .nth_usage(db, &usage)
                                .into_generic_item(),
                            Type::NamedTuple(n) => n
                                .as_tuple_ref()
                                .class(db)
                                .generics
                                .nth_usage(db, &usage)
                                .into_generic_item(),
                            Type::Class(GenericClass {
                                generics: ClassGenerics::List(generics),
                                ..
                            }) => generics[usage.index()].clone(),
                            // Very rare and therefore a separate case.
                            Type::Class(c) => c
                                .class(db)
                                .generics
                                .nth_usage(db, &usage)
                                .into_generic_item(),
                            Type::Dataclass(d) => match &d.class.generics {
                                ClassGenerics::List(generics) => generics[usage.index()].clone(),
                                _ => d
                                    .class(db)
                                    .generics
                                    .nth_usage(db, &usage)
                                    .into_generic_item(),
                            },
                            // If we expect class generics and tuples are involved, the tuple was already
                            // calculated.
                            _ => unreachable!(),
                        })
                    })
                    .unwrap_or_else(|| new_base.t.as_ref().clone())
            } else {
                *allowed_to_use += 1;
                new_base.t.as_ref().clone()
            },
            is_direct_base,
        }
    };

    let mut base_iterators: Vec<_> = bases
        .iter()
        .map(|t| {
            let mut additional_type = None;
            let generic_class = match &t {
                Type::Class(c) => Some(c.class(db)),
                Type::Dataclass(d) => Some(d.class.class(db)),
                Type::Tuple(tup) => {
                    let cls = tup.class(db);
                    additional_type = Some(cls.as_type(db));
                    Some(cls)
                }
                Type::NamedTuple(nt) => {
                    let cls = nt.as_tuple_ref().class(db);
                    additional_type = Some(cls.as_type(db));
                    Some(cls)
                }
                _ => None,
            };
            let super_classes = if let Some(cls) = generic_class {
                let cached_class_infos = cls.use_cached_class_infos(db);
                cached_class_infos.mro.as_ref()
            } else {
                &[]
            };
            std::iter::once(BaseToBeAdded {
                t: Cow::Borrowed(t),
                needs_remapping: false,
            })
            .chain(additional_type.into_iter().map(|t| BaseToBeAdded {
                t: Cow::Owned(t),
                needs_remapping: false,
            }))
            .chain(super_classes.iter().map(|base| BaseToBeAdded {
                t: Cow::Borrowed(&base.type_),
                needs_remapping: true,
            }))
            .enumerate()
            .peekable()
        })
        .collect();
    // Signals how many of the base_iterators we can use.
    let mut allowed_to_use = 1;
    'outer: loop {
        let mut had_entry = false;
        for base_index in 0..allowed_to_use.min(bases.len()) {
            if let Some((i, candidate)) = base_iterators[base_index].peek().cloned() {
                had_entry = true;
                let conflicts = base_iterators.iter().any(|base_bases| {
                    base_bases
                        .clone()
                        .skip(1)
                        .any(|(_, other)| to_base_kind(&candidate.t) == to_base_kind(&other.t))
                });
                if !conflicts {
                    let is_non_object = candidate.t.as_ref() != &object;
                    for (skip_index, base_bases) in base_iterators.iter_mut().enumerate() {
                        base_bases.next_if(|(other_index, next)| {
                            if *other_index == 0 {
                                allowed_to_use += 1;
                            }
                            let skip = to_base_kind(&candidate.t) == to_base_kind(&next.t);
                            if skip && skip_index != base_index && is_non_object {
                                let new = to_base_class(base_index, false, &candidate, &mut 0);
                                let other = to_base_class(skip_index, false, next, &mut 0);
                                if !new
                                    .type_
                                    .is_equal_type_where_any_matches_all(db, &other.type_)
                                {
                                    debug!(
                                        "Non-linearizable, because the type is similar, \
                                            but not equal: {} != {}",
                                        new.type_.format_short(db),
                                        other.type_.format_short(db),
                                    );
                                    linearizable = false
                                }
                            }
                            skip
                        });
                    }
                    if is_non_object {
                        let new =
                            to_base_class(base_index, i == 0, &candidate, &mut allowed_to_use);
                        mro.push(new);
                    };
                    continue 'outer;
                }
            }
        }
        if !had_entry {
            break;
        }
        for (base_index, base_bases) in base_iterators.iter_mut().enumerate() {
            if let Some((i, type_)) = base_bases.next() {
                debug!(
                    "Non-linearizable, because not fetched, {} ({base_index}->{i})",
                    type_.t.format_short(db)
                );
                linearizable = false;
                // Here we know that we have issues and only add the type if it's not already
                // there.
                if mro.iter().any(|b| &b.type_ == type_.t.as_ref()) {
                    if type_.t.as_ref() != &object {
                        let new = to_base_class(base_index, i == 0, &type_, &mut allowed_to_use);
                        mro.push(new);
                    };
                }
                continue 'outer;
            }
        }
        unreachable!()
    }
    (mro.into_boxed_slice(), linearizable)
}

fn join_abstract_attributes(db: &Database, abstract_attributes: &[PointLink]) -> Box<str> {
    join_with_commas(
        abstract_attributes
            .iter()
            .map(|&l| format!("\"{}\"", NodeRef::from_link(db, l).as_code())),
    )
    .into()
}

fn check_dataclass_options(
    db: &Database,
    file: &PythonFile,
    details: ArgumentsDetails,
    default_options: DataclassOptions,
) -> DataclassOptions {
    let mut options = default_options;
    for arg in details.iter() {
        if let ArgOrComprehension::Arg(Argument::Keyword(kw)) = arg {
            options.assign_keyword_arg_to_dataclass_options(db, file, kw);
        } else {
            NodeRef::new(file, details.index().unwrap())
                .add_type_issue(db, IssueKind::UnexpectedArgumentTo { name: "dataclass" })
        }
    }
    if !options.eq && options.order {
        options.eq = true;
        NodeRef::new(file, details.index().unwrap())
            .add_type_issue(db, IssueKind::DataclassOrderEnabledButNotEq);
    }
    options
}

impl DataclassOptions {
    fn assign_keyword_arg_to_dataclass_options(
        &mut self,
        db: &Database,
        file: &PythonFile,
        kwarg: Kwarg,
    ) {
        let (key, expr) = kwarg.unpack();
        let key = key.as_code();
        let assign_option = |target: &mut _| {
            if let Some(bool_) = expr.maybe_simple_bool() {
                *target = bool_;
            } else {
                NodeRef::new(file, expr.index())
                    .add_type_issue(db, IssueKind::ArgumentMustBeTrueOrFalse { key: key.into() })
            }
        };
        match key {
            "kw_only" => assign_option(&mut self.kw_only),
            "frozen" => {
                let mut new_frozen = false;
                assign_option(&mut new_frozen);
                self.frozen = Some(new_frozen);
            }
            "order" => assign_option(&mut self.order),
            "eq" => assign_option(&mut self.eq),
            "init" => assign_option(&mut self.init),
            "match_args" => assign_option(&mut self.match_args),
            "slots" => assign_option(&mut self.slots),
            "unsafe_hash" => assign_option(&mut self.unsafe_hash),
            // The other names should not go through while type checking
            _ => (),
        }
    }
}

fn maybe_dataclass_transform_func(
    db: &Database,
    func: FuncNodeRef,
) -> Option<DataclassTransformObj> {
    let decorated = func.node().maybe_decorated()?;
    {
        let func_point = func.point();
        if func_point.calculating() {
            return None;
        } else if !func_point.calculated() {
            func.set_point(Point::new_calculating())
        }
    }
    Function::new_with_unknown_parent(db, *func)
        .ensure_cached_func(&InferenceState::new(db, func.file));
    debug_assert!(func.point().calculated());
    if let Some(ComplexPoint::FunctionOverload(overload)) = func.maybe_complex() {
        overload.dataclass_transform.clone()
    } else {
        for decorator in decorated.decorators().iter() {
            let expr = decorator.named_expression().expression();
            if let ExpressionContent::ExpressionPart(ExpressionPart::Primary(primary)) =
                expr.unpack()
            {
                let primary_node_ref = NodeRef::new(func.file, primary.index());
                if primary_node_ref.point().calculated() {
                    if let Some(ComplexPoint::TypeInstance(Type::DataclassTransformObj(dto))) =
                        primary_node_ref.maybe_complex()
                    {
                        return Some(dto.clone());
                    }
                } else if let PrimaryContent::Execution(exec) = primary.second() {
                    let i_s = &InferenceState::new(db, func.file);
                    let name_resolution = func.file.name_resolution_for_types(i_s);
                    if let Some(Lookup::T(TypeContent::SpecialCase(
                        Specific::TypingDataclassTransform,
                    ))) =
                        name_resolution.lookup_type_primary_or_atom_if_only_names(primary.first())
                    {
                        return Some(
                            name_resolution
                                .insert_dataclass_transform(primary, exec)
                                .clone(),
                        );
                    }
                }
            }
        }
        None
    }
}

impl<'db, 'file> NameResolution<'db, 'file, '_> {
    pub(crate) fn insert_dataclass_transform(
        &self,
        primary: Primary,
        details: ArgumentsDetails,
    ) -> &'file DataclassTransformObj {
        // Checks dataclass_transform(...)
        let mut d = DataclassTransformObj::default();
        for arg in details.iter() {
            if let ArgOrComprehension::Arg(Argument::Keyword(kw)) = arg {
                let (key, value) = kw.unpack();
                let key = key.as_code();
                let assign_option = |target: &mut _| {
                    if let Some(bool_) = value.maybe_simple_bool() {
                        *target = bool_;
                    } else {
                        self.add_issue(
                            value.index(),
                            IssueKind::ArgumentMustBeTrueOrFalse { key: key.into() },
                        );
                    }
                };
                match key {
                    "eq_default" => assign_option(&mut d.eq_default),
                    "order_default" => assign_option(&mut d.order_default),
                    "kw_only_default" => assign_option(&mut d.kw_only_default),
                    "frozen_default" => assign_option(&mut d.frozen_default),
                    "field_specifiers" => self
                        .fill_dataclass_transform_field_specifiers(value, &mut d.field_specifiers),
                    _ => self.add_issue(
                        arg.index(),
                        IssueKind::DataclassTransformUnknownParam { name: key.into() },
                    ),
                }
            } else {
                self.add_type_issue(
                    arg.index(),
                    IssueKind::UnexpectedArgumentTo {
                        name: "dataclass_transform",
                    },
                )
            }
        }
        let node_ref = NodeRef::new(self.file, primary.index());
        node_ref.insert_type(Type::DataclassTransformObj(d.clone()));
        let Type::DataclassTransformObj(d) = node_ref.maybe_type().unwrap() else {
            unreachable!()
        };
        d
    }

    fn fill_dataclass_transform_field_specifiers(
        &self,
        value: Expression,
        field_specifiers: &mut Arc<[PointLink]>,
    ) {
        let check = || -> Result<Arc<[_]>, IssueKind> {
            if let Some(tuple) = value.maybe_tuple() {
                return tuple
                    .iter()
                    .map(|s| {
                        if let StarLikeExpression::NamedExpression(ne) = s {
                            match self.lookup_type_expr_if_only_names(ne.expression()) {
                                Some(Lookup::T(TypeContent::InvalidVariable(
                                    InvalidVariableType::Function { node_ref },
                                ))) => return Ok(node_ref.as_link()),
                                Some(Lookup::T(TypeContent::Class { node_ref, .. })) => {
                                    return Ok(node_ref.as_link());
                                }
                                _ => (),
                            }
                        }
                        Err(IssueKind::DataclassTransformFieldSpecifiersMustOnlyContainIdentifiers)
                    })
                    .collect();
            }
            Err(IssueKind::DataclassTransformFieldSpecifiersMustBeTuple)
        };
        match check() {
            Ok(new_specifiers) => *field_specifiers = new_specifiers,
            Err(issue) => self.add_type_issue(value.index(), issue),
        }
    }
}

enum ValidEnumMemberAssignment<'db> {
    SubExpression(Expression<'db>),
    Valid,
}
