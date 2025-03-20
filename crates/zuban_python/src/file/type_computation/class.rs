use std::{borrow::Cow, cell::OnceCell, rc::Rc};

use parsa_python_cst::{
    Argument, Arguments as CSTArguments, ArgumentsDetails, AssignmentContent, AsyncStmtContent,
    ClassDef, Decoratee, ExpressionContent, ExpressionPart, NodeIndex, PrimaryContent,
    StmtLikeContent, StmtLikeIterator, Target, TypeLike,
};

use crate::{
    arguments::{Arg, Args, KnownArgs, SimpleArgs},
    database::{
        BaseClass, ClassInfos, ClassKind, ClassStorage, ComplexPoint, Database, Locality,
        MetaclassState, ParentScope, Point, PointLink, ProtocolMember, Specific,
        TypedDictDefinition,
    },
    debug,
    diagnostics::{Issue, IssueKind},
    file::{
        type_computation::typed_dict::TypedDictMemberGatherer, use_cached_annotation_type,
        CalculatedBaseClass, OtherDefinitionIterator, PythonFile, TypeComputation,
        TypeComputationOrigin, TypeVarCallbackReturn, TypeVarFinder,
    },
    inference_state::InferenceState,
    inferred::Inferred,
    matching::ResultContext,
    node_ref::NodeRef,
    python_state::{NAME_TO_CLASS_DIFF, NAME_TO_FUNCTION_DIFF},
    type_::{
        dataclass_init_func, AnyCause, CallableContent, CallableParam, CallableParams,
        ClassGenerics, Dataclass, DataclassOptions, DataclassTransformObj, DbString, Enum,
        EnumMemberDefinition, FunctionKind, GenericClass, NamedTuple, ParamType, StringSlice,
        Tuple, Type, TypeVarLike, TypeVarLikes, TypedDict, TypedDictMember, Variance,
    },
    type_helpers::{Class, FirstParamProperties, Function, TypeOrClass},
    utils::{debug_indent, join_with_commas},
};

use super::{named_tuple::start_namedtuple_params, typed_dict::check_typed_dict_total_argument};

// Basically save the type vars on the class keyword.
const CLASS_TO_TYPE_VARS_DIFFERENCE: i64 = 1;
// Basically the `(` or `:` after the name
pub(crate) const CLASS_TO_CLASS_INFO_DIFFERENCE: i64 = NAME_TO_CLASS_DIFF as i64 + 1;

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
pub struct ClassNodeRef<'file>(NodeRef<'file>);

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

    #[inline]
    pub fn to_db_lifetime(self, db: &Database) -> ClassNodeRef {
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
    fn class_info_node_ref(&self) -> NodeRef {
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
        match node_ref.to_db_lifetime(db).complex().unwrap() {
            ComplexPoint::ClassInfos(class_infos) => Some(class_infos),
            _ => unreachable!(),
        }
    }

    fn add_issue_on_name(&self, db: &Database, kind: IssueKind) {
        let issue = Issue::from_node_index(&self.file.tree, self.node_index, kind);
        self.file.add_type_issue(db, issue)
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

        let type_vars = TypeVarFinder::find_class_type_vars(i_s, self);
        if type_vars.is_empty() {
            node_ref.set_point(Point::new_specific(Specific::Analyzed, Locality::Todo));
        } else {
            node_ref.insert_complex(ComplexPoint::TypeVarLikes(type_vars), Locality::Todo);
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
            .complex()
            .and_then(|c| match c {
                ComplexPoint::TypedDictDefinition(tdd) => Some(tdd),
                _ => None,
            })
    }

    pub fn class_storage(&self) -> &'file ClassStorage {
        let complex = self.complex().unwrap_or_else(|| {
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
pub struct ClassInitializer<'a> {
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
                    .find_type_var_like_including_ancestors(db, type_var, true)
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
            .find(type_var_like.clone(), self.node_ref.as_link())
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
                if let Type::Class(c) = &b.type_ {
                    if c.class(db)
                        .class_storage
                        .class_symbol_table
                        .lookup_symbol(n)
                        .is_some()
                    {
                        return true;
                    }
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
            self.node_ref.file_index(),
            self.class_storage.parent_scope,
            |i_s| {
                debug!("Calculate class infos for {}", self.name());
                debug_indent(|| self.insert_class_infos(&i_s))
            },
        )
    }

    fn insert_class_infos(&self, i_s: &InferenceState) {
        let node_ref = self.node_ref.class_info_node_ref();
        debug_assert!(NodeRef::new(node_ref.file, self.node().name_def().index())
            .point()
            .calculated());

        node_ref.set_point(Point::new_calculating());
        let db = i_s.db;

        let type_vars = self.type_vars(i_s);

        let mut was_dataclass = None;
        let maybe_decorated = self.node().maybe_decorated();
        let mut is_final = false;
        let mut total_ordering = false;
        let mut is_runtime_checkable = false;
        let mut dataclass_transform = None;
        if let Some(decorated) = maybe_decorated {
            let inference = self.node_ref.file.inference(i_s);

            let mut dataclass_options = None;
            for decorator in decorated.decorators().iter() {
                let expr = decorator.named_expression().expression();
                if let ExpressionContent::ExpressionPart(ExpressionPart::Primary(primary)) =
                    expr.unpack()
                {
                    if let PrimaryContent::Execution(exec) = primary.second() {
                        let inf = inference.infer_primary_or_atom(primary.first());
                        if inf.is_name_defined_in_module(db, "dataclasses", "dataclass") {
                            dataclass_options = Some(check_dataclass_options(
                                i_s,
                                self.node_ref.file,
                                primary.index(),
                                exec,
                                DataclassOptions::default(),
                            ));
                            continue;
                        }
                        if let Some(ComplexPoint::TypeInstance(Type::DataclassTransformObj(d))) =
                            inf.maybe_complex_point(db)
                        {
                            dataclass_options = Some(check_dataclass_options(
                                i_s,
                                self.node_ref.file,
                                primary.index(),
                                exec,
                                d.as_dataclass_options(),
                            ));
                            continue;
                        }
                    }
                }
                let inf = inference.infer_decorator(decorator);
                if let Some(maybe_link) = inf.maybe_saved_link() {
                    if maybe_link == db.python_state.typing_final().as_link() {
                        is_final = true;
                    } else if maybe_link == db.python_state.total_ordering_link() {
                        total_ordering = true;
                    } else if maybe_link == db.python_state.runtime_checkable_link()
                        || maybe_link == db.python_state.typing_extensions_runtime_checkable_link()
                    {
                        is_runtime_checkable = true;
                    }
                }

                if inf.is_name_defined_in_module(db, "dataclasses", "dataclass") {
                    dataclass_options = Some(DataclassOptions::default());
                }
                if let Some(ComplexPoint::TypeInstance(Type::DataclassTransformObj(d))) =
                    inf.maybe_complex_point(db)
                {
                    if d.executed_by_function {
                        dataclass_options = Some(d.as_dataclass_options());
                    } else {
                        dataclass_transform = Some(Box::new(d.clone()));
                    }
                }
            }
            if let Some(dataclass_options) = dataclass_options {
                let dataclass = Dataclass::new_uninitialized(
                    self.node_ref.as_link(),
                    type_vars,
                    dataclass_options,
                );
                let class = dataclass.class(db);
                if dataclass.options.slots && class.lookup_symbol(i_s, "__slots__").is_some() {
                    class.add_issue_on_name(
                        db,
                        IssueKind::DataclassPlusExplicitSlots {
                            class_name: class.name().into(),
                        },
                    )
                }
                was_dataclass = Some(dataclass);
            }
        }

        let (mut class_infos, typed_dict_total) = self.calculate_class_infos(i_s, type_vars);
        if let Some(dataclass) = &was_dataclass {
            // It is possible that there was a dataclass_transform in the metaclass
            let _ = class_infos
                .undefined_generics_type
                .set(Rc::new(Type::Dataclass(dataclass.clone())));
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

        if class_infos.class_kind == ClassKind::Protocol {
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

        let mut was_enum = None;
        let mut was_enum_base = false;
        if let MetaclassState::Some(link) = class_infos.metaclass {
            if link == db.python_state.enum_meta_link() {
                was_enum_base = true;
                if !self.use_cached_type_vars(db).is_empty() {
                    self.add_issue_on_name(db, IssueKind::EnumCannotBeGeneric);
                }
                class_infos.class_kind = ClassKind::Enum;
                let members = self.enum_members(db);
                if !members.is_empty() {
                    let enum_ = Enum::new(
                        DbString::StringSlice(self.name_string_slice()),
                        self.node_ref.as_link(),
                        self.node_ref.as_link(),
                        self.class_storage.parent_scope,
                        members,
                        OnceCell::new(),
                    );
                    was_enum = Some(enum_);
                }
            }
        }
        if let Some(enum_) = &was_enum {
            let enum_type = Rc::new(Type::Enum(enum_.clone()));
            // In case enum is combined with dataclass, just let the dataclass win
            let _ = class_infos.undefined_generics_type.set(enum_type.clone());
        }
        let mut was_typed_dict = None;
        if let Some(total) = typed_dict_total {
            let td = TypedDict::new_class_definition(
                self.name_string_slice(),
                self.node_ref.as_link(),
                type_vars.clone(),
                is_final,
            );
            // In case TypedDict is combined with dataclass, just let the dataclass win
            let _ = class_infos
                .undefined_generics_type
                .set(Rc::new(Type::TypedDict(td.clone())));
            NodeRef::new(self.node_ref.file, self.node().name_def().index()).insert_complex(
                ComplexPoint::TypedDictDefinition(TypedDictDefinition::new(td.clone(), total)),
                Locality::ImplicitExtern,
            );
            was_typed_dict = Some(td);
        }

        node_ref.insert_complex(ComplexPoint::ClassInfos(class_infos), Locality::Todo);
        debug_assert!(node_ref.point().calculated());

        if let Some(decorated) = maybe_decorated {
            // TODO we pretty much just ignore the fact that a decorated class can also be an enum.
            let mut inferred = Inferred::from_saved_node_ref(self.node_ref.into());
            for decorator in decorated.decorators().iter_reverse() {
                let decorate = self.node_ref.file.inference(i_s).infer_decorator(decorator);
                inferred = decorate.execute(
                    i_s,
                    &KnownArgs::new(
                        &inferred,
                        NodeRef::new(self.node_ref.file, decorator.index()),
                    ),
                );
            }
            // TODO for now don't save class decorators, because they are really not used in mypy.
            // let saved = inferred.save_redirect(i_s, name_def.file, name_def.node_index);
        }

        if let Some(dataclass) = was_dataclass {
            dataclass_init_func(&dataclass, db);
        }

        // Now that the class has been saved, we can use it like an actual class. We have to do
        // some member initialization things with TypedDicts, Enums, etc.
        let class = Class::with_undefined_generics(self.node_ref);
        if let Some(td) = was_typed_dict {
            initialize_typed_dict_members(db, &class, td);
        };

        if let Some(enum_) = was_enum {
            // Precalculate the enum values here. Note that this is intentionally done after
            // the insertion, to avoid recursions.
            // We need to calculate here, because otherwise the normal class
            // calculation will do it for us, which we probably do not want.
            for member in enum_.members.iter() {
                if member.value.is_some() {
                    member.infer_value(i_s, &enum_);
                }
            }
        }

        if was_enum_base {
            // Check if __new__ was correctly used in combination with enums (1)
            // Also check if mixins appear after enums (2)
            let mut had_new = 0;
            let mut enum_spotted: Option<Class> = None;
            for base in class.bases(db) {
                if let TypeOrClass::Class(c) = &base {
                    let is_enum = c.use_cached_class_infos(db).class_kind == ClassKind::Enum;
                    let has_mixin_enum_new = if is_enum {
                        c.bases(db).any(|inner| match inner {
                            TypeOrClass::Class(inner) => {
                                inner.use_cached_class_infos(db).class_kind != ClassKind::Enum
                                    && inner.has_customized_enum_new(i_s)
                            }
                            TypeOrClass::Type(_) => false,
                        })
                    } else {
                        c.has_customized_enum_new(i_s)
                    };
                    // (1)
                    if has_mixin_enum_new {
                        had_new += 1;
                        if had_new > 1 {
                            self.add_issue_on_name(
                                db,
                                IssueKind::EnumMultipleMixinNew {
                                    extra: c.qualified_name(db).into(),
                                },
                            );
                        }
                    }
                    // (2)
                    match enum_spotted {
                        Some(after) if !is_enum => {
                            self.add_issue_on_name(
                                db,
                                IssueKind::EnumMixinNotAllowedAfterEnum {
                                    after: after.qualified_name(db).into(),
                                },
                            );
                        }
                        _ => {
                            if is_enum {
                                enum_spotted = Some(*c);
                            }
                        }
                    }
                }
            }
        }
        // Change the methods that are actually changed by Python to be classmethods.
        for name in ["__init_subclass__", "__class_getitem__"] {
            if let Some(node_index) = self.class_storage.class_symbol_table.lookup_symbol(name) {
                let file = self.node_ref.file;
                if let Some(func_def) = NodeRef::new(file, node_index).maybe_name_of_function() {
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
                                    if i == 0 {
                                        p.type_ = ParamType::PositionalOnly(Type::Type(Rc::new(
                                            p.type_.expect_positional_type(),
                                        )));
                                    }
                                    p
                                })
                                .collect();
                        }
                        c.kind = FunctionKind::Classmethod {
                            had_first_self_or_class_annotation: true,
                        };
                        node_ref.insert_type(Type::Callable(Rc::new(c)));
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
    ) -> (Box<ClassInfos>, Option<bool>) {
        // Calculate all type vars beforehand
        let db = i_s.db;

        let mut bases: Vec<Type> = vec![];
        let mut incomplete_mro = false;
        let mut class_kind = ClassKind::Normal;
        let mut typed_dict_total = None;
        let mut had_new_typed_dict = false;
        let mut is_new_named_tuple = false;
        let mut metaclass = MetaclassState::None;
        let mut has_slots = self.class_storage.slots.is_some();
        let mut is_final = false;
        let mut dataclass_transform = None;
        let undefined_generics_type = OnceCell::new();
        let set_type_to_dataclass = |dc: &DataclassTransformObj, set_frozen_state_unknown: bool| {
            let mut options = dc.as_dataclass_options();
            if set_frozen_state_unknown {
                options.frozen = None;
            }
            if let Some(args) = self.node().arguments() {
                let args = SimpleArgs::new(
                    *i_s,
                    self.node_ref.file,
                    args.index(),
                    ArgumentsDetails::Node(args),
                );
                for arg in args.iter(i_s.mode) {
                    if let Some(key) = arg.keyword_name(db) {
                        options.assign_keyword_arg_to_dataclass_options(i_s, key, &arg);
                    }
                    // If another option is present, just ignore it. It is either checked by
                    // __init_subclass__ or it's a complex metaclass and we're screwed.
                }
            }
            undefined_generics_type
                .set(Rc::new(Type::Dataclass(Dataclass::new_uninitialized(
                    self.node_ref.as_link(),
                    type_vars,
                    options,
                ))))
                // Errors are ignored for now, whatever was first takes precedence.
                .ok();
        };
        let arguments = self.node().arguments();
        if let Some(arguments) = arguments {
            // Check metaclass before checking all the arguments, because it has a preference over
            // the metaclasses of the subclasses.
            for argument in arguments.iter() {
                if let Argument::Keyword(kwarg) = argument {
                    let (name, expr) = kwarg.unpack();
                    if name.as_str() == "metaclass" {
                        let node_ref = NodeRef::new(self.node_ref.file, expr.index());
                        let meta_base = TypeComputation::new(
                            i_s,
                            self.node_ref.file,
                            self.node_ref.as_link(),
                            &mut |_, _: &_, _: TypeVarLike, _| TypeVarCallbackReturn::NotFound {
                                allow_late_bound_callables: false,
                            },
                            TypeComputationOrigin::BaseClass,
                        )
                        .compute_base_class(expr);
                        match meta_base {
                            CalculatedBaseClass::Type(Type::Class(GenericClass {
                                link,
                                generics: ClassGenerics::None,
                            })) => {
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
                                    if let Some(infos) = c.maybe_cached_class_infos(db) {
                                        if let Some(dt) = &infos.dataclass_transform {
                                            set_type_to_dataclass(dt, true);
                                            dataclass_transform = infos.dataclass_transform.clone();
                                        }
                                    }
                                } else {
                                    node_ref.add_type_issue(
                                        db,
                                        IssueKind::MetaclassMustInheritFromType,
                                    );
                                }
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
                                node_ref.add_type_issue(db, IssueKind::InvalidMetaclass);
                            }
                        }
                    }
                }
            }

            // Calculate the type var remapping
            for argument in arguments.iter() {
                match argument {
                    Argument::Positional(n) => {
                        let base = TypeComputation::new(
                            i_s,
                            self.node_ref.file,
                            self.node_ref.as_link(),
                            &mut |_, _: &_, type_var_like: TypeVarLike, _| {
                                if let Some(usage) =
                                    type_vars.find(type_var_like.clone(), self.node_ref.as_link())
                                {
                                    TypeVarCallbackReturn::TypeVarLike(usage)
                                } else if let Some(usage) =
                                    self.maybe_type_var_like_in_parent(db, &type_var_like)
                                {
                                    usage
                                } else {
                                    // This can happen if two type var likes are used.
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
                                            if cached.class_kind != ClassKind::Normal
                                                && class_kind == ClassKind::Normal
                                                && !matches!(cached.class_kind, ClassKind::Protocol)
                                            {
                                                class_kind = cached.class_kind;
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
                                        if typed_dict_total.is_none() {
                                            typed_dict_total = Some(
                                                self.check_total_typed_dict_argument(db, arguments),
                                            )
                                        }
                                        class_kind = ClassKind::TypedDict;
                                        if typed_dict.is_final {
                                            NodeRef::new(self.node_ref.file, n.index())
                                                .add_type_issue(
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
                                        NodeRef::new(self.node_ref.file, n.index()).add_type_issue(
                                            db,
                                            IssueKind::CyclicDefinition { name },
                                        );
                                    } else {
                                        let cached_class_infos = class.use_cached_class_infos(db);
                                        if cached_class_infos.is_final {
                                            is_final = cached_class_infos.is_final;
                                            NodeRef::new(self.node_ref.file, n.index())
                                                .add_type_issue(
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
                                        match &cached_class_infos.class_kind {
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
                            CalculatedBaseClass::Protocol => {
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
                                    if typed_dict_total.is_none() {
                                        typed_dict_total = Some(
                                            self.check_total_typed_dict_argument(db, arguments),
                                        )
                                    }
                                }
                            }
                            CalculatedBaseClass::Generic => (),
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
                        };
                    }
                    Argument::Keyword(kwarg) => {
                        let (name, expr) = kwarg.unpack();
                        if name.as_str() != "metaclass" {
                            // Generate diagnostics
                            self.node_ref.file.inference(i_s).infer_expression(expr);
                            debug!(
                                "TODO shouldn't we handle this? In \
                                    testNewAnalyzerClassKeywordsForward it's ignored..."
                            )
                        }
                    }
                    Argument::Star(starred) => {
                        NodeRef::new(self.node_ref.file, starred.index())
                            .add_type_issue(db, IssueKind::InvalidBaseClass);
                    }
                    Argument::StarStar(double_starred) => {
                        NodeRef::new(self.node_ref.file, double_starred.index())
                            .add_type_issue(db, IssueKind::InvalidBaseClass);
                    }
                }
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
                    t.maybe_class(db).map_or(true, |cls| {
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
                class_kind,
                has_slots,
                protocol_members,
                is_final,
                total_ordering: false,
                is_runtime_checkable: true,
                abstract_attributes,
                dataclass_transform,
                undefined_generics_type,
            }),
            typed_dict_total,
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
                        generics: ClassGenerics::None,
                    });
                    let t2 = Type::Class(GenericClass {
                        link: link2,
                        generics: ClassGenerics::None,
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

    fn enum_members(&self, db: &Database) -> Box<[EnumMemberDefinition]> {
        let mut members = vec![];
        let mut name_indexes = vec![];
        for (name, name_index) in self.class_storage.class_symbol_table.iter() {
            if name.starts_with('_') {
                if name == "__members__" {
                    let name_node_ref = NodeRef::new(self.node_ref.file, *name_index);
                    if !name_node_ref
                        .as_name()
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

        for &name_index in name_indexes {
            let name_node_ref = NodeRef::new(self.node_ref.file, name_index);
            if name_node_ref
                .add_to_node_index(-(NAME_TO_FUNCTION_DIFF as i64))
                .maybe_function()
                .is_none()
            {
                let point = name_node_ref.point();
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
                let name = name_node_ref.as_name();
                if let Some(assignment) = name.maybe_assignment_definition_name() {
                    if let AssignmentContent::WithAnnotation(_, _, Some(_)) = assignment.unpack() {
                        NodeRef::new(self.node_ref.file, point.node_index())
                            .add_type_issue(db, IssueKind::EnumMemberAnnotationDisallowed);
                    }
                }
                if name.is_assignment_annotation_without_definition()
                    && !self.node_ref.file.is_stub()
                {
                    continue;
                }

                // TODO An enum member is never a descriptor. (that's how 3.10 does it). Here we
                // however only filter for functions and ignore decorators.
                members.push(EnumMemberDefinition::new(
                    StringSlice::from_name(self.node_ref.file_index(), name).into(),
                    Some(name_node_ref.as_link()),
                ))
            }
        }
        members.into_boxed_slice()
    }

    fn check_total_typed_dict_argument(&self, db: &Database, args: CSTArguments) -> bool {
        let mut total = true;
        for argument in args.iter() {
            if let Argument::Keyword(kwarg) = argument {
                let (name, expr) = kwarg.unpack();
                if name.as_code() == "total" {
                    total = check_typed_dict_total_argument(expr, |issue| {
                        NodeRef::new(self.node_ref.file, expr.index()).add_type_issue(db, issue)
                    })
                    .unwrap_or(true);
                }
            }
        }
        total
    }

    fn named_tuple_from_class(&self, db: &Database) -> Rc<NamedTuple> {
        let name = self.name_string_slice();
        Rc::new(NamedTuple::new(
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
        let i_s = &InferenceState::new(db).with_class_context(&cls);
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
            CallableParams::new_simple(Rc::from(vec)),
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
            let variance = match name_node_ref.as_name().expect_type() {
                TypeLike::ImportFromAsName(_) | TypeLike::DottedAsName(_) => continue,
                TypeLike::Function(_) => {
                    let p = name_node_ref.point();
                    debug_assert!(p.is_name_of_name_def_like(), "{p:?}");
                    if p.node_index() != name_index {
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

fn initialize_typed_dict_members(db: &Database, cls: &Class, typed_dict: Rc<TypedDict>) {
    let typed_dict_definition = cls.maybe_typed_dict_definition().unwrap();
    let mut typed_dict_members = TypedDictMemberGatherer::default();
    if let Some(args) = cls.node().arguments() {
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
                        .borrow_mut()
                        .push(typed_dict.clone());
                    debug!(
                        "Defer typed dict member initialization for {:?} after {:?}",
                        cls.name(),
                        super_cls.name(),
                    );
                    return;
                };
                typed_dict_members.merge(db, node_ref, td.members(db));
            }
        }
    }
    debug!("Start TypedDict members calculation for {:?}", cls.name());
    let file = cls.node_ref.file;
    find_stmt_typed_dict_types(
        &InferenceState::new(db).with_class_context(&cls),
        file,
        &mut typed_dict_members,
        cls.node().block().iter_stmt_likes(),
        typed_dict_definition.total,
    );
    debug!("End TypedDict members calculation for {:?}", cls.name());
    typed_dict.late_initialization_of_members(typed_dict_members.into_boxed_slice());
    loop {
        let mut borrowed = typed_dict_definition
            .deferred_subclass_member_initializations
            .borrow_mut();
        let Some(deferred) = borrowed.pop() else {
            break;
        };
        drop(borrowed);
        // TODO is this initialization correct?
        let cls = Class::from_non_generic_link(db, deferred.defined_at);
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
    total: bool,
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
                        db,
                        file.name_resolution_for_types(i_s)
                            .compute_class_typed_dict_member(
                                StringSlice::from_name(file.file_index, name_def.name()),
                                annot,
                                total,
                            ),
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
                                db,
                                TypedDictMember {
                                    type_: Type::Any(AnyCause::Todo),
                                    required: true,
                                    name: StringSlice::from_name(file.file_index, name_def.name()),
                                    read_only: false,
                                },
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
                _ => NodeRef::new(file, assignment.index())
                    .add_type_issue(db, IssueKind::InvalidStmtInNamedTuple),
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
    NamedTuple(Rc<NamedTuple>),
    TypedDict(Rc<TypedDict>),
    Tuple(Rc<Tuple>),
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
            linearizable = false;
        }
    }
    let add_to_mro = |mro: &mut Vec<BaseClass>,
                      base_index: usize,
                      is_direct_base,
                      new_base: &BaseToBeAdded,
                      allowed_to_use: &mut usize| {
        if new_base.t.as_ref() != &object {
            mro.push(BaseClass {
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
                                    ClassGenerics::List(generics) => {
                                        generics[usage.index()].clone()
                                    }
                                    _ => unreachable!(),
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
            })
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
                    for base_bases in base_iterators.iter_mut() {
                        base_bases.next_if(|(_, next)| {
                            to_base_kind(&candidate.t) == to_base_kind(&next.t)
                        });
                    }
                    add_to_mro(
                        &mut mro,
                        base_index,
                        i == 0,
                        &candidate,
                        &mut allowed_to_use,
                    );
                    continue 'outer;
                }
            }
        }
        if !had_entry {
            break;
        }
        for (base_index, base_bases) in base_iterators.iter_mut().enumerate() {
            if let Some((i, type_)) = base_bases.next() {
                linearizable = false;
                // Here we know that we have issues and only add the type if it's not already
                // there.
                if mro.iter().any(|b| &b.type_ == type_.t.as_ref()) {
                    add_to_mro(&mut mro, base_index, i == 0, &type_, &mut allowed_to_use);
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

impl DataclassOptions {
    fn assign_keyword_arg_to_dataclass_options<'db>(
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
