use std::{
    borrow::Cow,
    cell::{Cell, OnceCell, RefCell},
    fmt,
    rc::Rc,
};

use parsa_python_cst::{
    Argument, Arguments as CSTArguments, Assignment, AssignmentContent, AsyncStmtContent, ClassDef,
    Decoratee, ExpressionContent, ExpressionPart, PrimaryContent, StmtLikeContent,
    StmtLikeIterator, Target, TypeLike,
};

use super::{overload::OverloadResult, Callable, Instance, InstanceLookupOptions, LookupDetails};
use crate::{
    arguments::{Args, KnownArgs, SimpleArgs},
    database::{
        BaseClass, ClassInfos, ClassKind, ClassStorage, ComplexPoint, Database, Locality,
        MetaclassState, ParentScope, Point, PointKind, PointLink, ProtocolMember, Specific,
        TypedDictDefinition,
    },
    debug,
    diagnostics::IssueKind,
    file::{
        use_cached_annotation_type, CalculatedBaseClass, MultiDefinitionIterator, PythonFile,
        TypeComputation, TypeComputationOrigin, TypeVarCallbackReturn, TypeVarFinder,
    },
    format_data::FormatData,
    getitem::SliceType,
    inference_state::InferenceState,
    inferred::{AttributeKind, FunctionOrOverload, Inferred, MroIndex},
    matching::{
        calculate_callable_dunder_init_type_vars_and_return,
        calculate_callable_type_vars_and_return, calculate_class_dunder_init_type_vars_and_return,
        format_got_expected, maybe_class_usage, ErrorStrs, FunctionOrCallable, Generic, Generics,
        LookupKind, Match, Matcher, MismatchReason, OnTypeError, ResultContext,
    },
    node_ref::NodeRef,
    python_state::{NAME_TO_CLASS_DIFF, NAME_TO_FUNCTION_DIFF},
    type_::{
        check_dataclass_options, dataclass_init_func, execute_functional_enum,
        infer_typed_dict_total_argument, infer_value_on_member, AnyCause, CallableContent,
        CallableLike, CallableParam, CallableParams, ClassGenerics, Dataclass, DataclassOptions,
        DbString, Enum, EnumMemberDefinition, FormatStyle, FunctionKind, FunctionOverload,
        GenericClass, GenericsList, LookupResult, NamedTuple, NeverCause, ParamSpecArg,
        ParamSpecUsage, ParamType, StringSlice, Tuple, TupleArgs, Type, TypeVarLike,
        TypeVarLikeUsage, TypeVarLikes, TypedDict, TypedDictMember, TypedDictMemberGatherer,
        Variance,
    },
    type_helpers::{FirstParamProperties, Function},
    utils::{debug_indent, join_with_commas},
};

// Basically save the type vars on the class keyword.
const CLASS_TO_TYPE_VARS_DIFFERENCE: i64 = 1;
// Basically the `(` or `:` after the name
pub const CLASS_TO_CLASS_INFO_DIFFERENCE: i64 = NAME_TO_CLASS_DIFF as i64 + 1;

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

pub(super) const ORDERING_METHODS: [&'static str; 4] = ["__lt__", "__le__", "__gt__", "__ge__"];

pub fn cache_class_name(name_def: NodeRef, class: ClassDef) {
    if !name_def.point().calculated() {
        name_def.set_point(Point::new_redirect(
            name_def.file_index(),
            class.index(),
            Locality::Todo,
        ));
    }
}

#[derive(Clone, Copy)]
pub struct Class<'a> {
    pub node_ref: NodeRef<'a>,
    pub class_storage: &'a ClassStorage,
    pub generics: Generics<'a>,
    type_var_remap: Option<&'a GenericsList>,
}

impl<'db: 'a, 'a> Class<'a> {
    pub fn new(
        node_ref: NodeRef<'a>,
        class_storage: &'a ClassStorage,
        generics: Generics<'a>,
        type_var_remap: Option<&'a GenericsList>,
    ) -> Self {
        Self {
            node_ref,
            class_storage,
            generics,
            type_var_remap,
        }
    }

    pub fn from_generic_class_components(
        db: &'db Database,
        link: PointLink,
        list: &'a ClassGenerics,
    ) -> Self {
        let generics = Generics::from_class_generics(db, list);
        Self::from_position(NodeRef::from_link(db, link), generics, None)
    }

    pub fn from_non_generic_link(db: &'db Database, link: PointLink) -> Self {
        Self::from_non_generic_node_ref(NodeRef::from_link(db, link))
    }

    pub fn from_non_generic_node_ref(node_ref: NodeRef<'db>) -> Self {
        Self::from_position(node_ref, Generics::None, None)
    }

    #[inline]
    pub fn from_position(
        node_ref: NodeRef<'a>,
        generics: Generics<'a>,
        type_var_remap: Option<&'a GenericsList>,
    ) -> Self {
        Self::new(
            node_ref,
            node_ref.expect_class_storage(),
            generics,
            type_var_remap,
        )
    }

    #[inline]
    pub fn with_undefined_generics(node_ref: NodeRef<'a>) -> Self {
        Self::from_position(node_ref, Generics::NotDefinedYet, None)
    }

    pub fn with_self_generics(db: &'a Database, node_ref: NodeRef<'a>) -> Self {
        let type_var_likes = Self::with_undefined_generics(node_ref).use_cached_type_vars(db);
        Self::from_position(
            node_ref,
            match type_var_likes.len() {
                0 => Generics::None,
                _ => Generics::Self_ {
                    class_definition: node_ref.as_link(),
                    type_var_likes,
                },
            },
            None,
        )
    }

    pub fn instance(self) -> Instance<'a> {
        Instance::new(self, None)
    }

    fn type_check_dunder_init_func(
        &self,
        i_s: &InferenceState<'db, '_>,
        __init__: LookupResult,
        dunder_init_class: TypeOrClass,
        args: &dyn Args<'db>,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError,
        from_type_type: bool, // Errors are different for Cls() vs. Type[Cls] that is instantiated
    ) -> ClassExecutionResult {
        let Some(inf) = __init__.into_maybe_inferred() else {
            if self.is_protocol(i_s.db) {
                if !from_type_type {
                    args.add_issue(
                        i_s,
                        IssueKind::CannotInstantiateProtocol {
                            name: self.name().into(),
                        },
                    )
                }
            } else {
                debug_assert!(self.incomplete_mro(i_s.db));
            }
            let type_var_likes = self.type_vars(i_s);
            return ClassExecutionResult::ClassGenerics(match type_var_likes.is_empty() {
                false => ClassGenerics::List(type_var_likes.as_any_generic_list()),
                true => ClassGenerics::None,
            });
        };
        match inf.init_as_function(i_s, dunder_init_class.as_maybe_class()) {
            FunctionOrOverload::Function(func) => {
                /*
                let type_vars = self.type_vars(i_s);
                if let Some(func_cls) = &mut func.class {
                    if func_cls.type_var_remap.is_some() && matches!(func_cls.generics, Generics::NotDefinedYet) {
                        func_cls.generics = Generics::Self_ { class_definition: self.node_ref.as_link(), type_var_likes: &type_vars }
                    }
                }
                */

                let calculated_type_args = calculate_class_dunder_init_type_vars_and_return(
                    i_s,
                    self,
                    func,
                    args.iter(i_s.mode),
                    |issue| args.add_issue(i_s, issue),
                    result_context,
                    Some(on_type_error),
                );
                ClassExecutionResult::ClassGenerics(
                    calculated_type_args.type_arguments_into_class_generics(i_s.db),
                )
            }
            FunctionOrOverload::Callable(callable_content) => {
                let calculated_type_args = match dunder_init_class.as_base_class(i_s.db, self) {
                    Some(class) => {
                        let from_class = matches!(dunder_init_class, TypeOrClass::Class(_));
                        calculate_callable_dunder_init_type_vars_and_return(
                            i_s,
                            self,
                            Callable::new(&callable_content, from_class.then_some(class)),
                            args.iter(i_s.mode),
                            |issue| args.add_issue(i_s, issue),
                            from_class,
                            result_context,
                            Some(on_type_error),
                        )
                    }
                    // Happens for example when NamedTuples are involved.
                    None => calculate_callable_type_vars_and_return(
                        i_s,
                        Callable::new(&callable_content, Some(*self)),
                        args.iter(i_s.mode),
                        |issue| args.add_issue(i_s, issue),
                        false,
                        result_context,
                        Some(on_type_error),
                    ),
                };
                ClassExecutionResult::ClassGenerics(
                    calculated_type_args.type_arguments_into_class_generics(i_s.db),
                )
            }
            FunctionOrOverload::Overload(overloaded_function) => match overloaded_function
                .find_matching_function(
                    i_s,
                    args,
                    false,
                    Some(self),
                    true,
                    result_context,
                    on_type_error,
                    &|_, calculated_type_args| {
                        Type::new_class(
                            self.node_ref.as_link(),
                            calculated_type_args.type_arguments_into_class_generics(i_s.db),
                        )
                    },
                ) {
                OverloadResult::Single(callable) => {
                    // Execute the found function to create the diagnostics.
                    let result = calculate_callable_dunder_init_type_vars_and_return(
                        i_s,
                        self,
                        callable,
                        args.iter(i_s.mode),
                        |issue| args.add_issue(i_s, issue),
                        true,
                        result_context,
                        Some(on_type_error),
                    );
                    ClassExecutionResult::ClassGenerics(
                        result.type_arguments_into_class_generics(i_s.db),
                    )
                }
                OverloadResult::Union(t) => ClassExecutionResult::Inferred(Inferred::from_type(t)),
                OverloadResult::NotFound => {
                    ClassExecutionResult::Inferred(Inferred::new_any_from_error())
                }
            },
        }
    }

    pub fn node(&self) -> ClassDef<'a> {
        ClassDef::by_index(&self.node_ref.file.tree, self.node_ref.node_index)
    }

    pub fn name_string_slice(&self) -> StringSlice {
        let name = self.node().name();
        StringSlice::new(self.node_ref.file_index(), name.start(), name.end())
    }

    pub fn use_cached_type_vars(&self, db: &'db Database) -> &'a TypeVarLikes {
        let node_ref = self.type_vars_node_ref();
        let point = node_ref.point();
        debug_assert!(point.calculated());
        Self::get_calculated_type_vars(db, node_ref, point)
    }

    fn get_calculated_type_vars(
        db: &'db Database,
        node_ref: NodeRef<'a>,
        point: Point,
    ) -> &'a TypeVarLikes {
        if point.kind() == PointKind::Specific {
            &db.python_state.empty_type_var_likes
        } else {
            match node_ref.complex().unwrap() {
                ComplexPoint::TypeVarLikes(type_vars) => type_vars,
                _ => unreachable!(),
            }
        }
    }

    pub fn type_vars(&self, i_s: &InferenceState<'db, '_>) -> &'a TypeVarLikes {
        let node_ref = self.type_vars_node_ref();
        let point = node_ref.point();
        if point.calculated() {
            return Self::get_calculated_type_vars(i_s.db, node_ref, point);
        }

        let type_vars = TypeVarFinder::find_class_type_vars(i_s, self);
        if type_vars.is_empty() {
            self.type_vars_node_ref()
                .set_point(Point::new_specific(Specific::Analyzed, Locality::Todo));
        } else {
            self.type_vars_node_ref()
                .insert_complex(ComplexPoint::TypeVarLikes(type_vars), Locality::Todo);
        }
        self.type_vars(i_s)
    }

    pub fn maybe_type_var_like_in_parent(
        &self,
        db: &Database,
        type_var: &TypeVarLike,
    ) -> Option<TypeVarCallbackReturn> {
        match self.class_storage.parent_scope {
            ParentScope::Module => None,
            ParentScope::Class(node_index) => {
                let parent_class =
                    Self::with_undefined_generics(NodeRef::new(self.node_ref.file, node_index));
                parent_class.find_type_var_like_including_ancestors(db, type_var, true)
            }
            ParentScope::Function(node_index) => {
                Function::new_with_unknown_parent(db, NodeRef::new(self.node_ref.file, node_index))
                    .find_type_var_like_including_ancestors(db, type_var, true)
            }
        }
    }

    pub fn find_type_var_like_including_ancestors(
        &self,
        db: &Database,
        type_var: &TypeVarLike,
        class_seen: bool,
    ) -> Option<TypeVarCallbackReturn> {
        if let Some(tvl) = self
            .use_cached_type_vars(db)
            .find(type_var.clone(), self.node_ref.as_link())
        {
            if class_seen {
                return Some(TypeVarCallbackReturn::BoundByOuterClass);
            }
            return Some(TypeVarCallbackReturn::TypeVarLike(tvl));
        }
        self.maybe_type_var_like_in_parent(db, type_var)
    }

    pub fn is_calculating_class_infos(&self) -> bool {
        self.class_info_node_ref().point().calculating()
    }

    #[inline]
    fn type_vars_node_ref(&self) -> NodeRef<'a> {
        self.node_ref
            .add_to_node_index(CLASS_TO_TYPE_VARS_DIFFERENCE)
    }

    #[inline]
    fn class_info_node_ref(&self) -> NodeRef<'a> {
        self.node_ref
            .add_to_node_index(CLASS_TO_CLASS_INFO_DIFFERENCE)
    }

    pub fn ensure_calculated_class_infos(&self, i_s: &InferenceState<'db, '_>) {
        let node_ref = self.class_info_node_ref();
        let point = node_ref.point();
        if point.calculated() {
            return;
        }

        debug_assert!(NodeRef::new(node_ref.file, self.node().name_def().index())
            .point()
            .calculated());
        debug!("Calculate class infos for {}", self.name());

        node_ref.set_point(Point::new_calculating());

        let type_vars = self.type_vars(i_s);

        let mut was_dataclass = None;
        let maybe_decorated = self.node().maybe_decorated();
        let mut is_final = false;
        let mut total_ordering = false;
        let mut is_runtime_checkable = false;
        if let Some(decorated) = maybe_decorated {
            let inference = self.node_ref.file.inference(i_s);

            let mut dataclass_options = None;
            let dataclass_link = i_s.db.python_state.dataclasses_dataclass();
            for decorator in decorated.decorators().iter() {
                let expr = decorator.named_expression().expression();
                if let ExpressionContent::ExpressionPart(ExpressionPart::Primary(primary)) =
                    expr.unpack()
                {
                    if inference
                        .infer_primary_or_atom(primary.first())
                        .maybe_saved_link()
                        == Some(dataclass_link)
                    {
                        if let PrimaryContent::Execution(exec) = primary.second() {
                            let args =
                                SimpleArgs::new(*i_s, self.node_ref.file, primary.index(), exec);
                            dataclass_options = Some(check_dataclass_options(i_s, &args));
                            continue;
                        }
                    }
                }
                let inf = inference.infer_expression(expr);
                if let Some(maybe_link) = inf.maybe_saved_link() {
                    if maybe_link == i_s.db.python_state.typing_final().as_link() {
                        is_final = true;
                    } else if maybe_link == i_s.db.python_state.total_ordering_link() {
                        total_ordering = true;
                    } else if maybe_link == i_s.db.python_state.runtime_checkable_link()
                        || maybe_link
                            == i_s
                                .db
                                .python_state
                                .typing_extensions_runtime_checkable_link()
                    {
                        is_runtime_checkable = true;
                    }
                }

                if inf.maybe_saved_link() == Some(dataclass_link) {
                    dataclass_options = Some(DataclassOptions::default());
                }
            }
            if let Some(dataclass_options) = dataclass_options {
                let dataclass = Dataclass::new(
                    GenericClass {
                        link: self.node_ref.as_link(),
                        generics: if type_vars.is_empty() {
                            ClassGenerics::None
                        } else {
                            ClassGenerics::NotDefinedYet
                        },
                    },
                    dataclass_options,
                );
                let class = dataclass.class(i_s.db);
                if dataclass.options.slots && class.lookup_symbol(i_s, "__slots__").is_some() {
                    class.add_issue_on_name(
                        i_s,
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
            class_infos
                .undefined_generics_type
                .set(Rc::new(Type::Dataclass(dataclass.clone())))
                .unwrap();
        }
        if total_ordering {
            if !self.has_a_total_ordering_method_in_mro(i_s.db, &class_infos.mro) {
                // If there is no corresponding method, we just ignore the MRO
                NodeRef::new(self.node_ref.file, self.node().name_def().index())
                    .add_issue(i_s, IssueKind::TotalOrderingMissingMethod);
                total_ordering = false;
            }
        }
        class_infos.is_final |= is_final;
        class_infos.total_ordering = total_ordering;

        if class_infos.class_kind == ClassKind::Protocol {
            class_infos.is_runtime_checkable = is_runtime_checkable;
        } else {
            if is_runtime_checkable {
                self.add_issue_on_name(
                    i_s,
                    IssueKind::RuntimeCheckableCanOnlyBeUsedWithProtocolClasses,
                );
            }
            class_infos.is_runtime_checkable = true;
        }

        if is_final && !class_infos.abstract_attributes.is_empty() {
            self.add_issue_on_name(
                i_s,
                IssueKind::FinalClassHasAbstractAttributes {
                    class_name: self.qualified_name(i_s.db).into(),
                    attributes: join_abstract_attributes(i_s.db, &class_infos.abstract_attributes),
                },
            );
        }

        let mut was_enum = None;
        let mut was_enum_base = false;
        if let MetaclassState::Some(link) = class_infos.metaclass {
            if link == i_s.db.python_state.enum_meta_link() {
                was_enum_base = true;
                if !self.use_cached_type_vars(i_s.db).is_empty() {
                    self.add_issue_on_name(i_s, IssueKind::EnumCannotBeGeneric);
                }
                class_infos.class_kind = ClassKind::Enum;
                let members = self.enum_members(i_s);
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
            class_infos
                .undefined_generics_type
                .set(enum_type.clone())
                .unwrap();
        }
        let mut was_typed_dict = None;
        if let Some(total) = typed_dict_total {
            let td = TypedDict::new_class_definition(
                self.name_string_slice(),
                self.node_ref.as_link(),
                self.type_vars(i_s).clone(),
                is_final,
            );
            class_infos
                .undefined_generics_type
                .set(Rc::new(Type::TypedDict(td.clone())))
                .unwrap();
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
            let mut inferred = Inferred::from_saved_node_ref(self.node_ref);
            for decorator in decorated.decorators().iter_reverse() {
                let decorate = self
                    .node_ref
                    .file
                    .inference(i_s)
                    .infer_named_expression(decorator.named_expression());
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
            dataclass_init_func(&dataclass, i_s.db);
        }

        if let Some(td) = was_typed_dict {
            self.initialize_typed_dict_members(i_s, td);
        };

        if let Some(enum_) = was_enum {
            // Precalculate the enum values here. Note that this is intentionally done after
            // the insertion, to avoid recursions.
            // We need to calculate here, because otherwise the normal class
            // calculation will do it for us, which we probably do not want.
            for member in enum_.members.iter() {
                if member.value.is_some() {
                    infer_value_on_member(i_s, &enum_, member.value);
                }
            }
        }

        if was_enum_base {
            // Check if __new__ was correctly used in combination with enums (1)
            // Also check if mixins appear after enums (2)
            let mut had_new = 0;
            let mut enum_spotted: Option<Class> = None;
            for base in self.bases(i_s.db) {
                if let TypeOrClass::Class(c) = &base {
                    let is_enum = c.use_cached_class_infos(i_s.db).class_kind == ClassKind::Enum;
                    let has_mixin_enum_new = if is_enum {
                        c.bases(i_s.db).any(|inner| match inner {
                            TypeOrClass::Class(inner) => {
                                inner.use_cached_class_infos(i_s.db).class_kind != ClassKind::Enum
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
                                i_s,
                                IssueKind::EnumMultipleMixinNew {
                                    extra: c.qualified_name(i_s.db).into(),
                                },
                            );
                        }
                    }
                    // (2)
                    match enum_spotted {
                        Some(after) if !is_enum => {
                            self.add_issue_on_name(
                                i_s,
                                IssueKind::EnumMixinNotAllowedAfterEnum {
                                    after: after.qualified_name(i_s.db).into(),
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
                    let func = Function::new(node_ref, Some(*self));
                    func.ensure_cached_func(i_s);
                    let mut c = func.as_callable(i_s, FirstParamProperties::None);
                    if func_def.maybe_decorated().is_some() {
                        debug!("Make method a classmethod: {name}");
                    } else {
                        if !c.kind.had_first_self_or_class_annotation() {
                            let CallableParams::Simple(ps) = &mut c.params else {
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

    pub fn has_a_total_ordering_method_in_mro(&self, db: &Database, mro: &[BaseClass]) -> bool {
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

    pub fn use_cached_class_infos(&self, db: &'db Database) -> &'db ClassInfos {
        self.maybe_cached_class_infos(db).unwrap()
    }

    pub fn incomplete_mro(&self, db: &Database) -> bool {
        self.use_cached_class_infos(db).incomplete_mro
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

    pub fn bases(&self, db: &'a Database) -> impl Iterator<Item = TypeOrClass<'a>> {
        let generics = self.generics;
        self.use_cached_class_infos(db)
            .mro
            .iter()
            .filter(|&b| b.is_direct_base)
            .map(move |b| apply_generics_to_base_class(db, &b.type_, generics))
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
        let arguments = self.node().arguments();
        if let Some(arguments) = arguments {
            // Check metaclass before checking all the arguments, because it has a preference over
            // the metaclasses of the subclasses.
            for argument in arguments.iter() {
                if let Argument::Keyword(kwarg) = argument {
                    let (name, expr) = kwarg.unpack();
                    if name.as_str() == "metaclass" {
                        let node_ref = NodeRef::new(self.node_ref.file, expr.index());
                        let inference = self.node_ref.file.inference(i_s);
                        let meta_base = TypeComputation::new(
                            &inference,
                            self.node_ref.as_link(),
                            &mut |i_s, _: &_, type_var_like: TypeVarLike, _| {
                                TypeVarCallbackReturn::NotFound {
                                    allow_late_bound_callables: false,
                                }
                            },
                            TypeComputationOrigin::BaseClass,
                        )
                        .compute_base_class(expr);
                        match meta_base {
                            CalculatedBaseClass::Type(Type::Class(GenericClass {
                                link,
                                generics: ClassGenerics::None,
                            })) => {
                                let c = Class::from_non_generic_link(db, link);
                                if c.incomplete_mro(db)
                                    || c.class_link_in_mro(
                                        i_s,
                                        db.python_state.bare_type_node_ref().as_link(),
                                    )
                                {
                                    Self::update_metaclass(
                                        i_s,
                                        node_ref,
                                        &mut metaclass,
                                        MetaclassState::Some(link),
                                    )
                                } else {
                                    node_ref
                                        .add_issue(i_s, IssueKind::MetaclassMustInheritFromType);
                                }
                            }
                            CalculatedBaseClass::Unknown => {
                                if node_ref.file.flags(i_s.db).disallow_subclassing_any {
                                    NodeRef::new(self.node_ref.file, kwarg.index()).add_issue(
                                        i_s,
                                        IssueKind::DisallowedAnyMetaclass {
                                            class: expr.as_code().into(),
                                        },
                                    );
                                }
                                metaclass = MetaclassState::Unknown
                            }
                            _ => {
                                node_ref.add_issue(i_s, IssueKind::InvalidMetaclass);
                            }
                        }
                    }
                }
            }

            // Calculate the type var remapping
            for argument in arguments.iter() {
                match argument {
                    Argument::Positional(n) => {
                        let inference = self.node_ref.file.inference(i_s);
                        let base = TypeComputation::new(
                            &inference,
                            self.node_ref.as_link(),
                            &mut |i_s, _: &_, type_var_like: TypeVarLike, _| {
                                if let Some(usage) =
                                    type_vars.find(type_var_like.clone(), self.node_ref.as_link())
                                {
                                    TypeVarCallbackReturn::TypeVarLike(usage)
                                } else if let Some(usage) =
                                    self.maybe_type_var_like_in_parent(i_s.db, &type_var_like)
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
                                        .add_issue(i_s, IssueKind::DuplicateBaseClass { name });
                                    incomplete_mro = true;
                                    continue;
                                }
                                bases.push(t);
                                let class = match &bases.last().unwrap() {
                                    Type::Class(c) => {
                                        if let Some(cached) =
                                            c.class(i_s.db).maybe_cached_class_infos(i_s.db)
                                        {
                                            if cached.class_kind != ClassKind::Normal
                                                && class_kind == ClassKind::Normal
                                                && !matches!(cached.class_kind, ClassKind::Protocol)
                                            {
                                                class_kind = cached.class_kind;
                                            }
                                        }
                                        Some(c.class(db))
                                    }
                                    Type::Tuple(content) => {
                                        if class_kind == ClassKind::Normal {
                                            class_kind = ClassKind::Tuple;
                                        } else {
                                            todo!()
                                        }
                                        None
                                    }
                                    Type::Dataclass(d) => Some(d.class(db)),
                                    Type::TypedDict(typed_dict) => {
                                        if typed_dict_total.is_none() {
                                            typed_dict_total =
                                                Some(self.check_total_typed_dict_argument(
                                                    i_s, arguments,
                                                ))
                                        }
                                        class_kind = ClassKind::TypedDict;
                                        if typed_dict.is_final {
                                            NodeRef::new(self.node_ref.file, n.index()).add_issue(
                                                i_s,
                                                IssueKind::CannotInheritFromFinalClass {
                                                    class_name: Box::from(
                                                        typed_dict.name.unwrap().as_str(i_s.db),
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
                                            .add_issue(i_s, IssueKind::CyclicDefinition { name });
                                    } else {
                                        let cached_class_infos = class.use_cached_class_infos(db);
                                        if cached_class_infos.is_final {
                                            is_final = cached_class_infos.is_final;
                                            NodeRef::new(self.node_ref.file, n.index()).add_issue(
                                                i_s,
                                                IssueKind::CannotInheritFromFinalClass {
                                                    class_name: Box::from(class.name()),
                                                },
                                            );
                                        }
                                        incomplete_mro |= cached_class_infos.incomplete_mro;
                                        has_slots |= cached_class_infos.has_slots;
                                        Self::update_metaclass(
                                            i_s,
                                            NodeRef::new(self.node_ref.file, n.index()),
                                            &mut metaclass,
                                            cached_class_infos.metaclass,
                                        );
                                        match &cached_class_infos.class_kind {
                                            ClassKind::NamedTuple => {
                                                if matches!(
                                                    class_kind,
                                                    ClassKind::Normal | ClassKind::NamedTuple
                                                ) {
                                                    class_kind = ClassKind::NamedTuple;
                                                } else {
                                                    todo!()
                                                }
                                            }
                                            ClassKind::TypedDict => unreachable!(),
                                            _ => (),
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
                                let named_tuple = self
                                    .named_tuple_from_class(&i_s.with_class_context(self), *self);
                                bases.push(Type::NamedTuple(named_tuple));
                                class_kind = ClassKind::NamedTuple;
                            }
                            CalculatedBaseClass::TypedDict => {
                                if had_new_typed_dict {
                                    NodeRef::new(self.node_ref.file, n.index()).add_issue(
                                        i_s,
                                        IssueKind::DuplicateBaseClass {
                                            name: "TypedDict".into(),
                                        },
                                    );
                                } else {
                                    had_new_typed_dict = true;
                                    class_kind = ClassKind::TypedDict;
                                    if typed_dict_total.is_none() {
                                        typed_dict_total = Some(
                                            self.check_total_typed_dict_argument(i_s, arguments),
                                        )
                                    }
                                }
                            }
                            CalculatedBaseClass::Generic => (),
                            CalculatedBaseClass::Unknown => {
                                if self.node_ref.file.flags(i_s.db).disallow_subclassing_any {
                                    NodeRef::new(self.node_ref.file, n.index()).add_issue(
                                        i_s,
                                        IssueKind::DisallowedAnySubclass {
                                            class: n.as_code().into(),
                                        },
                                    );
                                }
                                incomplete_mro = true;
                            }
                            CalculatedBaseClass::InvalidEnum(enum_) => {
                                let name = enum_.name.as_str(i_s.db);
                                NodeRef::new(self.node_ref.file, n.index()).add_issue(
                                    i_s,
                                    IssueKind::EnumWithMembersNotExtendable { name: name.into() },
                                );
                                if enum_.class(i_s.db).use_cached_class_infos(i_s.db).is_final {
                                    NodeRef::new(self.node_ref.file, n.index()).add_issue(
                                        i_s,
                                        IssueKind::CannotInheritFromFinalClass {
                                            class_name: Box::from(name),
                                        },
                                    );
                                }
                                incomplete_mro = true;
                            }
                            CalculatedBaseClass::Invalid => {
                                NodeRef::new(self.node_ref.file, n.index())
                                    .add_issue(i_s, IssueKind::InvalidBaseClass);
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
                            .add_issue(i_s, IssueKind::InvalidBaseClass);
                    }
                    Argument::StarStar(double_starred) => {
                        NodeRef::new(self.node_ref.file, double_starred.index())
                            .add_issue(i_s, IssueKind::InvalidBaseClass);
                    }
                }
            }
        }
        match class_kind {
            ClassKind::TypedDict => {
                if bases.iter().any(|t| !matches!(t, Type::TypedDict(_))) {
                    NodeRef::new(self.node_ref.file, arguments.unwrap().index())
                        .add_issue(i_s, IssueKind::TypedDictBasesMustBeTypedDicts);
                }
            }
            ClassKind::Protocol => {
                if bases.iter().any(|t| {
                    t.maybe_class(i_s.db).map_or(true, |cls| {
                        !cls.is_protocol(i_s.db)
                            && cls.node_ref != i_s.db.python_state.object_node_ref()
                    })
                }) {
                    NodeRef::new(self.node_ref.file, arguments.unwrap().index())
                        .add_issue(i_s, IssueKind::BasesOfProtocolMustBeProtocol);
                }
            }
            _ => (),
        }
        if is_new_named_tuple && bases.len() > 1 {
            NodeRef::new(self.node_ref.file, arguments.unwrap().index())
                .add_issue(i_s, IssueKind::NamedTupleShouldBeASingleBase);
        }

        let (mro, linearizable) = linearize_mro_and_return_linearizable(i_s, &bases);
        if !linearizable {
            add_inconsistency_issue(i_s, self)
        }

        let mut found_tuple_like = None;
        for base in mro.iter() {
            if matches!(base.type_, Type::Tuple(_) | Type::NamedTuple(_)) {
                if let Some(found_tuple_like) = found_tuple_like {
                    if found_tuple_like != &base.type_ {
                        NodeRef::new(self.node_ref.file, arguments.unwrap().index())
                            .add_issue(i_s, IssueKind::IncompatibleBaseTuples);
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
            self.calculate_abstract_attributes(i_s, &metaclass, &class_kind, &mro);
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
                undefined_generics_type: OnceCell::new(),
            }),
            typed_dict_total,
        )
    }

    fn calculate_abstract_attributes(
        &self,
        i_s: &InferenceState,
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
                    .any(|&l| NodeRef::from_link(i_s.db, l).as_code() == name)
            {
                for base in &mro[..mro_index] {
                    if let Type::Class(c) = &base.type_ {
                        let class = c.class(i_s.db);
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
                let class = c.class(i_s.db);
                let class_infos = class.use_cached_class_infos(i_s.db);
                if base.is_direct_base {
                    for &link in class_infos.abstract_attributes.iter() {
                        let name = NodeRef::from_link(i_s.db, link).as_code();
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
        result.sort_by_key(|&l| NodeRef::from_link(i_s.db, l).as_code());
        if self.class_storage.abstract_attributes.is_empty()
            && !result.is_empty()
            && self.node_ref.file.is_stub()
        {
            let has_abc_meta_metaclass = || match metaclass {
                MetaclassState::Some(link) => Class::from_non_generic_link(i_s.db, *link)
                    .class_link_in_mro(i_s, i_s.db.python_state.abc_meta_link()),
                _ => false,
            };
            if !has_abc_meta_metaclass() {
                self.add_issue_on_name(
                    i_s,
                    IssueKind::ClassNeedsAbcMeta {
                        class_name: self.qualified_name(i_s.db).into(),
                        attributes: join_abstract_attributes(i_s.db, &result),
                    },
                )
            }
        }
        result.into()
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
                            node_ref.add_issue(i_s, IssueKind::MetaclassConflict);
                        }
                    }
                }
                _ => *current = new,
            },
        }
    }

    fn check_total_typed_dict_argument(&self, i_s: &InferenceState, args: CSTArguments) -> bool {
        let mut total = true;
        let inference = self.node_ref.file.inference(i_s);
        for argument in args.iter() {
            if let Argument::Keyword(kwarg) = argument {
                let (name, expr) = kwarg.unpack();
                if name.as_code() == "total" {
                    let inf = inference.infer_expression(expr);
                    total = infer_typed_dict_total_argument(i_s, inf, |issue| {
                        NodeRef::new(self.node_ref.file, expr.index()).add_issue(i_s, issue)
                    })
                    .unwrap_or(true);
                }
            }
        }
        total
    }

    pub fn is_metaclass(&self, db: &Database) -> bool {
        let python_type = db.python_state.bare_type_type();
        self.use_cached_class_infos(db)
            .mro
            .iter()
            .any(|t| t.type_ == python_type)
    }

    pub fn maybe_metaclass(&self, db: &Database) -> Option<PointLink> {
        match self.use_cached_class_infos(db).metaclass {
            MetaclassState::Some(link) => Some(link),
            _ => None,
        }
    }

    pub fn is_base_exception_group(&self, i_s: &InferenceState) -> bool {
        i_s.db
            .python_state
            .base_exception_group_node_ref()
            .is_some_and(|g| self.class_link_in_mro(i_s, g.as_link()))
    }

    pub fn is_base_exception(&self, i_s: &InferenceState) -> bool {
        self.class_link_in_mro(i_s, i_s.db.python_state.base_exception_node_ref().as_link())
    }

    pub fn is_exception(&self, i_s: &InferenceState) -> bool {
        self.class_link_in_mro(i_s, i_s.db.python_state.exception_node_ref().as_link())
    }

    pub fn is_protocol(&self, db: &Database) -> bool {
        self.use_cached_class_infos(db).class_kind == ClassKind::Protocol
    }

    pub fn check_protocol_match(
        &self,
        i_s: &InferenceState<'db, '_>,
        matcher: &mut Matcher,
        other: &Type,
    ) -> Match {
        const SHOW_MAX_MISMATCHES: usize = 2;
        const MAX_MISSING_MEMBERS: usize = 2;
        let mut missing_members = vec![];
        let mut mismatches = 0;
        let mut notes = vec![];
        let mut had_conflict_note = false;
        let mut had_at_least_one_member_with_same_name = false;

        let ignore_positional_param_names_old = matcher.ignore_positional_param_names;
        matcher.ignore_positional_param_names = true;

        let mut protocol_member_count = 0;
        for (mro_index, c) in self.mro_maybe_without_object(i_s.db, true) {
            let TypeOrClass::Class(c) = c else {
                debug!("Ignored a type in protocol mro. Why is it there in the first place?");
                continue;
            };
            let protocol_members = &c.use_cached_class_infos(i_s.db).protocol_members;
            protocol_member_count += protocol_members.len();
            for protocol_member in protocol_members.iter() {
                let name = NodeRef::new(c.node_ref.file, protocol_member.name_index).as_code();
                // It is possible to match a Callable against a Protocol that only implements
                // __call__.
                let is_call = name == "__call__";
                let mut mismatch = false;
                let had_error = RefCell::new(None);
                if is_call {
                    // __call__ matching doesn't ignore param names, matching all other methods
                    // does.
                    matcher.ignore_positional_param_names = false;
                    if !matches!(other, Type::Class(_)) {
                        let inf1 = Instance::new(c, None)
                            .type_lookup(
                                i_s,
                                |issue| {
                                    let issue_str = self.node_ref.issue_to_str(i_s, issue);
                                    debug!("Issue in protocol __call__: {issue_str}");
                                    *had_error.borrow_mut() = Some(issue_str);
                                },
                                name,
                            )
                            .into_inferred();
                        //Iterable[_T] :> EnumMeta Type[_EnumMemberT] :> EnumMeta
                        if inf1
                            .as_cow_type(i_s)
                            .matches(i_s, matcher, other, protocol_member.variance)
                            .bool()
                            && had_error.borrow().is_none()
                        {
                            matcher.ignore_positional_param_names = true;
                            had_at_least_one_member_with_same_name = true;
                            continue;
                        }
                        mismatch = true;
                    }
                }

                let had_binding_error = Cell::new(false);
                let mut had_lookup_error = false;
                let protocol_lookup_details = Instance::new(c, None).lookup(
                    i_s,
                    name,
                    InstanceLookupOptions::new(&|issue| had_binding_error.set(true))
                        .with_as_self_instance(&|| other.clone())
                        .with_disallowed_lazy_bound_method(),
                );
                let inf1 = protocol_lookup_details.lookup.into_inferred();

                // It's a bit weird that we have to filter out TypeVarLikes here, but at the moment
                // there is no way to have that information when we gather Protocol members.
                if matches!(
                    inf1.maybe_complex_point(i_s.db),
                    Some(ComplexPoint::TypeVarLike(_))
                ) {
                    continue;
                }

                other.run_after_lookup_on_each_union_member(
                    i_s,
                    None,
                    self.node_ref.file_index(),
                    name,
                    LookupKind::Normal,
                    &mut ResultContext::Unknown,
                    &|issue| {
                        let issue_str = self.node_ref.issue_to_str(i_s, issue);
                        debug!("Issue in protocol: {}", issue_str);
                        *had_error.borrow_mut() = Some(issue_str);
                    },
                    &mut |_, lookup_details| {
                        if matches!(lookup_details.lookup, LookupResult::None) {
                            had_lookup_error = true;
                        } else if had_error.borrow().is_none() {
                            had_at_least_one_member_with_same_name = true;
                            let t1 = inf1.as_cow_type(i_s);
                            let lookup = lookup_details.lookup.into_inferred();
                            let t2 = lookup.as_cow_type(i_s);
                            let m = t1.matches(i_s, matcher, &t2, protocol_member.variance);

                            let is_final_mismatch = lookup_details.attr_kind == AttributeKind::Final && protocol_lookup_details.attr_kind != AttributeKind::Final;

                            if (!m.bool()
                                    || (is_call && !matches!(other, Type::Class(_)))
                                    || had_binding_error.get()
                                )
                                // is_final_mismatch errors will be added later
                                && !is_final_mismatch
                            {
                                if !had_conflict_note {
                                    had_conflict_note = true;
                                    notes.push(protocol_conflict_note(i_s.db, other));
                                }
                                mismatch = true;
                                if mismatches < SHOW_MAX_MISMATCHES {
                                    match other.maybe_class(i_s.db) {
                                        Some(cls) => add_protocol_mismatch(
                                            i_s,
                                            &mut notes,
                                            name,
                                            &t1,
                                            &t2,
                                            &c.lookup(i_s, name, ClassLookupOptions::new(&|_| ()).with_as_type_type(&|| if other.is_subclassable(i_s.db) {
                                                Type::Type(Rc::new(other.clone()))
                                            } else {
                                                self.as_type_type(i_s.db)
                                            }))
                                                .lookup
                                                .into_inferred()
                                                .as_cow_type(i_s),
                                            &cls.simple_lookup(i_s, |_| (), name)
                                                .into_inferred()
                                                .as_cow_type(i_s),
                                        ),
                                        None => {
                                            let full_other = match other {
                                                Type::Type(t) if is_call => {
                                                    t.maybe_class(i_s.db).and_then(|cls| {
                                                        notes.push(format!(
                                                            r#""{}" has constructor incompatible with "__call__" of "{}""#,
                                                            cls.name(),
                                                            self.name()
                                                        ).into());
                                                        cls.find_relevant_constructor(i_s)
                                                            .into_type(i_s, cls)
                                                    })
                                                }
                                                _ => None,
                                            };
                                            add_protocol_mismatch(
                                                i_s,
                                                &mut notes,
                                                name,
                                                &t1,
                                                &t2,
                                                &t1,
                                                full_other.as_ref().unwrap_or(&t2),
                                            )
                                        }
                                    }
                                }
                            }
                            if lookup_details.attr_kind.is_read_only_property()
                                && !protocol_lookup_details.attr_kind.is_read_only_property()
                            {
                                mismatch = true;
                                if mismatches < SHOW_MAX_MISMATCHES {
                                    notes.push(
                                        format!(
                                        "Protocol member {}.{name} expected settable variable, \
                                         got read-only attribute",
                                        self.name()
                                    )
                                        .into(),
                                    );
                                }
                            }
                            if matches!(protocol_lookup_details.attr_kind, AttributeKind::ClassVar) {
                                if !matches!(lookup_details.attr_kind, AttributeKind::ClassVar)
                                {
                                    mismatch = true;
                                    if mismatches < SHOW_MAX_MISMATCHES {
                                        notes.push(
                                            format!(
                                                "Protocol member {}.{name} expected class variable, \
                                             got instance variable",
                                                self.name()
                                            )
                                            .into(),
                                        );
                                    }
                                } else if other.maybe_type_of_class(i_s.db).is_some() {
                                    mismatch = true;
                                    if mismatches < SHOW_MAX_MISMATCHES {
                                        notes.push(
                                            format!(
                                                "ClassVar protocol member {}.{name} can never be \
                                                 matched by a class object",
                                                self.name()
                                            )
                                            .into(),
                                        );
                                    }
                                }
                            }

                            if matches!(lookup_details.attr_kind, AttributeKind::ClassVar)
                               && !protocol_lookup_details.attr_kind.classvar_like()
                               && other.maybe_class(i_s.db).is_some()
                            {
                                mismatch = true;
                                if mismatches < SHOW_MAX_MISMATCHES {
                                    notes.push(
                                        format!(
                                            "Protocol member {}.{name} expected instance variable, \
                                         got class variable",
                                            self.name()
                                        )
                                        .into(),
                                    );
                                }
                            }
                            if protocol_lookup_details
                                .attr_kind
                                .classmethod_or_staticmethod()
                                && !lookup_details.attr_kind.classmethod_or_staticmethod()
                            {
                                mismatch = true;
                                if mismatches < SHOW_MAX_MISMATCHES {
                                    notes.push(
                                        format!(
                                        "Protocol member {}.{name} expected class or static method",
                                        self.name()
                                    )
                                        .into(),
                                    );
                                }
                            }
                            if lookup_details.attr_kind == AttributeKind::AnnotatedAttribute {
                                if let Type::Type(t) = other {
                                    mismatch = true;
                                    if mismatches < SHOW_MAX_MISMATCHES {
                                        notes.push(
                                            format!(
                                            "Only class variables allowed for class object access \
                                             on protocols, {name} is an instance variable of \"{}\"",
                                            t.format_short(i_s.db),
                                        )
                                            .into(),
                                        );
                                    }
                                }
                            }
                            if is_final_mismatch {
                                mismatch = true;
                                if mismatches < SHOW_MAX_MISMATCHES {
                                    notes.push(
                                        format!(
                                        "Protocol member {}.{name} expected settable variable, \
                                         got read-only attribute",
                                        self.name()
                                    )
                                        .into(),
                                    );
                                }
                            }
                        }
                    },
                );
                if let Some(issue) = had_error.take() {
                    if mismatches < SHOW_MAX_MISMATCHES {
                        notes.push(issue.into());
                    }
                    mismatch = true;
                }
                if had_lookup_error {
                    missing_members.push(name);
                }
                if is_call {
                    matcher.ignore_positional_param_names = true;
                }
                mismatches += mismatch as usize;
            }
        }
        if !had_at_least_one_member_with_same_name && !missing_members.is_empty() {
            return Match::new_false();
        }
        if mismatches > SHOW_MAX_MISMATCHES {
            notes.push(
                format!(
                    "    <{} more conflict(s) not shown>",
                    mismatches - SHOW_MAX_MISMATCHES
                )
                .into(),
            );
        }
        let missing_members_empty = missing_members.is_empty();
        if !missing_members_empty
            && protocol_member_count > 1
            && missing_members.len() <= MAX_MISSING_MEMBERS
        {
            let tmp;
            notes.push(
                format!(
                    r#""{}" is missing following "{}" protocol member:"#,
                    match other.maybe_class(i_s.db) {
                        Some(cls) => cls.name(),
                        None => {
                            tmp = other.format_short(i_s.db);
                            tmp.as_ref()
                        }
                    },
                    self.name()
                )
                .into(),
            );
            for name in missing_members {
                notes.push(format!("    {name}").into());
            }
        }
        matcher.ignore_positional_param_names = ignore_positional_param_names_old;
        if notes.is_empty() && missing_members_empty {
            Match::new_true()
        } else {
            Match::False {
                similar: false,
                reason: MismatchReason::ProtocolMismatches {
                    notes: notes.into_boxed_slice(),
                },
            }
        }
    }

    pub fn non_method_protocol_members(&self, db: &Database) -> Vec<String> {
        let mut members = vec![];
        for (mro_index, c) in self.mro_maybe_without_object(db, true) {
            let TypeOrClass::Class(c) = c else { continue };
            let protocol_members = &c.use_cached_class_infos(db).protocol_members;
            for protocol_member in protocol_members.iter() {
                let name_node_ref = NodeRef::new(self.node_ref.file, protocol_member.name_index);
                if !matches!(name_node_ref.as_name().expect_type(), TypeLike::Function(_)) {
                    members.push(name_node_ref.as_code().into())
                }
            }
        }
        members
    }

    pub fn has_customized_enum_new(&self, i_s: &InferenceState) -> bool {
        for (_, c) in self.mro_maybe_without_object(i_s.db, true) {
            let (c, lookup) = c.lookup_symbol(i_s, "__new__");
            if lookup.into_maybe_inferred().is_some() {
                let Some(class) = c else { unreachable!() };
                return class.node_ref.file.file_index
                    != i_s.db.python_state.enum_file().file_index;
            }
        }
        false
    }

    pub fn lookup_assignment(&self, name: &str) -> Option<Assignment<'a>> {
        let i = self.class_storage.class_symbol_table.lookup_symbol(name)?;
        NodeRef::new(self.node_ref.file, i)
            .as_name()
            .maybe_assignment_definition_name()
    }

    pub fn lookup_symbol(&self, i_s: &InferenceState<'db, '_>, name: &str) -> LookupResult {
        match self.class_storage.class_symbol_table.lookup_symbol(name) {
            None => {
                for star_import in self.node_ref.file.star_imports.iter() {
                    if star_import.scope == self.node_ref.node_index {
                        if let Some(result) = self
                            .node_ref
                            .file
                            .inference(i_s)
                            .lookup_name_in_star_import(star_import, name, true)
                        {
                            return result.into_lookup_result(i_s);
                        }
                    }
                }
                LookupResult::None
            }
            Some(node_index) => {
                let new_i_s = i_s.with_class_context(self);
                let inference = self.node_ref.file.inference(&new_i_s);
                let inf = if self
                    .node_ref
                    .file
                    .points
                    .get(node_index)
                    .needs_flow_analysis()
                {
                    inference.infer_name_of_definition_by_index(node_index)
                } else {
                    // If we don't need flow analysis, we need to make sure that the context is not
                    // wrong.
                    /*
                    inference.with_correct_context(true, |_| {
                        // TODO it is currently intentional that we do no use the changed
                        // inference, but this should probably be changed at some point
                        inference.infer_name_of_definition_by_index(node_index)
                    })
                    */
                    inference.infer_name_of_definition_by_index(node_index)
                };
                LookupResult::GotoName {
                    name: PointLink::new(self.node_ref.file.file_index, node_index),
                    inf,
                }
            }
        }
    }

    fn lookup_and_class_and_maybe_ignore_self_internal<T>(
        &self,
        i_s: &InferenceState<'db, '_>,
        name: &str,
        super_count: usize,
        bind: impl FnOnce(LookupResult, TypeOrClass<'a>, MroIndex) -> T,
    ) -> T {
        if name == "__doc__" {
            let t = if self.node().has_docstr() {
                i_s.db.python_state.str_type()
            } else {
                Type::None
            };
            return bind(
                LookupResult::UnknownName(Inferred::from_type(t)),
                TypeOrClass::Class(*self),
                0.into(),
            );
        }
        for (mro_index, c) in self
            .mro_maybe_without_object(i_s.db, self.incomplete_mro(i_s.db))
            .skip(super_count)
        {
            let (_, result) = c.lookup_symbol(i_s, name);
            if !matches!(result, LookupResult::None) {
                return match &c {
                    // TODO why?
                    TypeOrClass::Type(t) if matches!(t.as_ref(), Type::NamedTuple(_)) => bind(
                        result,
                        TypeOrClass::Class(i_s.db.python_state.typing_named_tuple_class()),
                        mro_index,
                    ),
                    _ => bind(result, c.clone(), mro_index),
                };
            }
        }
        bind(
            LookupResult::None,
            TypeOrClass::Type(Cow::Borrowed(&Type::Any(AnyCause::Internal))),
            0.into(),
        )
    }

    pub fn lookup(
        &self,
        i_s: &InferenceState<'db, '_>,
        name: &str,
        options: ClassLookupOptions,
    ) -> LookupDetails<'a> {
        let class_infos = self.use_cached_class_infos(i_s.db);
        let result = if options.kind == LookupKind::Normal {
            if class_infos.class_kind == ClassKind::Enum
                && options.use_descriptors
                && name == "_ignore_"
            {
                return LookupDetails {
                    lookup: LookupResult::None,
                    class: TypeOrClass::Class(*self),
                    attr_kind: AttributeKind::Attribute,
                    mro_index: None,
                };
            }
            self.lookup_and_class_and_maybe_ignore_self_internal(
                i_s,
                name,
                options.super_count,
                |lookup_result, class, mro_index| {
                    let mut attr_kind = AttributeKind::Attribute;
                    let result = lookup_result.and_then(|inf| {
                        let mut bind_class_descriptors = |in_class, class_t, inf: Inferred| {
                            let i_s = i_s.with_class_context(&in_class);
                            let result = inf.bind_class_descriptors(
                                &i_s,
                                self,
                                in_class,
                                class_t,
                                options.add_issue,
                                options.use_descriptors,
                                options.as_type_type,
                            );
                            if let Some((_, k)) = &result {
                                attr_kind = *k;
                            }
                            result.map(|inf| inf.0)
                        };
                        match &class {
                            TypeOrClass::Class(in_class) => {
                                if class_infos.has_slots
                                    && options.use_descriptors
                                    && self.in_slots(i_s.db, name)
                                {
                                    (options.add_issue)(
                                        IssueKind::SlotsConflictWithClassVariableAccess {
                                            name: name.into(),
                                        },
                                    )
                                }
                                if let Some(as_type_type) =
                                    options.as_type_type.filter(|_| mro_index.0 == 0)
                                {
                                    let Type::Type(t) = as_type_type() else {
                                        unreachable!()
                                    };
                                    bind_class_descriptors(
                                        *in_class,
                                        &TypeOrClass::Type(Cow::Owned((*t).clone())),
                                        inf,
                                    )
                                } else {
                                    bind_class_descriptors(*in_class, &class, inf)
                                }
                            }
                            TypeOrClass::Type(t) => match t.as_ref() {
                                Type::Dataclass(d) => {
                                    bind_class_descriptors(d.class(i_s.db), &class, inf)
                                }
                                _ => Some(inf),
                            },
                        }
                    });
                    result.map(|lookup| LookupDetails {
                        class,
                        lookup,
                        attr_kind,
                        mro_index: Some(mro_index),
                    })
                },
            )
        } else {
            None
        };
        if options.avoid_metaclass {
            return result.unwrap_or_else(|| LookupDetails::none());
        }
        match result {
            Some(LookupDetails {
                lookup: LookupResult::None,
                ..
            })
            | None => {
                let metaclass_result = match class_infos.metaclass {
                    MetaclassState::Unknown => LookupDetails::any(AnyCause::Todo),
                    _ => {
                        let instance = Instance::new(class_infos.metaclass(i_s.db), None);
                        instance.lookup(
                            i_s,
                            name,
                            InstanceLookupOptions::new(options.add_issue).with_as_self_instance(
                                options
                                    .as_type_type
                                    .unwrap_or(&|| self.as_type_type(i_s.db)),
                            ),
                        )
                    }
                };
                if matches!(&metaclass_result.lookup, LookupResult::None)
                    && self.incomplete_mro(i_s.db)
                {
                    LookupDetails::any(AnyCause::Todo)
                } else {
                    LookupDetails {
                        class: TypeOrClass::Class(*self),
                        lookup: metaclass_result.lookup,
                        attr_kind: metaclass_result.attr_kind,
                        mro_index: None,
                    }
                }
            }
            Some(result) => result,
        }
    }

    pub fn generics(&self) -> Generics {
        if let Some(type_var_remap) = self.type_var_remap {
            Generics::List(type_var_remap, Some(&self.generics))
        } else {
            self.generics
        }
    }

    pub fn set_correct_generics_if_necessary_for_init_in_superclass(&mut self) {
        if self.type_var_remap.is_some() && matches!(self.generics, Generics::NotDefinedYet) {
            self.generics = Generics::None;
        }
    }

    pub fn needs_generic_remapping_for_attributes(&self, i_s: &InferenceState, t: &Type) -> bool {
        !self.type_vars(i_s).is_empty() || t.has_self_type(i_s.db)
    }

    pub fn nth_type_argument(&self, db: &Database, nth: usize) -> Type {
        let type_vars = self.use_cached_type_vars(db);
        self.generics()
            .nth(db, &type_vars[nth], nth)
            .expect_type_argument()
            .into_owned()
    }

    pub fn nth_param_spec_usage(
        &self,
        db: &'db Database,
        usage: &ParamSpecUsage,
    ) -> Cow<ParamSpecArg> {
        let generic = self
            .generics()
            .nth_usage(db, &TypeVarLikeUsage::ParamSpec(usage.clone()));
        if let Generic::ParamSpecArg(p) = generic {
            p
        } else {
            unreachable!()
        }
    }

    pub fn mro_maybe_without_object(
        &self,
        db: &'db Database,
        without_object: bool,
    ) -> MroIterator<'db, 'a> {
        let class_infos = self.use_cached_class_infos(db);
        if let Some(type_var_remap) = self.type_var_remap {
            if matches!(self.generics, Generics::Self_ { .. } | Generics::None) {
                return Class::new(
                    self.node_ref,
                    self.class_storage,
                    Generics::List(type_var_remap, None),
                    None,
                )
                .mro_maybe_without_object(db, without_object);
            }
            // TODO Do something similar for generics, because otherwise we lose type_var_remap
        }
        MroIterator::new(
            db,
            TypeOrClass::Class(*self),
            self.generics,
            class_infos.mro.iter(),
            without_object
                || self.node_ref == db.python_state.object_node_ref()
                || class_infos.class_kind == ClassKind::Protocol,
        )
    }

    pub fn mro(&self, db: &'db Database) -> MroIterator<'db, 'a> {
        self.mro_maybe_without_object(db, self.node_ref == db.python_state.object_node_ref())
    }

    pub fn class_link_in_mro(&self, i_s: &InferenceState, link: PointLink) -> bool {
        if self.node_ref.as_link() == link {
            return true;
        }
        let class_infos = self.use_cached_class_infos(i_s.db);
        class_infos.mro.iter().any(|b| match &b.type_ {
            Type::Class(c) => link == c.link,
            t => t
                .inner_generic_class(i_s)
                .is_some_and(|c| c.node_ref.as_link() == link),
        })
    }

    pub fn class_in_mro(&self, db: &'db Database, node_ref: NodeRef) -> Option<Class> {
        for (_, type_or_cls) in self.mro(db) {
            if let TypeOrClass::Class(c) = type_or_cls {
                if c.node_ref == node_ref {
                    return Some(c);
                }
            }
        }
        None
    }

    pub fn is_object_class(&self, db: &Database) -> bool {
        self.node_ref == db.python_state.object_node_ref()
    }

    pub fn format(&self, format_data: &FormatData) -> Box<str> {
        let mut result = match format_data.style {
            FormatStyle::Short if !format_data.should_format_qualified(self.node_ref.as_link()) => {
                self.name().to_owned()
            }
            _ => self.qualified_name(format_data.db),
        };
        let type_var_likes = self.type_vars(&InferenceState::new(format_data.db));
        // Format classes that have not been initialized like Foo() or Foo[int] like "Foo".
        if !type_var_likes.is_empty() && !matches!(self.generics, Generics::NotDefinedYet) {
            // Returns something like [str] or [List[int], Set[Any]]
            let strings: Vec<_> = self
                .generics()
                .iter(format_data.db)
                .filter_map(|g| g.format(format_data))
                .collect();
            if strings.is_empty() {
                result += "[()]"
            } else {
                result += &format!("[{}]", strings.join(", "))
            };
        }

        if let Some(class_infos) = self.maybe_cached_class_infos(format_data.db) {
            match &class_infos.class_kind {
                ClassKind::NamedTuple => {
                    let named_tuple = self.maybe_named_tuple_base(format_data.db).unwrap();
                    return named_tuple.format_with_name(format_data, &result, self.generics);
                }
                ClassKind::Tuple if format_data.style == FormatStyle::MypyRevealType => {
                    for (_, type_or_class) in self.mro(format_data.db) {
                        if let TypeOrClass::Type(t) = type_or_class {
                            if let Type::Tuple(tup) = t.as_ref() {
                                if matches!(
                                    tup.args,
                                    TupleArgs::FixedLen(_) | TupleArgs::WithUnpack(_)
                                ) {
                                    return tup.format_with_fallback(
                                        format_data,
                                        &format!(", fallback={result}"),
                                    );
                                }
                            }
                        }
                    }
                }
                _ => (),
            }
        }
        result.into()
    }

    pub fn format_short(&self, db: &Database) -> Box<str> {
        self.format(&FormatData::new_short(db))
    }

    pub fn as_inferred(&self, i_s: &InferenceState) -> Inferred {
        Inferred::from_type(self.as_type_type(i_s.db))
    }

    pub fn generics_as_list(&self, db: &Database) -> ClassGenerics {
        // TODO we instantiate, because we cannot use use_cached_type_vars?
        let type_var_likes = self.type_vars(&InferenceState::new(db));
        match type_var_likes.is_empty() {
            false => match self.generics() {
                Generics::NotDefinedYet => ClassGenerics::List(GenericsList::new_generics(
                    type_var_likes
                        .iter()
                        .map(|t| t.as_any_generic_item())
                        .collect(),
                )),
                Generics::ExpressionWithClassType(file, expr) => {
                    ClassGenerics::ExpressionWithClassType(PointLink::new(
                        file.file_index,
                        expr.index(),
                    ))
                }
                Generics::SlicesWithClassTypes(file, slices) => {
                    ClassGenerics::SlicesWithClassTypes(PointLink::new(
                        file.file_index,
                        slices.index(),
                    ))
                }
                Generics::List(generics, None) => ClassGenerics::List((*generics).clone()),
                generics => ClassGenerics::List(GenericsList::new_generics(
                    generics.iter(db).map(|g| g.into_generic_item(db)).collect(),
                )),
            },
            true => ClassGenerics::None,
        }
    }

    pub fn as_generic_class(&self, db: &Database) -> GenericClass {
        GenericClass {
            link: self.node_ref.as_link(),
            generics: self.generics_as_list(db),
        }
    }

    pub fn as_type(&self, db: &Database) -> Type {
        Type::Class(self.as_generic_class(db))
    }

    pub fn as_type_type(&self, db: &Database) -> Type {
        let class_infos = self.use_cached_class_infos(db);
        Type::Type(if matches!(self.generics, Generics::NotDefinedYet) {
            class_infos
                .undefined_generics_type
                .get_or_init(|| {
                    Rc::new(Type::new_class(
                        self.node_ref.as_link(),
                        ClassGenerics::NotDefinedYet,
                    ))
                })
                .clone()
        } else {
            Rc::new(self.as_type(db))
        })
    }

    pub fn as_type_with_type_vars_for_not_yet_defined_generics(&self, db: &Database) -> Type {
        match self.generics {
            Generics::NotDefinedYet => Class::with_self_generics(db, self.node_ref).as_type(db),
            _ => self.as_type(db),
        }
    }

    fn named_tuple_from_class(&self, i_s: &InferenceState, cls: Class) -> Rc<NamedTuple> {
        let name = self.name_string_slice();
        Rc::new(NamedTuple::new(
            name,
            self.initialize_named_tuple_class_members(i_s, name),
        ))
    }

    fn initialize_named_tuple_class_members(
        &self,
        i_s: &InferenceState,
        name: StringSlice,
    ) -> CallableContent {
        let mut vec = start_namedtuple_params(i_s.db);
        let file = self.node_ref.file;
        find_stmt_named_tuple_types(i_s, file, &mut vec, self.node().block().iter_stmt_likes());
        for (name, index) in self.class_storage.class_symbol_table.iter() {
            if NAMEDTUPLE_PROHIBITED_NAMES.contains(&name) {
                NodeRef::new(self.node_ref.file, *index).add_issue(
                    i_s,
                    IssueKind::NamedTupleInvalidAttributeOverride { name: name.into() },
                )
            }
        }
        let tvls = self.use_cached_type_vars(i_s.db);
        CallableContent::new_simple(
            Some(DbString::StringSlice(name)),
            None,
            self.node_ref.as_link(),
            self.use_cached_type_vars(i_s.db).clone(),
            CallableParams::new_simple(Rc::from(vec)),
            Type::Self_,
        )
    }

    fn initialize_typed_dict_members(&self, i_s: &InferenceState, typed_dict: Rc<TypedDict>) {
        let typed_dict_definition = self.maybe_typed_dict_definition().unwrap();
        let i_s = &i_s.with_class_context(self);
        let mut typed_dict_members = TypedDictMemberGatherer::default();
        if let Some(args) = self.node().arguments() {
            for (i, base) in self
                .use_cached_class_infos(i_s.db)
                .mro
                .iter()
                .rev()
                .filter(|t| t.is_direct_base)
                .enumerate()
            {
                match &base.type_ {
                    Type::TypedDict(td) => {
                        let node_ref =
                            NodeRef::new(self.node_ref.file, args.iter().nth(i).unwrap().index());
                        let Some(super_class_members) = td.maybe_calculated_members(i_s.db) else {
                            let super_cls = Class::from_non_generic_link(i_s.db, td.defined_at);
                            let tdd = super_cls.maybe_typed_dict_definition().unwrap();
                            tdd.deferred_subclass_member_initializations
                                .borrow_mut()
                                .push(typed_dict.clone());
                            debug!(
                                "Defer typed dict member initialization for {:?} after {:?}",
                                self.name(),
                                super_cls.name(),
                            );
                            return;
                        };
                        typed_dict_members.merge(i_s, node_ref, td.members(i_s.db));
                    }
                    _ => (),
                }
            }
        }
        debug!("Start TypedDict members calculation for {:?}", self.name());
        let file = self.node_ref.file;
        find_stmt_typed_dict_types(
            i_s,
            file,
            &mut typed_dict_members,
            self.node().block().iter_stmt_likes(),
            typed_dict_definition.total,
        );
        debug!("End TypedDict members calculation for {:?}", self.name());
        typed_dict.late_initialization_of_members(typed_dict_members.into_boxed_slice());
        loop {
            let mut borrowed = typed_dict_definition
                .deferred_subclass_member_initializations
                .borrow_mut();
            let Some(deferred) = borrowed.pop() else {
                break;
            };
            drop(borrowed);
            let cls = Class::from_non_generic_link(i_s.db, deferred.defined_at);
            debug!(
                "Calculate TypedDict members for deferred subclass {:?}",
                cls.name()
            );
            cls.initialize_typed_dict_members(i_s, deferred)
        }
    }

    fn enum_members(&self, i_s: &InferenceState) -> Box<[EnumMemberDefinition]> {
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
                        name_node_ref.add_issue(i_s, IssueKind::EnumMembersAttributeOverwritten)
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
                debug_assert_eq!(point.specific(), Specific::NameOfNameDef);
                if point.node_index() != name_index {
                    NodeRef::new(self.node_ref.file, point.node_index()).add_issue(
                        i_s,
                        IssueKind::EnumReusedMemberName {
                            enum_name: self.name().into(),
                            member_name: name_node_ref.as_code().into(),
                        },
                    )
                }
                let name = name_node_ref.as_name();
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
                    debug_assert_eq!(p.maybe_specific(), Some(Specific::NameOfNameDef));
                    if p.node_index() != name_index {
                        let mut has_overload = false;
                        let mut has_non_overload = false;
                        for index in MultiDefinitionIterator::new(&file.points, name_index) {
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

    pub fn find_relevant_constructor(
        &self,
        i_s: &InferenceState<'db, '_>,
    ) -> NewOrInitConstructor<'_> {
        let (__init__, init_class, init_mro_index) = self
            .lookup_and_class_and_maybe_ignore_self_internal(
                i_s,
                "__init__",
                0,
                |lookup, cls, mro_index| (lookup, cls, mro_index),
            );
        self.lookup_and_class_and_maybe_ignore_self_internal(
            i_s,
            "__new__",
            0,
            |__new__, cls, new_mro_index| {
                // This is just a weird heuristic Mypy uses, because the type system itself is very unclear
                // what to do if both __new__ and __init__ are present. So just only use __new__ if it's in
                // a lower MRO than an __init__.
                let is_new = new_mro_index < init_mro_index;
                NewOrInitConstructor {
                    is_new,
                    // TODO this should not be bound if is_new = false
                    constructor: match is_new {
                        false => __init__,
                        true => __new__
                            .and_then(|inf| {
                                Some(inf.bind_new_descriptors(i_s, self, cls.as_maybe_class()))
                            })
                            .unwrap(),
                    },
                    init_class,
                }
            },
        )
    }

    pub(crate) fn execute(
        &self,
        i_s: &InferenceState<'db, '_>,
        args: &dyn Args<'db>,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError,
        from_type_type: bool,
    ) -> Inferred {
        if self.node_ref == i_s.db.python_state.dict_node_ref() {
            // This is a special case where we intercept the call to dict(..) when used with
            // TypedDict.
            if let Some(file) = args.in_file() {
                if let Some(inf) = file
                    .inference(i_s)
                    .infer_dict_call_from_context(args, result_context)
                {
                    return inf;
                }
            }
        }
        match self.execute_and_return_generics(
            i_s,
            args,
            result_context,
            on_type_error,
            from_type_type,
        ) {
            ClassExecutionResult::ClassGenerics(generics) => {
                let result = Inferred::from_type(Type::Class(GenericClass {
                    link: self.node_ref.as_link(),
                    generics,
                }));
                debug!("Class execute: {}", result.format_short(i_s));
                if self.node_ref == i_s.db.python_state.bare_type_node_ref() {
                    if let Some(first_arg) =
                        args.maybe_single_positional_arg(i_s, &mut ResultContext::Unknown)
                    {
                        return execute_bare_type(i_s, first_arg);
                    }
                }
                result
            }
            ClassExecutionResult::Inferred(inf) => inf,
        }
    }

    pub(crate) fn execute_and_return_generics(
        &self,
        i_s: &InferenceState<'db, '_>,
        args: &dyn Args<'db>,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError,
        from_type_type: bool,
    ) -> ClassExecutionResult {
        let had_type_error = Cell::new(false);
        let d = |_: &FunctionOrCallable, _: &Database| {
            had_type_error.set(true);
            Some(format!("\"{}\"", self.name()))
        };
        let on_type_error = on_type_error.with_custom_generate_diagnostic_string(&d);

        let class_infos = self.use_cached_class_infos(i_s.db);
        if !class_infos.abstract_attributes.is_empty()
            && !class_infos.incomplete_mro
            && matches!(self.generics, Generics::NotDefinedYet)
        {
            args.add_issue(
                i_s,
                IssueKind::CannotInstantiateAbstractClass {
                    name: self.name().into(),
                    abstract_attributes: class_infos.abstract_attributes.clone(),
                },
            )
        }
        match &class_infos.class_kind {
            ClassKind::Enum if self.node_ref.as_link() != i_s.db.python_state.enum_auto_link() => {
                // For whatever reason, auto is special, because it is somehow defined as an enum as
                // well, which is very weird.
                let metaclass =
                    Class::from_non_generic_link(i_s.db, i_s.db.python_state.enum_meta_link())
                        .instance();
                let call = metaclass
                    .type_lookup(i_s, |issue| args.add_issue(i_s, issue), "__call__")
                    .into_inferred()
                    .execute_with_details(i_s, args, result_context, on_type_error);
                if had_type_error.get() {
                    return ClassExecutionResult::Inferred(Inferred::new_any_from_error());
                }
                return ClassExecutionResult::Inferred(
                    execute_functional_enum(i_s, *self, args, result_context)
                        .unwrap_or_else(Inferred::new_invalid_type_definition),
                );
            }
            _ => (),
        }

        let constructor = self.find_relevant_constructor(i_s);
        if constructor.is_new {
            let result = constructor
                .constructor
                .into_inferred()
                .execute_with_details(i_s, args, result_context, on_type_error)
                .as_type(i_s);
            // Only subclasses of the current class are valid, otherwise return the current
            // class. Diagnostics will care about these cases and raise errors when needed.
            if !result.is_any()
                && self
                    .as_type(i_s.db)
                    .is_simple_super_type_of(i_s, &result)
                    .bool()
            {
                return ClassExecutionResult::Inferred(Inferred::from_type(result));
            } else if matches!(self.generics, Generics::NotDefinedYet)
                && !self.type_vars(i_s).is_empty()
            {
                // This is a bit special, because in some cases like reversed() __new__ returns a
                // super class of the current class. We use that super class to infer the generics
                // that are relevant in the current class.
                let mut matcher = Matcher::new_class_matcher(i_s, *self);
                Self::with_self_generics(i_s.db, self.node_ref)
                    .as_type(i_s.db)
                    .is_sub_type_of(i_s, &mut matcher, &result);
                return ClassExecutionResult::ClassGenerics(ClassGenerics::List(
                    matcher.into_type_arguments(i_s.db).1.unwrap(),
                ));
            } else {
                return ClassExecutionResult::ClassGenerics(self.generics_as_list(i_s.db));
            }
        }

        debug!("Check {} __init__", self.name());
        debug_indent(|| {
            self.type_check_dunder_init_func(
                i_s,
                constructor.constructor,
                constructor.init_class,
                args,
                result_context,
                on_type_error,
                from_type_type,
            )
        })
    }

    pub(crate) fn simple_lookup(
        &self,
        i_s: &InferenceState,
        add_issue: impl Fn(IssueKind),
        name: &str,
    ) -> LookupResult {
        self.lookup(i_s, name, ClassLookupOptions::new(&add_issue))
            .lookup
    }

    pub fn qualified_name(&self, db: &Database) -> String {
        self.class_storage
            .parent_scope
            .qualified_name(db, self.node_ref, self.name())
    }

    pub fn name(&self) -> &'a str {
        self.node().name().as_str()
    }

    pub fn get_item(
        &self,
        i_s: &InferenceState,
        slice_type: &SliceType,
        result_context: &mut ResultContext,
    ) -> Inferred {
        match self.use_cached_class_infos(i_s.db).metaclass {
            MetaclassState::Some(_) => {
                if let Some(__getitem__) = self
                    .lookup(
                        i_s,
                        "__getitem__",
                        ClassLookupOptions::new(&|issue| {
                            slice_type.as_node_ref().add_issue(i_s, issue)
                        })
                        .with_kind(LookupKind::OnlyType),
                    )
                    .lookup
                    .into_maybe_inferred()
                {
                    return __getitem__.execute(i_s, &slice_type.as_args(*i_s));
                }
            }
            MetaclassState::Unknown => return Inferred::new_any_from_error(),
            MetaclassState::None => (),
        }
        slice_type
            .file
            .inference(i_s)
            .compute_type_application_on_class(
                *self,
                *slice_type,
                matches!(result_context, ResultContext::AssignmentNewDefinition),
            )
    }

    pub fn in_slots(&self, db: &Database, name: &str) -> bool {
        for (_, type_or_class) in self.mro_maybe_without_object(db, true) {
            match type_or_class {
                TypeOrClass::Type(_) => (),
                TypeOrClass::Class(class) => {
                    if let Some(slots) = &class.class_storage.slots {
                        if slots.iter().any(|slot| {
                            let s = slot.as_str(db);
                            s == name
                        }) {
                            return true;
                        }
                    }
                }
            }
        }
        false
    }

    fn add_issue_on_name(&self, i_s: &InferenceState, issue: IssueKind) {
        NodeRef::new(self.node_ref.file, self.node().name().index()).add_issue(i_s, issue)
    }

    pub(crate) fn check_slots(
        &self,
        i_s: &InferenceState,
        add_issue: impl Fn(IssueKind),
        name: &str,
    ) {
        for (_, type_or_class) in self.mro_maybe_without_object(i_s.db, true) {
            match type_or_class {
                TypeOrClass::Type(_) => (),
                TypeOrClass::Class(class) => {
                    let Some(slots) = &class.class_storage.slots else {
                        return;
                    };
                    if class.lookup_symbol(i_s, "__setattr__").is_some() {
                        return;
                    }
                    if slots.iter().any(|slot| {
                        let s = slot.as_str(i_s.db);
                        s == name || s == "__dict__"
                    }) {
                        return;
                    }
                    if let Some(on_class) = class.lookup_symbol(i_s, name).into_maybe_inferred() {
                        if on_class
                            .as_cow_type(&i_s.with_class_context(&class))
                            .is_func_or_overload()
                        {
                            // Adds IssueType::CannotAssignToAMethod in other places.
                            return;
                        }
                    }
                }
            }
        }
        add_issue(IssueKind::AssigningToNameOutsideOfSlots {
            name: name.into(),
            class: self.qualified_name(i_s.db).into(),
        })
    }

    pub(crate) fn check_self_definition(
        &self,
        i_s: &InferenceState,
        add_issue: impl Fn(IssueKind),
        name: &str,
    ) {
        self.lookup_and_class_and_maybe_ignore_self_internal(i_s, name, 0, |lookup, _, _| {
            if let Some(inf) = lookup.into_maybe_inferred() {
                if inf.maybe_saved_specific(i_s.db)
                    == Some(Specific::AnnotationOrTypeCommentClassVar)
                {
                    add_issue(IssueKind::CannotAssignToClassVarViaInstance { name: name.into() })
                } else if inf.as_cow_type(i_s).is_func_or_overload_not_any_callable() {
                    // See testSlotsAssignmentWithMethodReassign
                    //add_issue(IssueType::CannotAssignToAMethod);
                }
            }
        });
        self.check_slots(i_s, add_issue, name)
    }

    pub fn maybe_named_tuple_base(&self, db: &'a Database) -> Option<Rc<NamedTuple>> {
        if self.use_cached_class_infos(db).class_kind == ClassKind::NamedTuple {
            for (_, base) in self.mro(db) {
                if let TypeOrClass::Type(base) = base {
                    if let Type::NamedTuple(named_tuple) = base.as_ref() {
                        return Some(named_tuple.clone());
                    }
                }
            }
            unreachable!()
        }
        None
    }

    pub fn maybe_tuple_base(&self, db: &Database) -> Option<Rc<Tuple>> {
        match self.use_cached_class_infos(db).class_kind {
            ClassKind::NamedTuple | ClassKind::Tuple => {
                for (_, base) in self.mro(db) {
                    if let TypeOrClass::Type(base) = base {
                        return Some(match base.as_ref() {
                            Type::NamedTuple(named_tuple) => named_tuple.as_tuple(),
                            Type::Tuple(tup) => tup.clone(),
                            _ => continue,
                        });
                    }
                }
                unreachable!()
            }
            _ => None,
        }
    }

    pub fn maybe_dataclass(&self, db: &Database) -> Option<Rc<Dataclass>> {
        // TODO this should probably not be needed.
        match self
            .maybe_cached_class_infos(db)?
            .undefined_generics_type
            .get()?
            .as_ref()
        {
            Type::Dataclass(d) => Some(d.clone()),
            _ => None,
        }
    }

    pub fn maybe_typed_dict(&self) -> Option<Rc<TypedDict>> {
        self.maybe_typed_dict_definition()
            .map(|tdd| tdd.typed_dict())
    }

    pub fn maybe_typed_dict_definition(&self) -> Option<&TypedDictDefinition> {
        NodeRef::new(self.node_ref.file, self.node().name_def().index())
            .complex()
            .and_then(|c| match c {
                ComplexPoint::TypedDictDefinition(tdd) => Some(tdd),
                _ => None,
            })
    }
}

impl fmt::Debug for Class<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("Class")
            .field("file_index", &self.node_ref.file.file_index)
            .field("node_index", &self.node_ref.node_index)
            .field("name", &self.name())
            .field("generics", &self.generics)
            .field("type_var_remap", &self.type_var_remap)
            .finish()
    }
}

pub enum ClassExecutionResult {
    ClassGenerics(ClassGenerics),
    Inferred(Inferred),
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

fn to_base_kind(i_s: &InferenceState, t: &Type) -> BaseKind {
    match t {
        Type::Class(c) => BaseKind::Class(c.link),
        Type::Type(_) => BaseKind::Type,
        Type::Tuple(tup) => BaseKind::Tuple(tup.clone()),
        Type::Dataclass(d) => BaseKind::Dataclass(d.class.link),
        Type::TypedDict(d) => BaseKind::TypedDict(d.clone()),
        Type::NamedTuple(nt) => BaseKind::NamedTuple(nt.clone()),
        Type::Enum(_) => BaseKind::Enum,
        Type::NewType(n) => to_base_kind(i_s, n.type_(i_s)),
        _ => unreachable!("{t:?}"),
    }
}

#[derive(Clone)]
struct BaseToBeAdded<'a> {
    t: Cow<'a, Type>,
    needs_remapping: bool,
}

pub fn linearize_mro_and_return_linearizable(
    i_s: &InferenceState,
    bases: &[Type],
) -> (Box<[BaseClass]>, bool) {
    let mut mro: Vec<BaseClass> = vec![];

    let object = i_s.db.python_state.object_type();
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
                        .replace_type_var_likes(i_s.db, &mut |usage| {
                            Some(match &bases[base_index] {
                                Type::Tuple(tup) => tup
                                    .class(i_s.db)
                                    .generics
                                    .nth_usage(i_s.db, &usage)
                                    .into_generic_item(i_s.db),
                                Type::NamedTuple(n) => n
                                    .as_tuple_ref()
                                    .class(i_s.db)
                                    .generics
                                    .nth_usage(i_s.db, &usage)
                                    .into_generic_item(i_s.db),
                                Type::Class(GenericClass {
                                    generics: ClassGenerics::List(generics),
                                    ..
                                }) => generics[usage.index()].clone(),
                                // Very rare and therefore a separate case.
                                Type::Class(c) => c
                                    .class(i_s.db)
                                    .generics
                                    .nth_usage(i_s.db, &usage)
                                    .into_generic_item(i_s.db),
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
                Type::Class(c) => Some(c.class(i_s.db)),
                Type::Dataclass(d) => Some(d.class.class(i_s.db)),
                Type::Tuple(tup) => {
                    let cls = tup.class(i_s.db);
                    additional_type = Some(cls.as_type(i_s.db));
                    Some(cls)
                }
                Type::NamedTuple(nt) => {
                    let cls = nt.as_tuple_ref().class(i_s.db);
                    additional_type = Some(cls.as_type(i_s.db));
                    Some(cls)
                }
                _ => None,
            };
            let super_classes = if let Some(cls) = generic_class {
                let cached_class_infos = cls.use_cached_class_infos(i_s.db);
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
                    base_bases.clone().skip(1).any(|(_, other)| {
                        to_base_kind(i_s, &candidate.t) == to_base_kind(i_s, &other.t)
                    })
                });
                if !conflicts {
                    for base_bases in base_iterators.iter_mut() {
                        base_bases.next_if(|(_, next)| {
                            to_base_kind(i_s, &candidate.t) == to_base_kind(i_s, &next.t)
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

fn add_inconsistency_issue(i_s: &InferenceState, class: &Class) {
    NodeRef::new(
        class.node_ref.file,
        class.node().arguments().unwrap().index(),
    )
    .add_issue(
        i_s,
        IssueKind::InconsistentMro {
            name: class.name().into(),
        },
    );
}

pub struct MroIterator<'db, 'a> {
    db: &'db Database,
    generics: Generics<'a>,
    pub class: Option<TypeOrClass<'a>>,
    iterator: std::slice::Iter<'a, BaseClass>,
    mro_index: u32,
    pub returned_object: bool,
}

impl<'db, 'a> MroIterator<'db, 'a> {
    pub fn new(
        db: &'db Database,
        class: TypeOrClass<'a>,
        generics: Generics<'a>,
        iterator: std::slice::Iter<'a, BaseClass>,
        returned_object: bool,
    ) -> Self {
        Self {
            db,
            generics,
            class: Some(class),
            iterator,
            mro_index: 0,
            returned_object,
        }
    }
}

#[derive(Debug, Clone)]
pub enum TypeOrClass<'a> {
    Type(Cow<'a, Type>),
    Class(Class<'a>),
}

impl<'a> TypeOrClass<'a> {
    pub fn lookup_symbol<'db: 'a>(
        &'a self,
        i_s: &InferenceState<'db, '_>,
        name: &str,
    ) -> (Option<Class<'a>>, LookupResult) {
        match self {
            Self::Class(class) => (Some(*class), class.lookup_symbol(i_s, name)),
            Self::Type(t) => t.lookup_symbol(i_s, name),
        }
    }

    pub fn name(&self, db: &'a Database) -> &str {
        match self {
            Self::Class(class) => class.name(),
            Self::Type(t) => match t.as_ref() {
                Type::Dataclass(d) => d.class(db).name(),
                Type::NamedTuple(nt) => nt.name(db),
                Type::Tuple(_) => "Tuple",
                _ => unreachable!(),
            },
        }
    }

    pub fn qualified_name(&self, db: &'a Database) -> String {
        match self {
            Self::Class(class) => class.qualified_name(db),
            Self::Type(t) => match t.as_ref() {
                Type::Dataclass(d) => d.class(db).qualified_name(db),
                Type::NamedTuple(nt) => nt.qualified_name(db),
                _ => self.name(db).into(),
            },
        }
    }

    pub fn format(&self, db: &FormatData) -> Box<str> {
        match self {
            Self::Class(class) => class.format(db),
            Self::Type(t) => t.format(db),
        }
    }

    #[inline]
    pub fn as_maybe_class(&self) -> Option<Class<'a>> {
        match self {
            TypeOrClass::Class(c) => Some(*c),
            TypeOrClass::Type(_) => None,
        }
    }

    pub fn as_base_class<'x>(&'x self, db: &'x Database, cls: &Class<'x>) -> Option<Class> {
        match self {
            TypeOrClass::Class(c) => Some(*c),
            TypeOrClass::Type(t) => match t.as_ref() {
                Type::Dataclass(d) => Some(d.as_base_class(db, cls.generics)),
                _ => None,
            },
        }
    }

    pub fn is_object(&self, db: &Database) -> bool {
        matches!(self, TypeOrClass::Class(c) if c.node_ref == db.python_state.object_node_ref())
    }

    pub fn is_frozen_dataclass(&self) -> bool {
        match self {
            Self::Type(t) => match t.as_ref() {
                Type::Dataclass(d) => d.options.frozen,
                _ => false,
            },
            Self::Class(_) => false,
        }
    }
    pub fn originates_in_builtins_or_typing(&self, db: &Database) -> bool {
        match self {
            TypeOrClass::Class(c) => {
                let class_file_index = c.node_ref.file_index();
                class_file_index == db.python_state.builtins().file_index
                    || c.node_ref.file_index() == db.python_state.typing().file_index
            }
            TypeOrClass::Type(_) => true,
        }
    }

    pub fn as_type(&self, db: &Database) -> Type {
        match self {
            TypeOrClass::Class(c) => c.as_type(db),
            TypeOrClass::Type(t) => t.clone().into_owned(),
        }
    }
}

impl<'db: 'a, 'a> Iterator for MroIterator<'db, 'a> {
    type Item = (MroIndex, TypeOrClass<'a>);

    fn next(&mut self) -> Option<Self::Item> {
        if self.class.is_some() {
            self.mro_index += 1;
            Some((MroIndex(0), self.class.take().unwrap()))
        } else if let Some(c) = self.iterator.next() {
            let r = Some((
                MroIndex(self.mro_index),
                apply_generics_to_base_class(self.db, &c.type_, self.generics),
            ));
            self.mro_index += 1;
            r
        } else if !self.returned_object {
            self.returned_object = true;
            Some((
                MroIndex(self.mro_index),
                TypeOrClass::Class(self.db.python_state.object_class()),
            ))
        } else {
            None
        }
    }
}

impl<'db: 'a, 'a> DoubleEndedIterator for MroIterator<'db, 'a> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if !self.returned_object {
            self.returned_object = true;
            Some((
                MroIndex(self.mro_index),
                TypeOrClass::Class(self.db.python_state.object_class()),
            ))
        } else if let Some(c) = self.iterator.next_back() {
            let r = Some((
                MroIndex(self.mro_index),
                apply_generics_to_base_class(self.db, &c.type_, self.generics),
            ));
            self.mro_index += 1;
            r
        } else if self.class.is_some() {
            self.mro_index += 1;
            Some((MroIndex(0), self.class.take().unwrap()))
        } else {
            None
        }
    }
}

fn apply_generics_to_base_class<'a>(
    db: &'a Database,
    t: &'a Type,
    generics: Generics<'a>,
) -> TypeOrClass<'a> {
    match &t {
        Type::Class(c) => {
            TypeOrClass::Class(match &c.generics {
                ClassGenerics::List(g) => {
                    if matches!(generics, Generics::Self_ { .. }) {
                        // Self generics imply that there is no remapping of generics necessary. We can
                        // therefore simply use the class in the mro.
                        c.class(db)
                    } else {
                        Class::from_position(NodeRef::from_link(db, c.link), generics, Some(g))
                    }
                }
                ClassGenerics::None => {
                    Class::from_position(NodeRef::from_link(db, c.link), generics, None)
                }
                _ => unreachable!(),
            })
        }
        // TODO is this needed?
        //Type::RecursiveType(r) if matches!(r.origin(db), RecursiveTypeOrigin::Class(_)) => TypeOrClass::Class(Class::from_position(NodeRef::from_link(db, r.link), generics, r.generics.as_ref())),
        _ if matches!(generics, Generics::None | Generics::NotDefinedYet) => {
            TypeOrClass::Type(Cow::Borrowed(t))
        }
        _ => {
            let new_t = t.replace_type_var_likes_and_self(
                db,
                &mut |usage| Some(generics.nth_usage(db, &usage).into_generic_item(db)),
                &|| None,
            );
            TypeOrClass::Type(new_t.map(Cow::Owned).unwrap_or_else(|| Cow::Borrowed(t)))
        }
    }
}

fn find_stmt_named_tuple_types(
    i_s: &InferenceState,
    file: &PythonFile,
    vec: &mut Vec<CallableParam>,
    stmts: StmtLikeIterator,
) {
    for stmt_like in stmts {
        match stmt_like.node {
            StmtLikeContent::Assignment(assignment) => match assignment.unpack() {
                AssignmentContent::WithAnnotation(Target::Name(name), annot, default) => {
                    if default.is_none() && vec.last().is_some_and(|last| last.has_default) {
                        NodeRef::new(file, assignment.index())
                            .add_issue(i_s, IssueKind::NamedTupleNonDefaultFieldFollowsDefault);
                        continue;
                    }
                    file.inference(i_s)
                        .ensure_cached_named_tuple_annotation(annot);
                    let t = use_cached_annotation_type(i_s.db, file, annot).into_owned();
                    if name.as_code().starts_with('_') {
                        NodeRef::new(file, name.index()).add_issue(
                            i_s,
                            IssueKind::NamedTupleNameCannotStartWithUnderscore {
                                field_name: name.as_code().into(),
                            },
                        )
                    } else {
                        vec.push(CallableParam {
                            type_: ParamType::PositionalOrKeyword(t),
                            has_default: default.is_some(),
                            name: Some(StringSlice::from_name(file.file_index, name.name()).into()),
                        })
                    }
                }
                _ => NodeRef::new(file, assignment.index())
                    .add_issue(i_s, IssueKind::InvalidStmtInNamedTuple),
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
                .add_issue(i_s, IssueKind::InvalidStmtInNamedTuple),
        }
    }
}

fn find_stmt_typed_dict_types(
    i_s: &InferenceState,
    file: &PythonFile,
    vec: &mut TypedDictMemberGatherer,
    stmt_likes: StmtLikeIterator,
    total: bool,
) {
    for stmt_like in stmt_likes {
        match stmt_like.node {
            StmtLikeContent::Assignment(assignment) => match assignment.unpack() {
                AssignmentContent::WithAnnotation(Target::Name(name_def), annot, right_side) => {
                    if right_side.is_some() {
                        NodeRef::new(file, assignment.index())
                            .add_issue(i_s, IssueKind::TypedDictInvalidMemberRightSide);
                    }
                    if let Err(issue) = vec.add(
                        i_s.db,
                        file.inference(i_s).compute_class_typed_dict_member(
                            StringSlice::from_name(file.file_index, name_def.name()),
                            annot,
                            total,
                        ),
                    ) {
                        NodeRef::new(file, assignment.index()).add_issue(i_s, issue);
                    }
                }
                AssignmentContent::Normal(targets, _) => {
                    NodeRef::new(file, assignment.index())
                        .add_issue(i_s, IssueKind::TypedDictInvalidMember);
                    for target in targets {
                        if let Target::Name(name_def) = target {
                            // Add those names regardless, because an error was already added.
                            vec.add(
                                i_s.db,
                                TypedDictMember {
                                    type_: Type::Any(AnyCause::Todo),
                                    required: true,
                                    name: StringSlice::from_name(file.file_index, name_def.name()),
                                },
                            )
                            .ok();
                        }
                    }
                }
                _ => NodeRef::new(file, assignment.index())
                    .add_issue(i_s, IssueKind::TypedDictInvalidMember),
            },
            StmtLikeContent::Error(_)
            | StmtLikeContent::PassStmt(_)
            | StmtLikeContent::StarExpressions(_) => (),
            s => NodeRef::new(file, stmt_like.parent_index)
                .add_issue(i_s, IssueKind::TypedDictInvalidMember),
        }
    }
}

fn add_protocol_mismatch(
    i_s: &InferenceState,
    notes: &mut Vec<Box<str>>,
    name: &str,
    t1: &Type,
    t2: &Type,
    full1: &Type,
    full2: &Type,
) {
    match (full1, full2) {
        (
            Type::Callable(_) | Type::FunctionOverload(_),
            Type::Callable(_) | Type::FunctionOverload(_) | Type::Type(_),
        ) => {
            notes.push("    Expected:".into());
            let c1 = full1.maybe_callable(i_s).unwrap();
            let c2 = full2.maybe_callable(i_s).unwrap();
            format_callable_like(i_s.db, notes, &c1, &c2);
            notes.push("    Got:".into());
            format_callable_like(i_s.db, notes, &c2, &c1);
        }
        _ => {
            let ErrorStrs { got, expected } = format_got_expected(i_s.db, t2, t1);
            notes.push(format!(r#"    {name}: expected "{expected}", got "{got}""#).into())
        }
    }
}

fn protocol_conflict_note(db: &Database, other: &Type) -> Box<str> {
    match other {
        Type::Module(file_index) => format!(
            "Following member(s) of Module \"{}\" have conflicts:",
            db.loaded_python_file(*file_index).qualified_name(db)
        ),
        Type::Type(t) => format!(
            "Following member(s) of \"{}\" have conflicts:",
            t.format_short(db)
        ),
        _ => format!(
            "Following member(s) of \"{}\" have conflicts:",
            other.format_short(db)
        ),
    }
    .into()
}

fn join_abstract_attributes(db: &Database, abstract_attributes: &[PointLink]) -> Box<str> {
    join_with_commas(
        abstract_attributes
            .iter()
            .map(|&l| format!("\"{}\"", NodeRef::from_link(db, l).as_code())),
    )
    .into()
}

fn format_callable_like(
    db: &Database,
    notes: &mut Vec<Box<str>>,
    c: &CallableLike,
    other: &CallableLike,
) {
    let other_had_first_annotation = other.had_first_self_or_class_annotation();
    let prefix = "        ";
    let format_callable = |c: &CallableContent| {
        format!(
            "{prefix}{}",
            c.format_pretty_detailed(
                &FormatData::new_short(db),
                !c.kind.had_first_self_or_class_annotation() && !other_had_first_annotation,
                false,
            )
        )
    };

    match c {
        CallableLike::Callable(c) => notes.push(format_callable(c).into()),
        CallableLike::Overload(o) => {
            for c in o.iter_functions() {
                notes.push(format!("{prefix}@overload").into());
                notes.push(format_callable(c).into());
            }
        }
    }
}

fn init_as_callable(
    i_s: &InferenceState,
    cls: Class,
    inf: Inferred,
    mut init_class: TypeOrClass,
) -> Option<CallableLike> {
    let cls = if matches!(cls.generics(), Generics::NotDefinedYet) {
        // Because of this, generics are not remapped more than the type_var_remap
        if let TypeOrClass::Class(init_class) = &mut init_class {
            init_class.generics = Generics::None;
        }
        Class::with_self_generics(i_s.db, cls.node_ref)
    } else {
        cls
    };
    let init_class = init_class.as_maybe_class();
    let callable = if let Some(c) = init_class {
        let i_s = &i_s.with_class_context(&c);
        inf.as_cow_type(i_s).maybe_callable(i_s)
    } else {
        inf.as_cow_type(i_s).maybe_callable(i_s)
    };
    let to_callable = |c: &CallableContent| {
        // Since __init__ does not have a return, we need to check the params
        // of the __init__ functions and the class as a return type separately.
        c.remove_first_positional_param().map(|mut c| {
            let self_ = cls.as_type(i_s.db);
            let needs_type_var_remap = init_class
                .is_some_and(|c| !c.type_vars(i_s).is_empty() && c.node_ref != cls.node_ref);

            // If the __init__ comes from a super class, we need to fetch the generics that
            // are relevant for our class.
            if c.has_self_type(i_s.db) || needs_type_var_remap {
                c = c.replace_type_var_likes_and_self_inplace(
                    i_s.db,
                    &mut |usage| {
                        if needs_type_var_remap {
                            if let Some(func_class) = init_class {
                                if let Some(result) = maybe_class_usage(i_s.db, &func_class, &usage)
                                {
                                    return Some(result);
                                }
                            }
                        }
                        None
                    },
                    &|| Some(self_.clone()),
                )
            }
            c.return_type = self_;

            // Now we have two sets of generics, the generics for the class and the
            // generics for the __init__ function. We merge those and then set the proper
            // ids for the type vars.
            let class_type_vars = cls.type_vars(i_s);
            if class_type_vars.is_empty() {
                c.type_vars = class_type_vars.clone();
            } else {
                let mut tv_vec = class_type_vars.as_vec();
                tv_vec.extend(c.type_vars.iter().cloned());
                c.type_vars = TypeVarLikes::from_vec(tv_vec);
            }
            let c_defined_at = c.defined_at;
            if !c.type_vars.is_empty() {
                c = c.replace_type_var_likes_and_self_inplace(
                    i_s.db,
                    &mut |mut usage| {
                        let in_def = usage.in_definition();
                        if cls.node_ref.as_link() == in_def {
                            usage.update_in_definition_and_index(c_defined_at, usage.index());
                        } else if c_defined_at == in_def {
                            usage.update_in_definition_and_index(
                                c_defined_at,
                                (class_type_vars.len() + usage.index().as_usize()).into(),
                            )
                        } else {
                            return None;
                        }
                        Some(usage.into_generic_item())
                    },
                    &|| unreachable!("was already replaced above"),
                );
            }
            Rc::new(c)
        })
    };
    callable.and_then(|callable_like| match callable_like {
        CallableLike::Callable(c) => to_callable(&c).map(CallableLike::Callable),
        CallableLike::Overload(callables) => {
            let funcs: Box<_> = callables
                .iter_functions()
                .filter_map(|c| to_callable(c))
                .collect();
            match funcs.len() {
                0 => None,
                1 => Some(CallableLike::Callable(
                    funcs.into_vec().into_iter().next().unwrap(),
                )),
                _ => Some(CallableLike::Overload(FunctionOverload::new(funcs))),
            }
        }
    })
}

pub struct NewOrInitConstructor<'a> {
    // A data structure to show wheter __init__ or __new__ is the relevant constructor for a class
    constructor: LookupResult,
    init_class: TypeOrClass<'a>,
    is_new: bool,
}

impl NewOrInitConstructor<'_> {
    pub fn maybe_callable(self, i_s: &InferenceState, cls: Class) -> Option<CallableLike> {
        let inf = self.constructor.into_inferred();
        if self.is_new {
            inf.as_cow_type(i_s).maybe_callable(i_s)
        } else {
            init_as_callable(i_s, cls, inf, self.init_class)
        }
    }

    fn into_type(self, i_s: &InferenceState, cls: Class) -> Option<Type> {
        self.maybe_callable(i_s, cls).map(|c| c.into())
    }
}

pub fn start_namedtuple_params(db: &Database) -> Vec<CallableParam> {
    vec![CallableParam {
        type_: ParamType::PositionalOnly(db.python_state.type_of_self.clone()),
        has_default: false,
        name: None,
    }]
}

pub struct ClassLookupOptions<'x> {
    add_issue: &'x dyn Fn(IssueKind),
    kind: LookupKind,
    use_descriptors: bool,
    super_count: usize,
    avoid_metaclass: bool,
    as_type_type: Option<&'x dyn Fn() -> Type>,
}

impl<'x> ClassLookupOptions<'x> {
    pub(crate) fn new(add_issue: &'x dyn Fn(IssueKind)) -> Self {
        Self {
            add_issue,
            kind: LookupKind::Normal,
            use_descriptors: true,
            super_count: 0,
            avoid_metaclass: false,
            as_type_type: None,
        }
    }

    pub fn with_ignore_self(mut self) -> Self {
        self.super_count = 1;
        self
    }

    pub fn with_as_type_type(mut self, as_type_type: &'x dyn Fn() -> Type) -> Self {
        self.as_type_type = Some(as_type_type);
        self
    }

    pub fn without_descriptors(mut self) -> Self {
        self.use_descriptors = false;
        self
    }

    pub fn with_kind(mut self, kind: LookupKind) -> Self {
        self.kind = kind;
        self
    }

    pub fn with_super_count(mut self, super_count: usize) -> Self {
        self.super_count = super_count;
        self
    }

    pub fn with_avoid_metaclass(mut self) -> Self {
        self.avoid_metaclass = true;
        self
    }
}

fn execute_bare_type<'db>(i_s: &InferenceState<'db, '_>, first_arg: Inferred) -> Inferred {
    let mut type_part = Type::Never(NeverCause::Other);
    for t in first_arg.as_cow_type(i_s).iter_with_unpacked_unions(i_s.db) {
        match t {
            Type::Class(_)
            | Type::None
            | Type::Any(_)
            | Type::Self_
            | Type::Dataclass(_)
            | Type::Tuple(_)
            | Type::NewType(_)
            | Type::TypeVar(_)
            | Type::Enum(_) => type_part.union_in_place(t.clone()),
            Type::Literal(l) => type_part.union_in_place(l.fallback_type(i_s.db)),
            Type::Type(type_) => match type_.as_ref() {
                Type::Class(c) => match &c.class(i_s.db).use_cached_class_infos(i_s.db).metaclass {
                    MetaclassState::Some(link) => {
                        type_part.union_in_place(Type::new_class(*link, ClassGenerics::None))
                    }
                    _ => type_part.union_in_place(i_s.db.python_state.object_type().clone()),
                },
                Type::Any(cause) => type_part.union_in_place(Type::Any(*cause)),
                _ => type_part.union_in_place(i_s.db.python_state.object_type()),
            },
            Type::Module(_) | Type::NamedTuple(_) => {
                type_part.union_in_place(i_s.db.python_state.module_type())
            }
            Type::EnumMember(m) => type_part.union_in_place(Type::Enum(m.enum_.clone())),
            Type::Super { .. } => type_part.union_in_place(i_s.db.python_state.super_type()),
            _ => type_part.union_in_place(i_s.db.python_state.object_type()),
        }
    }
    if type_part.is_never() {
        first_arg // Must be never
    } else {
        Inferred::from_type(Type::Type(Rc::new(type_part)))
    }
}
