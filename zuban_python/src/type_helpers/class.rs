use std::cell::{Cell, OnceCell};
use std::fmt;
use std::rc::Rc;

use parsa_python_ast::{
    Argument, Arguments as ASTArguments, AssignmentContent, AsyncStmtContent, BlockContent,
    ClassDef, Decoratee, ExpressionContent, ExpressionPart, PrimaryContent, SimpleStmtContent,
    SimpleStmts, StmtContent, StmtOrError, Target,
};

use super::enum_::execute_functional_enum;
use super::function::OverloadResult;
use super::{Callable, Instance, Module, NamedTupleValue};
use crate::arguments::{Arguments, KnownArguments, NoArguments, SimpleArguments};
use crate::database::{
    BaseClass, CallableContent, CallableParam, CallableParams, ClassGenerics, ClassInfos,
    ClassStorage, ClassType, ComplexPoint, Database, Dataclass, DataclassOptions, DbType, Enum,
    EnumMemberDefinition, FormatStyle, FunctionKind, GenericClass, GenericsList, Locality,
    MetaclassState, MroIndex, NamedTuple, ParamSpecific, ParentScope, Point, PointLink, PointType,
    StringSlice, TypeVarLike, TypeVarLikeUsage, TypeVarLikes, TypedDict, TypedDictMember, Variance,
};
use crate::debug;
use crate::diagnostics::IssueType;
use crate::file::{use_cached_annotation_type, File};
use crate::file::{
    CalculatedBaseClass, PythonFile, TypeComputation, TypeComputationOrigin, TypeVarCallbackReturn,
    TypeVarFinder,
};
use crate::getitem::SliceType;
use crate::inference_state::InferenceState;
use crate::inferred::{FunctionOrOverload, Inferred};
use crate::matching::{
    calculate_callable_init_type_vars_and_return, calculate_callable_type_vars_and_return,
    calculate_class_init_type_vars_and_return, CallableLike, FormatData, FunctionOrCallable,
    Generics, IteratorContent, LookupKind, LookupResult, Match, Matcher, MismatchReason,
    OnTypeError, ResultContext, Type,
};
use crate::node_ref::NodeRef;
use crate::python_state::NAME_TO_FUNCTION_DIFF;
use crate::type_helpers::dataclass::check_dataclass_options;
use crate::type_helpers::enum_::infer_value_on_member;
use crate::type_helpers::{format_pretty_callable, infer_typed_dict_total_argument};

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

    pub fn from_generic_class(db: &'db Database, c: &'a GenericClass) -> Self {
        Self::from_generic_class_components(db, c.link, &c.generics)
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
        Self::from_position(
            node_ref,
            Generics::Self_ {
                class_definition: node_ref.as_link(),
                type_var_likes: Self::with_undefined_generics(node_ref).use_cached_type_vars(db),
            },
            None,
        )
    }

    fn type_check_init_func(
        &self,
        i_s: &InferenceState<'db, '_>,
        __init__: LookupResult,
        init_class: Option<Class>,
        args: &dyn Arguments<'db>,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError<'db, '_>,
    ) -> Option<ClassGenerics> {
        let Some(inf) = __init__.into_maybe_inferred() else {
            if self.is_protocol(i_s.db) {
                args.as_node_ref().add_issue(i_s, IssueType::CannotInstantiateProtocol {
                    name: self.name().into()
                })
            } else {
                debug_assert!(self.incomplete_mro(i_s.db));
            }
            let type_var_likes = self.type_vars(i_s);
            return Some(match type_var_likes.is_empty() {
                false => ClassGenerics::List(type_var_likes.as_any_generic_list()),
                true => ClassGenerics::None,
            })
        };
        match inf.init_as_function(i_s, init_class) {
            Some(FunctionOrOverload::Function(func)) => {
                let calculated_type_args = calculate_class_init_type_vars_and_return(
                    i_s,
                    self,
                    func,
                    args.iter(),
                    &|| args.as_node_ref(),
                    result_context,
                    Some(on_type_error),
                );
                Some(calculated_type_args.type_arguments_into_class_generics())
            }
            Some(FunctionOrOverload::Callable(callable_content)) => {
                let calculated_type_args = match init_class {
                    Some(class) => todo!() /*calculate_callable_init_type_vars_and_return(
                        i_s,
                        &class,
                        Callable::new(&callable_content, Some(*self)),
                        args.iter(),
                        &|| args.as_node_ref(),
                        result_context,
                        Some(on_type_error),
                    )*/,
                    // Happens for example when NamedTuples are involved.
                    None => calculate_callable_type_vars_and_return(
                        i_s,
                        Callable::new(&callable_content, Some(*self)),
                        args.iter(),
                        &|| args.as_node_ref(),
                        false,
                        result_context,
                        Some(on_type_error),
                    ),
                };
                Some(calculated_type_args.type_arguments_into_class_generics())
            }
            Some(FunctionOrOverload::Overload(overloaded_function)) => match overloaded_function
                .find_matching_function(
                    i_s,
                    args,
                    false,
                    Some(self),
                    true,
                    result_context,
                    on_type_error,
                ) {
                OverloadResult::Single(callable) => {
                    // Execute the found function to create the diagnostics.
                    let result = calculate_callable_init_type_vars_and_return(
                        i_s,
                        self,
                        callable,
                        args.iter(),
                        &|| args.as_node_ref(),
                        result_context,
                        Some(on_type_error),
                    );
                    Some(result.type_arguments_into_class_generics())
                }
                OverloadResult::Union(t) => todo!(),
                OverloadResult::NotFound => None,
            },
            None => unreachable!("Should never happen, because there's always object.__init__"),
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
        if point.type_() == PointType::NodeAnalysis {
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

        let type_vars =
            TypeVarFinder::find_class_type_vars(&mut self.node_ref.file.inference(i_s), self);
        if type_vars.is_empty() {
            self.type_vars_node_ref()
                .set_point(Point::new_node_analysis(Locality::Todo));
        } else {
            self.type_vars_node_ref()
                .insert_complex(ComplexPoint::TypeVarLikes(type_vars), Locality::Todo);
        }
        self.type_vars(i_s)
    }

    pub fn maybe_type_var_like_in_parent(
        &self,
        i_s: &InferenceState<'db, '_>,
        type_var: &TypeVarLike,
    ) -> Option<TypeVarLikeUsage<'static>> {
        match self.class_storage.parent_scope {
            ParentScope::Module => None,
            ParentScope::Class(node_index) => {
                let parent_class =
                    Self::with_undefined_generics(NodeRef::new(self.node_ref.file, node_index));
                parent_class
                    .maybe_type_var_like_in_parent(i_s, type_var)
                    .or_else(|| {
                        parent_class
                            .type_vars(i_s)
                            .find(type_var.clone(), parent_class.node_ref.as_link())
                    })
            }
            ParentScope::Function(node_index) => todo!(),
        }
    }

    fn is_calculating_class_infos(&self) -> bool {
        self.class_info_node_ref().point().calculating()
    }

    #[inline]
    fn type_vars_node_ref(&self) -> NodeRef<'a> {
        self.node_ref.add_to_node_index(1)
    }

    #[inline]
    fn class_info_node_ref(&self) -> NodeRef<'a> {
        self.node_ref.add_to_node_index(4)
    }

    pub fn ensure_calculated_class_infos(&self, i_s: &InferenceState<'db, '_>, name_def: NodeRef) {
        let node_ref = self.class_info_node_ref();
        let point = node_ref.point();
        if point.calculated() {
            return;
        }

        debug_assert!(!name_def.point().calculated());

        node_ref.set_point(Point::new_calculating());
        // TODO it is questionable that we are just marking this as OK, because it could be an
        // Enum / dataclass.
        name_def.set_point(Point::new_redirect(
            self.node_ref.file_index(),
            self.node_ref.node_index,
            Locality::Todo,
        ));

        let type_vars = self.type_vars(i_s);

        let mut was_dataclass = None;
        let maybe_decorated = self.node().maybe_decorated();
        if let Some(decorated) = maybe_decorated {
            let mut inference = self.node_ref.file.inference(i_s);

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
                            let args = SimpleArguments::new(
                                *i_s,
                                self.node_ref.file,
                                primary.index(),
                                exec,
                            );
                            dataclass_options = Some(check_dataclass_options(i_s, &args));
                            continue;
                        }
                    }
                }
                if inference.infer_expression(expr).maybe_saved_link() == Some(dataclass_link) {
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
                was_dataclass = Some(dataclass.clone());
                let new_t = DbType::Type(Rc::new(DbType::Dataclass(dataclass)));
                Inferred::from_type(new_t).save_redirect(i_s, name_def.file, name_def.node_index);
            }
        }

        let (mut class_infos, was_typed_dict) = self.calculate_class_infos(i_s, type_vars);
        let mut was_enum = None;
        let mut was_enum_base = false;
        if let Some(td) = was_typed_dict {
            name_def.insert_complex(
                ComplexPoint::TypedDictDefinition(Rc::new(DbType::TypedDict(td.clone()))),
                Locality::ImplicitExtern,
            );
        }
        if let MetaclassState::Some(link) = class_infos.metaclass {
            if link == i_s.db.python_state.enum_meta_link() {
                was_enum_base = true;
                if !self.use_cached_type_vars(i_s.db).is_empty() {
                    self.node_ref.add_issue(i_s, IssueType::EnumCannotBeGeneric);
                }
                class_infos.class_type = ClassType::Enum;
                let members = self.enum_members(i_s);
                if !members.is_empty() {
                    let enum_ = Enum::new(
                        self.name_string_slice(),
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
        node_ref.insert_complex(ComplexPoint::ClassInfos(class_infos), Locality::Todo);
        debug_assert!(node_ref.point().calculated());

        if let Some(decorated) = maybe_decorated {
            // TODO we pretty much just ignore the fact that a decorated class can also be an enum.
            let mut inferred = Inferred::from_saved_node_ref(self.node_ref);
            for decorator in decorated.decorators().iter_reverse() {
                if matches!(
                    decorator.as_code(),
                    "@final\n" | "@type_check_only\n" | "@runtime_checkable\n"
                ) {
                    // TODO this branch should not be here!
                    continue;
                }
                let decorate = self
                    .node_ref
                    .file
                    .inference(i_s)
                    .infer_named_expression(decorator.named_expression());
                inferred = decorate.execute(
                    i_s,
                    &KnownArguments::new(
                        &inferred,
                        NodeRef::new(self.node_ref.file, decorator.index()),
                    ),
                );
            }
            // TODO for now don't save classdecorators, becaues they are really not used in mypy.
            // let saved = inferred.save_redirect(i_s, name_def.file, name_def.node_index);
        }

        if let Some(dataclass) = was_dataclass {
            Dataclass::__init__(&dataclass, i_s.db);
        }

        if let Some(enum_) = was_enum {
            let c = ComplexPoint::TypeInstance(DbType::Type(Rc::new(DbType::Enum(enum_.clone()))));
            // The locality is implicit, because we have a OnceCell that is inferred
            // after what we are doing here.
            name_def.insert_complex(c, Locality::ImplicitExtern);

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
                    let is_enum = c.use_cached_class_infos(i_s.db).class_type == ClassType::Enum;
                    let has_mixin_enum_new = if is_enum {
                        c.bases(i_s.db).any(|inner| match inner {
                            TypeOrClass::Class(inner) => {
                                inner.use_cached_class_infos(i_s.db).class_type != ClassType::Enum
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
                            self.node_ref.add_issue(
                                i_s,
                                IssueType::EnumMultipleMixinNew {
                                    extra: c.format(&FormatData::with_style(
                                        i_s.db,
                                        FormatStyle::Qualified,
                                    )),
                                },
                            );
                        }
                    }
                    // (2)
                    match enum_spotted {
                        Some(after) if !is_enum => {
                            self.node_ref.add_issue(
                                i_s,
                                IssueType::EnumMixinNotAllowedAfterEnum {
                                    after: after.format(&FormatData::with_style(
                                        i_s.db,
                                        FormatStyle::Qualified,
                                    )),
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
            .filter_map(move |b| {
                b.is_direct_base
                    .then(|| apply_generics_to_base_class(db, &b.type_, generics))
            })
    }

    fn calculate_class_infos(
        &self,
        i_s: &InferenceState<'db, '_>,
        type_vars: &TypeVarLikes,
    ) -> (Box<ClassInfos>, Option<Rc<TypedDict>>) {
        debug!("Calculate class infos for {}", self.name());
        // Calculate all type vars beforehand
        let db = i_s.db;

        let mut bases: Vec<DbType> = vec![];
        let mut incomplete_mro = false;
        let mut class_type = ClassType::Normal;
        let mut maybe_typed_dict_members = None;
        let mut is_new_typed_dict = false;
        let mut metaclass = MetaclassState::None;
        if let Some(arguments) = self.node().arguments() {
            // Check metaclass before checking all the arguments, because it has a preference over
            // the metaclasses of the subclasses.
            for argument in arguments.iter() {
                if let Argument::Keyword(kwarg) = argument {
                    let (name, expr) = kwarg.unpack();
                    if name.as_str() == "metaclass" {
                        let node_ref = NodeRef::new(self.node_ref.file, expr.index());
                        let mut inference = self.node_ref.file.inference(i_s);
                        let meta_base = TypeComputation::new(
                            &mut inference,
                            self.node_ref.as_link(),
                            &mut |i_s, _: &_, type_var_like: TypeVarLike, _| {
                                todo!();
                            },
                            TypeComputationOrigin::BaseClass,
                        )
                        .compute_base_class(expr);
                        match meta_base {
                            CalculatedBaseClass::DbType(DbType::Class(GenericClass {
                                link,
                                generics: ClassGenerics::None,
                            })) => {
                                let c = Class::from_non_generic_link(db, link);
                                if c.incomplete_mro(db)
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
                                    )
                                } else {
                                    node_ref
                                        .add_issue(i_s, IssueType::MetaclassMustInheritFromType);
                                }
                            }
                            CalculatedBaseClass::Unknown => metaclass = MetaclassState::Unknown,
                            _ => {
                                node_ref.add_issue(i_s, IssueType::InvalidMetaclass);
                            }
                        }
                    }
                }
            }

            // Calculate the type var remapping
            for argument in arguments.iter() {
                match argument {
                    Argument::Positional(n) => {
                        let mut inference = self.node_ref.file.inference(i_s);
                        let base = TypeComputation::new(
                            &mut inference,
                            self.node_ref.as_link(),
                            &mut |i_s, _: &_, type_var_like: TypeVarLike, _| {
                                if let Some(usage) =
                                    type_vars.find(type_var_like.clone(), self.node_ref.as_link())
                                {
                                    return TypeVarCallbackReturn::TypeVarLike(usage);
                                }
                                if let Some(usage) =
                                    self.maybe_type_var_like_in_parent(i_s, &type_var_like)
                                {
                                    return TypeVarCallbackReturn::TypeVarLike(usage);
                                }
                                todo!("Maybe class in func");
                            },
                            TypeComputationOrigin::BaseClass,
                        )
                        .compute_base_class(n.expression());
                        match base {
                            CalculatedBaseClass::DbType(t) => {
                                if let Some(name) = bases.iter().find_map(|base| {
                                    Type::new(base).check_duplicate_base_class(db, &Type::new(&t))
                                }) {
                                    NodeRef::new(self.node_ref.file, n.index())
                                        .add_issue(i_s, IssueType::DuplicateBaseClass { name });
                                    incomplete_mro = true;
                                    continue;
                                }
                                bases.push(t);
                                let class = match &bases.last().unwrap() {
                                    DbType::Class(c) => Some(Class::from_generic_class(db, c)),
                                    DbType::Tuple(content) => None,
                                    DbType::Callable(content) => None,
                                    DbType::Dataclass(d) => Some(d.class(db)),
                                    DbType::TypedDict(typed_dict) => {
                                        if matches!(
                                            class_type,
                                            ClassType::Normal | ClassType::TypedDict
                                        ) {
                                            let mut members: Vec<_> =
                                                typed_dict.members.clone().into();
                                            self.initialize_typed_dict_members(
                                                &i_s.with_class_context(self),
                                                &mut members,
                                                self.check_total_typed_dict_argument(
                                                    i_s, arguments,
                                                ),
                                            );
                                            class_type = ClassType::TypedDict;
                                            maybe_typed_dict_members = Some(members);
                                        } else {
                                            todo!()
                                        }
                                        bases.pop();
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
                                            .add_issue(i_s, IssueType::CyclicDefinition { name });
                                    } else {
                                        let cached_class_infos = class.use_cached_class_infos(db);
                                        incomplete_mro |= cached_class_infos.incomplete_mro;
                                        Self::update_metaclass(
                                            i_s,
                                            NodeRef::new(self.node_ref.file, n.index()),
                                            &mut metaclass,
                                            cached_class_infos.metaclass,
                                        );
                                        match &cached_class_infos.class_type {
                                            ClassType::NamedTuple(named_tuple) => {
                                                if matches!(class_type, ClassType::Normal) {
                                                    class_type =
                                                        ClassType::NamedTuple(named_tuple.clone());
                                                } else {
                                                    todo!()
                                                }
                                            }
                                            ClassType::TypedDict => {
                                                unreachable!()
                                            }
                                            _ => (),
                                        }
                                    }
                                }
                            }
                            // TODO this might overwrite other class types
                            CalculatedBaseClass::Protocol => {
                                class_type = ClassType::Protocol;
                                metaclass = MetaclassState::Some(db.python_state.abc_meta_link())
                            }
                            CalculatedBaseClass::NamedTuple(named_tuple) => {
                                let named_tuple =
                                    named_tuple.clone_with_new_init_class(self.name_string_slice());
                                bases.push(DbType::NamedTuple(named_tuple.clone()));
                                class_type = ClassType::NamedTuple(named_tuple);
                            }
                            CalculatedBaseClass::NewNamedTuple => {
                                let named_tuple = self
                                    .named_tuple_from_class(&i_s.with_class_context(self), *self);
                                bases.push(DbType::NamedTuple(named_tuple.clone()));
                                class_type = ClassType::NamedTuple(named_tuple);
                            }
                            CalculatedBaseClass::TypedDict => {
                                is_new_typed_dict = true;
                                let mut members = vec![];

                                self.initialize_typed_dict_members(
                                    &i_s.with_class_context(self),
                                    &mut members,
                                    self.check_total_typed_dict_argument(i_s, arguments),
                                );
                                class_type = ClassType::TypedDict;
                                maybe_typed_dict_members = Some(members);
                            }
                            CalculatedBaseClass::Generic => (),
                            CalculatedBaseClass::Unknown => {
                                incomplete_mro = true;
                            }
                            CalculatedBaseClass::InvalidEnum(enum_) => {
                                NodeRef::new(self.node_ref.file, n.index()).add_issue(
                                    i_s,
                                    IssueType::EnumWithMembersNotExtendable {
                                        name: enum_.name.as_str(i_s.db).into(),
                                    },
                                );
                                incomplete_mro = true;
                            }
                            CalculatedBaseClass::Invalid => {
                                NodeRef::new(self.node_ref.file, n.index())
                                    .add_issue(i_s, IssueType::InvalidBaseClass);
                                incomplete_mro = true;
                            }
                        };
                    }
                    Argument::Keyword(kwarg) => {
                        let (name, expr) = kwarg.unpack();
                        if name.as_str() != "metaclass" {
                            // Generate diagnostics
                            self.node_ref.file.inference(i_s).infer_expression(expr);
                            debug!("TODO shouldn't we handle this? In testNewAnalyzerClassKeywordsForward it's ignored...")
                        }
                    }
                    Argument::Starred(starred) => {
                        NodeRef::new(self.node_ref.file, starred.index())
                            .add_issue(i_s, IssueType::InvalidBaseClass);
                    }
                    Argument::DoubleStarred(double_starred) => {
                        NodeRef::new(self.node_ref.file, double_starred.index())
                            .add_issue(i_s, IssueType::InvalidBaseClass);
                    }
                }
            }
        }
        if is_new_typed_dict {
            // For some reason the mro calculation has problems if we don't do this here. No idea
            // why this doesn't cause issues in real Python.
            bases.push(i_s.db.python_state.typed_dict_db_type());
        }
        (
            Box::new(ClassInfos {
                mro: linearize_mro(i_s, self, bases),
                metaclass,
                incomplete_mro,
                class_type,
            }),
            maybe_typed_dict_members.map(|members| {
                Rc::new(TypedDict {
                    name: self.name_string_slice(),
                    members: members.into(),
                    defined_at: self.node_ref.as_link(),
                    type_var_likes: self.type_vars(i_s).clone(),
                })
            }),
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
                    let t1 = Type::owned(DbType::Class(GenericClass {
                        link: *link1,
                        generics: ClassGenerics::None,
                    }));
                    let t2 = Type::owned(DbType::Class(GenericClass {
                        link: link2,
                        generics: ClassGenerics::None,
                    }));
                    if !t1.is_simple_sub_type_of(i_s, &t2).bool() {
                        if t2.is_simple_sub_type_of(i_s, &t1).bool() {
                            *current = new
                        } else {
                            node_ref.add_issue(i_s, IssueType::MetaclassConflict);
                        }
                    }
                }
                _ => *current = new,
            },
        }
    }

    fn check_total_typed_dict_argument(&self, i_s: &InferenceState, args: ASTArguments) -> bool {
        let mut total = true;
        let mut inference = self.node_ref.file.inference(i_s);
        for argument in args.iter() {
            if let Argument::Keyword(kwarg) = argument {
                let (name, expr) = kwarg.unpack();
                if name.as_code() == "total" {
                    let inf = inference
                        .infer_expression_with_context(expr, &mut ResultContext::ExpectLiteral);
                    total = infer_typed_dict_total_argument(
                        i_s,
                        inf,
                        NodeRef::new(self.node_ref.file, expr.index()),
                    )
                    .unwrap_or(true);
                }
            }
        }
        total
    }

    pub fn is_metaclass(&self, db: &Database) -> bool {
        let python_type = db.python_state.bare_type_db_type();
        self.use_cached_class_infos(db)
            .mro
            .iter()
            .any(|t| t.type_ == python_type)
    }

    pub fn is_base_exception_group(&self, db: &Database) -> bool {
        self.class_link_in_mro(
            db,
            db.python_state.base_exception_group_node_ref().as_link(),
        )
    }

    pub fn is_base_exception(&self, db: &Database) -> bool {
        self.class_link_in_mro(db, db.python_state.base_exception_node_ref().as_link())
    }

    pub fn is_exception(&self, db: &Database) -> bool {
        self.class_link_in_mro(db, db.python_state.exception_node_ref().as_link())
    }

    pub fn is_protocol(&self, db: &Database) -> bool {
        self.use_cached_class_infos(db).class_type == ClassType::Protocol
    }

    pub fn check_protocol_match(
        &self,
        i_s: &InferenceState<'db, '_>,
        matcher: &mut Matcher,
        other: &Type,
        variance: Variance,
    ) -> Match {
        const SHOW_MAX_MISMATCHES: usize = 2;
        const MAX_MISSING_MEMBERS: usize = 2;
        let mut missing_members = vec![];
        let mut mismatches = 0;
        let mut notes = vec![];
        let mut had_conflict_note = false;

        let mut protocol_member_count = 0;
        debug!("TODO this from is completely wrong and should never be used.");
        let hack = self.node_ref;
        for (mro_index, c) in self.mro_maybe_without_object(i_s.db, true) {
            let TypeOrClass::Class(c) = c else {
                todo!()
            };
            protocol_member_count += c.class_storage.class_symbol_table.len();
            let symbol_table = &c.class_storage.class_symbol_table;
            for (name, _) in unsafe { symbol_table.iter_on_finished_table() } {
                // It is possible to match a Callable against a Protocol that only implements
                // __call__.
                if name == "__call__" && !matches!(other.as_ref(), DbType::Class(_)) {
                    let inf1 = Instance::new(c, None)
                        .type_lookup(i_s, hack, name)
                        .into_inferred();
                    let t1 = inf1.as_type(i_s);
                    if t1.matches(i_s, matcher, other, variance).bool() {
                        continue;
                    }
                }

                if let Some(l) = other
                    .lookup(
                        i_s,
                        hack,
                        name,
                        LookupKind::Normal,
                        &mut ResultContext::Unknown,
                        &|_| (),
                    )
                    .into_maybe_inferred()
                {
                    let inf1 = Instance::new(c, None)
                        .full_lookup(i_s, hack, name)
                        .into_inferred();
                    let t1 = inf1.as_type(i_s);
                    let t2 = l.as_type(i_s);
                    let m = t1.matches(i_s, matcher, &t2, variance);
                    if !m.bool() {
                        if !had_conflict_note {
                            had_conflict_note = true;
                            notes.push(
                                match other.as_ref() {
                                    DbType::Module(file_index) => format!(
                                        "Following member(s) of Module \"{}\" have conflicts:",
                                        Module::from_file_index(i_s.db, *file_index)
                                            .qualified_name(i_s.db)
                                    ),
                                    DbType::Type(t) => format!(
                                        "Following member(s) of \"{}\" have conflicts:",
                                        t.format_short(i_s.db)
                                    ),
                                    _ => format!(
                                        "Following member(s) of \"{}\" have conflicts:",
                                        other.format_short(i_s.db)
                                    ),
                                }
                                .into(),
                            );
                        }
                        mismatches += 1;
                        if mismatches <= SHOW_MAX_MISMATCHES {
                            match other.maybe_class(i_s.db) {
                                Some(cls) => add_protocol_mismatch(
                                    i_s,
                                    &mut notes,
                                    name,
                                    &t1,
                                    &t2,
                                    &c.lookup(i_s, hack, name, LookupKind::Normal)
                                        .into_inferred()
                                        .as_type(i_s),
                                    &cls.lookup(i_s, hack, name, LookupKind::Normal)
                                        .into_inferred()
                                        .as_type(i_s),
                                ),
                                None => {
                                    add_protocol_mismatch(i_s, &mut notes, name, &t1, &t2, &t1, &t2)
                                }
                            }
                        }
                    }
                } else {
                    missing_members.push(name);
                }
            }
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

    pub fn has_customized_enum_new(&self, i_s: &InferenceState) -> bool {
        for (_, c) in self.mro_maybe_without_object(i_s.db, true) {
            let (c, lookup) = c.lookup_symbol(i_s, "__new__");
            if lookup.into_maybe_inferred().is_some() {
                let Some(class) = c else {
                    unreachable!()
                };
                return class.node_ref.file.file_index()
                    != i_s.db.python_state.enum_file().file_index();
            }
        }
        false
    }

    pub fn lookup_symbol(&self, i_s: &InferenceState<'db, '_>, name: &str) -> LookupResult {
        match self.class_storage.class_symbol_table.lookup_symbol(name) {
            None => LookupResult::None,
            Some(node_index) => {
                let inf = self
                    .node_ref
                    .file
                    .inference(&i_s.with_class_context(self))
                    .infer_name_by_index(node_index);
                LookupResult::GotoName(
                    PointLink::new(self.node_ref.file.file_index(), node_index),
                    inf,
                )
            }
        }
    }

    fn lookup_and_class_and_maybe_ignore_self_internal(
        &self,
        i_s: &InferenceState<'db, '_>,
        name: &str,
        ignore_self: bool,
    ) -> (LookupResult, Option<Class>, MroIndex) {
        for (mro_index, c) in self
            .mro_maybe_without_object(i_s.db, self.incomplete_mro(i_s.db))
            .skip(ignore_self as usize)
        {
            let (_, result) = c.lookup_symbol(i_s, name);
            if !matches!(result, LookupResult::None) {
                if let TypeOrClass::Class(c) = c {
                    return (result, Some(c), mro_index);
                } else {
                    return (result, None, mro_index);
                }
            }
        }
        (LookupResult::None, None, 0.into())
    }

    pub fn lookup_and_class_and_maybe_ignore_self(
        &self,
        i_s: &InferenceState<'db, '_>,
        hack: NodeRef,
        name: &str,
        kind: LookupKind,
        ignore_self: bool,
    ) -> (LookupResult, Option<Class>) {
        self.lookup_with_or_without_descriptors_internal(i_s, hack, name, kind, false, ignore_self)
    }

    pub fn lookup_without_descriptors(
        &self,
        i_s: &InferenceState<'db, '_>,
        node_ref: NodeRef,
        name: &str,
    ) -> (LookupResult, Option<Class>) {
        self.lookup_with_or_without_descriptors_internal(
            i_s,
            node_ref,
            name,
            LookupKind::Normal,
            false,
            false,
        )
    }

    pub fn lookup_with_or_without_descriptors_internal(
        &'a self,
        i_s: &InferenceState<'db, '_>,
        node_ref: NodeRef,
        name: &str,
        kind: LookupKind,
        use_descriptors: bool,
        ignore_self: bool,
    ) -> (LookupResult, Option<Class>) {
        let class_infos = self.use_cached_class_infos(i_s.db);
        let (result, in_class) = if kind == LookupKind::Normal {
            if class_infos.class_type == ClassType::Enum && use_descriptors && name == "_ignore_" {
                return (LookupResult::None, Some(*self));
            }
            let (lookup_result, in_class, _) =
                self.lookup_and_class_and_maybe_ignore_self_internal(i_s, name, ignore_self);
            let result = lookup_result.and_then(|inf| {
                if let Some(in_class) = in_class {
                    let i_s = i_s.with_class_context(&in_class);
                    inf.bind_class_descriptors(&i_s, self, in_class, node_ref, use_descriptors)
                } else {
                    Some(inf)
                }
            });
            (result, in_class)
        } else {
            (None, None)
        };
        match result {
            Some(LookupResult::None) | None => {
                let result = match class_infos.metaclass {
                    MetaclassState::Unknown => LookupResult::any(),
                    _ => {
                        let instance = Instance::new(class_infos.metaclass(i_s.db), None);
                        instance
                            .lookup_with_explicit_self_binding(
                                i_s,
                                node_ref,
                                name,
                                LookupKind::Normal,
                                0,
                                || self.as_type(i_s).into_db_type(),
                            )
                            .1
                    }
                };
                if matches!(result, LookupResult::None) && self.incomplete_mro(i_s.db) {
                    (LookupResult::any(), in_class)
                } else {
                    (result, in_class)
                }
            }
            Some(x) => (x, in_class),
        }
    }

    pub fn generics(&self) -> Generics {
        if let Some(type_var_remap) = self.type_var_remap {
            Generics::List(type_var_remap, Some(&self.generics))
        } else {
            self.generics
        }
    }

    pub fn has_simple_self_generics(&self) -> bool {
        matches!(self.generics, Generics::Self_ { .. }) && self.type_var_remap.is_none()
    }

    pub fn nth_type_argument(&self, db: &Database, nth: usize) -> DbType {
        let type_vars = self.use_cached_type_vars(db);
        self.generics()
            .nth_type_argument(db, &type_vars[nth], nth)
            .into_db_type()
    }

    fn mro_maybe_without_object(
        &self,
        db: &'db Database,
        without_object: bool,
    ) -> MroIterator<'db, 'a> {
        let class_infos = self.use_cached_class_infos(db);
        MroIterator::new(
            db,
            TypeOrClass::Class(*self),
            self.generics,
            class_infos.mro.iter(),
            without_object
                || self.node_ref == db.python_state.object_node_ref()
                || class_infos.class_type == ClassType::Protocol,
        )
    }

    pub fn mro(&self, db: &'db Database) -> MroIterator<'db, 'a> {
        self.mro_maybe_without_object(db, self.node_ref == db.python_state.object_node_ref())
    }

    pub fn class_link_in_mro(&self, db: &'db Database, link: PointLink) -> bool {
        if self.node_ref.as_link() == link {
            return true;
        }
        let class_infos = self.use_cached_class_infos(db);
        class_infos
            .mro
            .iter()
            .any(|b| matches!(&b.type_, DbType::Class(c) if link == c.link))
    }

    pub fn is_object_class(&self, db: &Database) -> Match {
        (self.node_ref == db.python_state.object_node_ref()).into()
    }

    pub fn format(&self, format_data: &FormatData) -> Box<str> {
        let mut result = match format_data.style {
            FormatStyle::Short => self.name().to_owned(),
            FormatStyle::Qualified | FormatStyle::MypyRevealType => {
                self.qualified_name(format_data.db)
            }
        };
        let type_var_likes = self.type_vars(&InferenceState::new(format_data.db));
        if !type_var_likes.is_empty() {
            result += &self
                .generics()
                .format(format_data, Some(type_var_likes.len()));
        }
        let class_infos = self.use_cached_class_infos(format_data.db);
        match &class_infos.class_type {
            ClassType::NamedTuple(named_tuple) => NamedTupleValue::new(format_data.db, named_tuple)
                .format_with_name(format_data, &result, self.generics),
            _ => result.into(),
        }
    }

    pub fn format_short(&self, db: &Database) -> Box<str> {
        self.format(&FormatData::new_short(db))
    }

    pub fn as_inferred(&self, i_s: &InferenceState) -> Inferred {
        Inferred::from_type(self.as_type(i_s).into_db_type())
    }

    pub fn generics_as_list(&self, db: &Database) -> ClassGenerics {
        // TODO we instantiate, because we cannot use use_cached_type_vars?
        let type_vars = self.type_vars(&InferenceState::new(db));
        self.generics().as_generics_list(db, type_vars)
    }

    pub fn as_generic_class(&self, db: &Database) -> GenericClass {
        GenericClass {
            link: self.node_ref.as_link(),
            generics: self.generics_as_list(db),
        }
    }

    pub fn as_db_type(&self, db: &Database) -> DbType {
        DbType::Class(self.as_generic_class(db))
    }

    pub fn as_type(&self, i_s: &InferenceState<'db, '_>) -> Type<'a> {
        Type::owned(DbType::Type(Rc::new(self.as_db_type(i_s.db))))
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
        match self.node().block().unpack() {
            BlockContent::Indented(stmts) => {
                for stmt in stmts {
                    let StmtOrError::Stmt(stmt) = stmt else {
                        continue
                    };
                    match stmt.unpack() {
                        StmtContent::SimpleStmts(simple) => {
                            find_stmt_named_tuple_types(i_s, file, &mut vec, simple)
                        }
                        StmtContent::FunctionDef(_) => (),
                        StmtContent::AsyncStmt(async_stmt)
                            if matches!(async_stmt.unpack(), AsyncStmtContent::FunctionDef(_)) => {}
                        StmtContent::Decorated(dec)
                            if matches!(
                                dec.decoratee(),
                                Decoratee::FunctionDef(_) | Decoratee::AsyncFunctionDef(_)
                            ) => {}
                        _ => NodeRef::new(file, stmt.index())
                            .add_issue(i_s, IssueType::InvalidStmtInNamedTuple),
                    }
                }
            }
            BlockContent::OneLine(simple) => todo!(), //find_stmt_named_tuple_types(i_s, file, &mut vec, simple),
        }
        let tvls = self.use_cached_type_vars(i_s.db);
        CallableContent {
            name: Some(name),
            class_name: None,
            defined_at: self.node_ref.as_link(),
            kind: FunctionKind::Function,
            type_vars: self.use_cached_type_vars(i_s.db).clone(),
            params: CallableParams::Simple(Rc::from(vec)),
            result_type: DbType::Self_,
        }
    }

    fn initialize_typed_dict_members(
        &self,
        i_s: &InferenceState,
        vec: &mut Vec<TypedDictMember>,
        total: bool,
    ) {
        let file = self.node_ref.file;
        match self.node().block().unpack() {
            BlockContent::Indented(stmts) => {
                for stmt in stmts {
                    let StmtOrError::Stmt(stmt) = stmt else {
                        continue
                    };
                    match stmt.unpack() {
                        StmtContent::SimpleStmts(simple) => {
                            find_stmt_typed_dict_types(i_s, file, vec, simple, total)
                        }
                        _ => NodeRef::new(file, stmt.index())
                            .add_issue(i_s, IssueType::TypedDictInvalidMember),
                    }
                }
            }
            BlockContent::OneLine(simple) => todo!(), //find_stmt_typed_dict_types(i_s, file, &mut vec, simple),
        }
        let tvls = self.use_cached_type_vars(i_s.db);
    }

    fn enum_members(&self, i_s: &InferenceState) -> Box<[EnumMemberDefinition]> {
        let mut members = vec![];
        let mut name_indexes = vec![];
        for (name, name_index) in unsafe {
            self.class_storage
                .class_symbol_table
                .iter_on_finished_table()
        } {
            if name.starts_with('_') {
                if name == "__members__" {
                    let name_node_ref = NodeRef::new(self.node_ref.file, *name_index);
                    if !name_node_ref
                        .as_name()
                        .is_assignment_annotation_without_definition()
                    {
                        name_node_ref.add_issue(i_s, IssueType::EnumMembersAttributeOverwritten)
                    }
                }
                continue;
            }
            name_indexes.push(name_index);
        }

        // The name indexes are not guarantueed to be sorted by its order in the tree. We however
        // want the original order in an enum.
        name_indexes.sort();

        for name_index in name_indexes {
            let name_node_ref = NodeRef::new(self.node_ref.file, *name_index);
            if name_node_ref
                .add_to_node_index(-(NAME_TO_FUNCTION_DIFF as i64))
                .maybe_function()
                .is_none()
            {
                let point = name_node_ref.point();
                if point.calculated() && point.type_() == PointType::MultiDefinition {
                    NodeRef::new(self.node_ref.file, point.node_index()).add_issue(
                        i_s,
                        IssueType::EnumReusedMemberName {
                            enum_name: self.name().into(),
                            member_name: name_node_ref.as_code().into(),
                        },
                    )
                }
                // TODO An enum member is never a descriptor. (that's how 3.10 does it). Here we
                // however only filter for functions and ignore decorators.
                members.push(EnumMemberDefinition::new(
                    StringSlice::from_name(self.node_ref.file_index(), name_node_ref.as_name())
                        .into(),
                    Some(name_node_ref.as_link()),
                ))
            }
        }
        members.into_boxed_slice()
    }

    pub fn find_relevant_constructor(
        &self,
        i_s: &InferenceState<'db, '_>,
    ) -> NewOrInitConstructor<'_> {
        let (__init__, init_class, init_mro_index) =
            self.lookup_and_class_and_maybe_ignore_self_internal(i_s, "__init__", false);
        let (__new__, new_class, new_mro_index) =
            self.lookup_and_class_and_maybe_ignore_self_internal(i_s, "__new__", false);
        // This is just a weird heuristic Mypy uses, because the type system itself is very unclear
        // what to do if both __new__ and __init__ are present. So just only use __new__ if it's in
        // a lower MRO than an __init__.
        let is_new = !matches!(__new__, LookupResult::None) && new_mro_index < init_mro_index;
        NewOrInitConstructor {
            is_new,
            // TODO this should not be bound if is_new = false
            constructor: match is_new {
                false => __init__,
                true => __new__
                    .and_then(|inf| Some(inf.bind_new_descriptors(i_s, self, new_class)))
                    .unwrap(),
            },
            init_class,
        }
    }

    pub fn execute(
        &self,
        original_i_s: &InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError<'db, '_>,
    ) -> Inferred {
        if self.node_ref == original_i_s.db.python_state.dict_node_ref() {
            // This is a special case where we intercept the call to dict(..) when used with
            // TypedDict.
            if let Some(inf) = args
                .as_node_ref()
                .file
                .inference(original_i_s)
                .infer_dict_call_from_context(args, result_context)
            {
                return inf;
            }
        }
        match self.execute_and_return_generics(original_i_s, args, result_context, on_type_error) {
            ClassExecutionResult::ClassGenerics(generics) => {
                let result = Inferred::from_type(DbType::Class(GenericClass {
                    link: self.node_ref.as_link(),
                    generics,
                }));
                debug!("Class execute: {}", result.format_short(original_i_s));
                result
            }
            ClassExecutionResult::Inferred(inf) => inf,
        }
    }

    fn execute_and_return_generics(
        &self,
        original_i_s: &InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError<'db, '_>,
    ) -> ClassExecutionResult {
        let i_s = &original_i_s.with_class_context(self);
        let had_type_error = Cell::new(false);
        let d = |_: &FunctionOrCallable, _: &Database| {
            had_type_error.set(true);
            Some(format!("\"{}\"", self.name()))
        };
        let on_type_error = on_type_error.with_custom_generate_diagnostic_string(&d);

        match &self.use_cached_class_infos(i_s.db).class_type {
            ClassType::Enum if self.node_ref.as_link() != i_s.db.python_state.enum_auto_link() => {
                // For whatever reason, auto is special, because it is somehow defined as an enum as
                // well, which is very weird.
                let metaclass = Instance::new(
                    Class::from_non_generic_link(i_s.db, i_s.db.python_state.enum_meta_link()),
                    None,
                );
                let call = metaclass
                    .type_lookup(i_s, args.as_node_ref(), "__call__")
                    .into_inferred();
                let DbType::FunctionOverload(o) = call.as_db_type(i_s) else {
                    todo!()
                };
                // Enum currently has multiple signatures that are not all relevant. Just pick the one
                // that's relevant, because otherwise we would have very very ugly error messages with
                // overload outputs.
                let significant_call =
                    Callable::new(o.iter_functions().nth(1).unwrap(), Some(metaclass.class));
                significant_call.execute(i_s, args, on_type_error, result_context);
                if had_type_error.get() {
                    return ClassExecutionResult::Inferred(Inferred::new_any());
                }
                return ClassExecutionResult::Inferred(
                    execute_functional_enum(original_i_s, *self, args, result_context)
                        .unwrap_or_else(Inferred::new_any),
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
                .as_db_type(i_s);
            return match &result {
                // Only subclasses of the current class are valid, otherwise return the current
                // class. Diagnostics will care about these cases and raise errors when needed.
                DbType::Class(c)
                    if Type::new(&self.as_db_type(i_s.db))
                        .is_simple_super_type_of(i_s, &Type::new(&result))
                        .bool() =>
                {
                    ClassExecutionResult::Inferred(Inferred::from_type(result))
                }
                _ => ClassExecutionResult::ClassGenerics(self.generics_as_list(i_s.db)),
            };
        }

        match self.type_check_init_func(
            i_s,
            constructor.constructor,
            constructor.init_class,
            args,
            result_context,
            on_type_error,
        ) {
            Some(generics) => ClassExecutionResult::ClassGenerics(generics),
            None => ClassExecutionResult::Inferred(Inferred::new_any()),
        }
    }

    pub fn lookup(
        &self,
        i_s: &InferenceState,
        node_ref: NodeRef,
        name: &str,
        kind: LookupKind,
    ) -> LookupResult {
        self.lookup_with_or_without_descriptors_internal(i_s, node_ref, name, kind, true, false)
            .0
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
                        slice_type.as_node_ref(),
                        "__getitem__",
                        LookupKind::OnlyType,
                    )
                    .into_maybe_inferred()
                {
                    return __getitem__.execute(i_s, &slice_type.as_args(*i_s));
                }
            }
            MetaclassState::Unknown => {
                todo!()
            }
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

    pub fn iter(&self, i_s: &InferenceState, from: NodeRef) -> Option<IteratorContent> {
        match self.use_cached_class_infos(i_s.db).metaclass {
            MetaclassState::Some(_) => self
                .lookup(i_s, from, "__iter__", LookupKind::OnlyType)
                .into_maybe_inferred()
                .map(|__iter__| {
                    IteratorContent::Inferred(
                        __iter__
                            .execute(i_s, &NoArguments::new(from))
                            .type_lookup_and_execute(
                                i_s,
                                from,
                                "__next__",
                                &NoArguments::new(from),
                                &|_| todo!(),
                            ),
                    )
                }),
            MetaclassState::Unknown => {
                todo!()
            }
            MetaclassState::None => None,
        }
    }
}

impl fmt::Debug for Class<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("Class")
            .field("file_index", &self.node_ref.file.file_index())
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

#[derive(Debug, PartialEq, Eq)]
enum BaseKind {
    Class(PointLink),
    Dataclass(PointLink),
    NamedTuple,
    TypedDict,
    Tuple,
    Type,
    Enum,
    Callable,
}

fn to_base_kind(t: &DbType) -> BaseKind {
    match t {
        DbType::Class(c) => BaseKind::Class(c.link),
        DbType::Type(_) => BaseKind::Type,
        DbType::Tuple(_) => BaseKind::Tuple,
        DbType::Dataclass(d) => BaseKind::Dataclass(d.class.link),
        DbType::TypedDict(d) => BaseKind::TypedDict,
        DbType::NamedTuple(_) => BaseKind::NamedTuple,
        DbType::Enum(_) => BaseKind::Enum,
        DbType::Callable(_) => BaseKind::Callable,
        _ => unreachable!("{t:?}"),
    }
}

fn linearize_mro(i_s: &InferenceState, class: &Class, bases: Vec<DbType>) -> Box<[BaseClass]> {
    let mut mro = vec![];

    let object = i_s.db.python_state.object_db_type();
    if let Some(index) = bases.iter().position(|base| base == &object) {
        // Instead of adding object to each iterator (because in our mro, object is not saved), we
        // just check for object in bases here. If it's not in the last position it's wrong.
        if index != bases.len() - 1 {
            add_inconsistency_issue(i_s, class)
        }
    }
    let mut add_to_mro =
        |base_index: usize, is_direct_base, new_base: &DbType, allowed_to_use: &mut usize| {
            if new_base != &object {
                mro.push(BaseClass {
                    type_: if is_direct_base {
                        *allowed_to_use += 1;
                        new_base.clone()
                    } else {
                        Type::new(new_base).replace_type_var_likes(i_s.db, &mut |t| {
                            bases[base_index].expect_class_generics()[t.index()].clone()
                        })
                    },
                    is_direct_base,
                })
            }
        };

    let mut base_iterators: Vec<_> = bases
        .iter()
        .map(|t| {
            let generic_class = match &t {
                DbType::Class(c) => Some(c),
                DbType::Dataclass(d) => Some(&d.class),
                _ => None,
            };
            let super_classes = if let Some(generic_class) = generic_class {
                let class = Class::from_generic_class(i_s.db, generic_class);
                let cached_class_infos = class.use_cached_class_infos(i_s.db);
                cached_class_infos.mro.as_ref()
            } else {
                &[]
            };
            std::iter::once(t)
                .chain(super_classes.iter().map(|base| &base.type_))
                .enumerate()
                .peekable()
        })
        .collect();
    let mut linearizable = true;
    let mut allowed_to_use = 1;
    'outer: loop {
        let mut had_entry = false;
        for base_index in 0..allowed_to_use.min(bases.len()) {
            if let Some((i, candidate)) = base_iterators[base_index].peek().copied() {
                had_entry = true;
                let conflicts = base_iterators.iter().any(|base_bases| {
                    base_bases
                        .clone()
                        .skip(1)
                        .any(|(_, other)| to_base_kind(candidate) == to_base_kind(other))
                });
                if !conflicts {
                    for base_bases in base_iterators.iter_mut() {
                        base_bases
                            .next_if(|(_, next)| to_base_kind(candidate) == to_base_kind(next));
                    }
                    add_to_mro(base_index, i == 0, candidate, &mut allowed_to_use);
                    continue 'outer;
                }
            }
        }
        if !had_entry {
            break;
        }
        for (base_index, base_bases) in base_iterators.iter_mut().enumerate() {
            if let Some((i, type_)) = base_bases.next() {
                // If it doesn't have to do with one of the first type, it is caused by
                // inconsistencies earlier.
                if bases.contains(type_) {
                    linearizable = false;
                }
                add_to_mro(base_index, i == 0, type_, &mut allowed_to_use);
                continue 'outer;
            }
        }
        unreachable!()
    }
    if !linearizable {
        add_inconsistency_issue(i_s, class)
    }
    mro.into_boxed_slice()
}

fn add_inconsistency_issue(i_s: &InferenceState, class: &Class) {
    NodeRef::new(
        class.node_ref.file,
        class.node().arguments().unwrap().index(),
    )
    .add_issue(
        i_s,
        IssueType::InconsistentMro {
            name: class.name().into(),
        },
    );
}

pub struct MroIterator<'db, 'a> {
    db: &'db Database,
    generics: Generics<'a>,
    class: Option<TypeOrClass<'a>>,
    iterator: std::slice::Iter<'a, BaseClass>,
    mro_index: u32,
    returned_object: bool,
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

#[derive(Debug)]
pub enum TypeOrClass<'a> {
    Type(Type<'a>),
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

    pub fn name<'db: 'a>(&self, db: &'a Database) -> &str {
        match self {
            Self::Class(class) => class.name(),
            Self::Type(t) => match t.as_ref() {
                DbType::Dataclass(d) => d.class(db).name(),
                _ => todo!(),
            },
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
    t: &'a DbType,
    generics: Generics<'a>,
) -> TypeOrClass<'a> {
    match &t {
        DbType::Class(g) => {
            let n = NodeRef::from_link(db, g.link);
            TypeOrClass::Class(match &g.generics {
                ClassGenerics::List(g) => Class::from_position(n, generics, Some(g)),
                ClassGenerics::None => Class::from_position(n, generics, None),
                ClassGenerics::ExpressionWithClassType(link) => todo!("Class::from_position(n, Generics::from_class_generics(self.db, t_generics), None)"),
                ClassGenerics::SlicesWithClassTypes(link) => todo!(),
                ClassGenerics::NotDefinedYet => unreachable!(),
            })
        }
        // TODO this is wrong, because it does not use generics.
        _ if matches!(generics, Generics::None | Generics::NotDefinedYet) => {
            TypeOrClass::Type(Type::new(t))
        }
        _ => TypeOrClass::Type(Type::owned(Type::new(t).replace_type_var_likes_and_self(
            db,
            &mut |usage| generics.nth_usage(db, &usage).into_generic_item(db),
            &|| todo!(),
        ))),
    }
}

fn find_stmt_named_tuple_types(
    i_s: &InferenceState,
    file: &PythonFile,
    vec: &mut Vec<CallableParam>,
    simple_stmts: SimpleStmts,
) {
    for simple in simple_stmts.iter() {
        match simple.unpack() {
            SimpleStmtContent::Assignment(assignment) => match assignment.unpack() {
                AssignmentContent::WithAnnotation(Target::Name(name), annot, default) => {
                    if default.is_none() && vec.last().is_some_and(|last| last.has_default) {
                        NodeRef::new(file, assignment.index())
                            .add_issue(i_s, IssueType::NamedTupleNonDefaultFieldFollowsDefault);
                        continue;
                    }
                    file.inference(i_s).ensure_cached_annotation(annot);
                    let t = use_cached_annotation_type(i_s.db, file, annot).into_db_type();
                    vec.push(CallableParam {
                        param_specific: ParamSpecific::PositionalOrKeyword(t),
                        has_default: default.is_some(),
                        name: Some(StringSlice::from_name(file.file_index(), name.name())),
                    })
                }
                _ => NodeRef::new(file, assignment.index())
                    .add_issue(i_s, IssueType::InvalidStmtInNamedTuple),
            },
            _ => (),
        }
    }
}

fn find_stmt_typed_dict_types(
    i_s: &InferenceState,
    file: &PythonFile,
    vec: &mut Vec<TypedDictMember>,
    simple_stmts: SimpleStmts,
    total: bool,
) {
    for simple in simple_stmts.iter() {
        match simple.unpack() {
            SimpleStmtContent::Assignment(assignment) => match assignment.unpack() {
                AssignmentContent::WithAnnotation(Target::Name(name), annot, default) => {
                    let (type_, has_default) = file
                        .inference(i_s)
                        .compute_class_typed_dict_member(annot, total);
                    vec.push(TypedDictMember {
                        type_,
                        required: !has_default,
                        name: StringSlice::from_name(file.file_index(), name.name()),
                    })
                }
                _ => NodeRef::new(file, assignment.index())
                    .add_issue(i_s, IssueType::InvalidStmtInNamedTuple),
            },
            _ => (),
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
    match (full1.as_ref(), full2.as_ref()) {
        (DbType::Callable(c1), DbType::Callable(c2)) => {
            let s1 = format_pretty_callable(&FormatData::new_short(i_s.db), c1);
            let s2 = format_pretty_callable(&FormatData::new_short(i_s.db), c2);
            notes.push("    Expected:".into());
            notes.push(format!("        {s1}").into());
            notes.push("    Got:".into());
            notes.push(format!("        {s2}").into());
        }
        _ => notes.push(
            format!(
                r#"    {name}: expected "{}", got "{}""#,
                t1.format(&FormatData::with_style(i_s.db, FormatStyle::Qualified)),
                t2.format(&FormatData::with_style(i_s.db, FormatStyle::Qualified))
            )
            .into(),
        ),
    }
}

pub struct NewOrInitConstructor<'a> {
    // A data structure to show wheter __init__ or __new__ is the relevant constructor for a class
    constructor: LookupResult,
    init_class: Option<Class<'a>>,
    is_new: bool,
}

impl NewOrInitConstructor<'_> {
    pub fn maybe_callable(self, i_s: &InferenceState, cls: Class) -> Option<CallableLike> {
        let inf = self.constructor.into_inferred();
        if self.is_new {
            inf.as_type(i_s).maybe_callable(i_s).map(
                |callable_like| /*match self.init_class {
                                       // TODO probably enable??
                    Some(class) => match callable_like {
                        CallableLike::Callable(c) => {
                            CallableLike::Callable(Rc::new(merge_class_type_vars_into_callable(
                                i_s.db,
                                class,
                                class,
                                &c,
                            )))
                        }
                        CallableLike::Overload(overload) => CallableLike::Overload(FunctionOverload::new(overload.iter_functions().map(|c| {
                            dbg!(merge_class_type_vars_into_callable(
                                i_s.db,
                                class,
                                class,
                                &c,
                            ))
                        }).collect()))
                    },
                    None => */callable_like, /*}*/
            )
        } else {
            let callable = if let Some(c) = self.init_class {
                let i_s = &i_s.with_class_context(&c);
                inf.as_type(i_s).maybe_callable(i_s)
            } else {
                inf.as_type(i_s).maybe_callable(i_s)
            };
            callable.and_then(|callable_like| match callable_like {
                CallableLike::Callable(c) => {
                    // Since __init__ does not have a return, We need to check the params
                    // of the __init__ functions and the class as a return type separately.
                    if !c.type_vars.is_empty() {
                        todo!()
                    }
                    c.remove_first_param().map(|mut c| {
                        c.result_type = cls.as_db_type(i_s.db);
                        CallableLike::Callable(Rc::new(c))
                    })
                }
                CallableLike::Overload(_) => todo!(),
            })
        }
    }
}

pub fn start_namedtuple_params(db: &Database) -> Vec<CallableParam> {
    vec![CallableParam {
        param_specific: ParamSpecific::PositionalOnly(db.python_state.type_of_self.clone()),
        has_default: false,
        name: None,
    }]
}
