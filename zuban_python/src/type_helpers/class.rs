use std::fmt;
use std::rc::Rc;

use parsa_python_ast::{
    Argument, AssignmentContent, BlockContent, ClassDef, Decoratee, SimpleStmtContent, SimpleStmts,
    StmtContent, Target,
};

use super::enum_::gather_functional_enum_members;
use super::function::OverloadResult;
use super::{Callable, Instance, Module, NamedTupleValue};
use crate::arguments::{ArgumentKind, Arguments};
use crate::database::{
    BaseClass, CallableContent, CallableParam, CallableParams, ClassGenerics, ClassInfos,
    ClassStorage, ClassType, ComplexPoint, Database, DbType, Enum, EnumMemberDefinition,
    FormatStyle, FunctionKind, GenericClass, GenericsList, Locality, MetaclassState, MroIndex,
    NamedTuple, ParamSpecific, ParentScope, Point, PointLink, PointType, StringSlice, TypeVarLike,
    TypeVarLikeUsage, TypeVarLikes, Variance,
};
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
    calculate_class_init_type_vars_and_return, FormatData, Generics, LookupResult, Match, Matcher,
    MismatchReason, OnTypeError, ResultContext, Type,
};
use crate::node_ref::NodeRef;
use crate::python_state::NAME_TO_FUNCTION_DIFF;
use crate::type_helpers::format_pretty_callable;
use crate::{base_qualified_name, debug};

#[derive(Clone, Copy)]
pub struct Class<'a> {
    pub node_ref: NodeRef<'a>,
    pub class_storage: &'a ClassStorage,
    pub generics: Generics<'a>,
    pub type_var_remap: Option<&'a GenericsList>,
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

    #[inline]
    pub fn from_position(
        node_ref: NodeRef<'a>,
        generics: Generics<'a>,
        type_var_remap: Option<&'a GenericsList>,
    ) -> Self {
        let complex = node_ref.complex().unwrap();
        match complex {
            ComplexPoint::Class(c) => Self::new(node_ref, c, generics, type_var_remap),
            _ => unreachable!("Probably an issue with indexing: {complex:?}"),
        }
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
        args: &dyn Arguments<'db>,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError<'db, '_>,
    ) -> Option<ClassGenerics> {
        let (init, class) =
            self.lookup_and_class_and_maybe_ignore_self_internal(i_s, "__init__", false);
        let Some(inf) = init.into_maybe_inferred() else {
            if self.is_protocol(i_s.db) {
                args.as_node_ref().add_issue(i_s, IssueType::CannotInstantiateProtocol {
                    name: self.name().into()
                })
            } else {
                debug_assert!(self.incomplete_mro(i_s.db));
            }
            return Some(match self.type_vars(i_s) {
                Some(type_vars) => ClassGenerics::List(type_vars.as_any_generic_list()),
                None => ClassGenerics::None,
            })
        };
        match inf.init_as_function(i_s.db, class) {
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
                let calculated_type_args = match class {
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
                        None,
                        Callable::new(&callable_content, Some(*self)),
                        args.iter(),
                        &|| args.as_node_ref(),
                        result_context,
                        Some(on_type_error),
                    ),
                };
                Some(calculated_type_args.type_arguments_into_class_generics())
            }
            Some(FunctionOrOverload::Overload(overloaded_function)) => match overloaded_function
                .find_matching_function(i_s, args, Some(self), true, result_context, on_type_error)
            {
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

    pub fn use_cached_type_vars(&self, db: &Database) -> Option<&'a TypeVarLikes> {
        let node_ref = self.type_vars_node_ref();
        let point = node_ref.point();
        debug_assert!(point.calculated());
        Self::get_calculated_type_vars(node_ref, point)
    }

    fn get_calculated_type_vars(node_ref: NodeRef, point: Point) -> Option<&TypeVarLikes> {
        (point.type_() != PointType::NodeAnalysis).then(|| match node_ref.complex().unwrap() {
            ComplexPoint::TypeVarLikes(type_vars) => type_vars,
            _ => unreachable!(),
        })
    }

    pub fn type_vars(&self, i_s: &InferenceState) -> Option<&'a TypeVarLikes> {
        let node_ref = self.type_vars_node_ref();
        let point = node_ref.point();
        if point.calculated() {
            return Self::get_calculated_type_vars(node_ref, point);
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
                            .and_then(|t| t.find(type_var.clone(), parent_class.node_ref.as_link()))
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
        if !point.calculated() {
            debug_assert!(!name_def.point().calculated());
            // We can redirect now, because we are going to calculate the class infos.
            name_def.set_point(Point::new_redirect(
                self.node_ref.file_index(),
                self.node_ref.node_index,
                Locality::Todo,
            ));

            let node_ref = self.class_info_node_ref();
            node_ref.set_point(Point::new_calculating());
            let mut class_infos = self.calculate_class_infos(i_s);
            if let MetaclassState::Some(link) = class_infos.metaclass {
                if link == i_s.db.python_state.enum_meta_link() {
                    class_infos.class_type = ClassType::Enum;
                    let members = self.enum_members();
                    if !members.is_empty() {
                        let c = ComplexPoint::TypeInstance(DbType::Type(Rc::new(DbType::Enum(
                            Rc::new(Enum {
                                name: self.name_string_slice(),
                                class: self.node_ref.as_link(),
                                members,
                            }),
                        ))));
                        name_def.insert_complex(c, Locality::Todo);
                    }
                }
            }
            node_ref.insert_complex(ComplexPoint::ClassInfos(class_infos), Locality::Todo);
            debug_assert!(node_ref.point().calculated());
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

    fn calculate_class_infos(&self, i_s: &InferenceState<'db, '_>) -> Box<ClassInfos> {
        debug!("Calculate class infos for {}", self.name());
        // Calculate all type vars beforehand
        let type_vars = self.type_vars(i_s);

        let mut mro: Vec<BaseClass> = vec![];
        let mut incomplete_mro = false;
        let mut class_type = ClassType::Normal;
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
                                let c = Class::from_generic_class_components(
                                    i_s.db,
                                    link,
                                    &ClassGenerics::None,
                                );
                                if c.incomplete_mro(i_s.db)
                                    || c.in_mro(
                                        i_s.db,
                                        &DbType::Class(GenericClass {
                                            link: i_s.db.python_state.type_node_ref().as_link(),
                                            generics: ClassGenerics::None,
                                        }),
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
                                /*
                                node_ref.add_issue(
                                    i_s,
                                    IssueType::DynamicMetaclassNotSupported {
                                        class_name: Box::from(self.name()),
                                    },
                                );
                                */
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
                        let db = i_s.db;
                        let mut inference = self.node_ref.file.inference(i_s);
                        let base = TypeComputation::new(
                            &mut inference,
                            self.node_ref.as_link(),
                            &mut |i_s, _: &_, type_var_like: TypeVarLike, _| {
                                if let Some(type_vars) = type_vars {
                                    if let Some(usage) = type_vars
                                        .find(type_var_like.clone(), self.node_ref.as_link())
                                    {
                                        return TypeVarCallbackReturn::TypeVarLike(usage);
                                    }
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
                                let mro_index = mro.len();
                                if let Some(name) = mro.iter().find_map(|base| {
                                    Type::new(&base.type_)
                                        .check_duplicate_base_class(db, &Type::new(&t))
                                }) {
                                    NodeRef::new(self.node_ref.file, n.index())
                                        .add_issue(i_s, IssueType::DuplicateBaseClass { name });
                                    incomplete_mro = true;
                                    continue;
                                }
                                mro.push(BaseClass {
                                    is_direct_base: true,
                                    type_: t,
                                });
                                let class = match &mro.last().unwrap().type_ {
                                    DbType::Class(c) => Some(Class::from_generic_class(i_s.db, c)),
                                    DbType::Tuple(content) => None,
                                    DbType::Callable(content) => None,
                                    _ => unreachable!(),
                                };
                                if let Some(class) = class {
                                    if class.is_calculating_class_infos() {
                                        let name = Box::<str>::from(class.name());
                                        mro.pop();
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
                                        if let ClassType::NamedTuple(named_tuple) =
                                            &cached_class_infos.class_type
                                        {
                                            if matches!(class_type, ClassType::Normal) {
                                                class_type =
                                                    ClassType::NamedTuple(named_tuple.clone());
                                            } else {
                                                todo!()
                                            }
                                        }
                                        for base in cached_class_infos.mro.iter() {
                                            mro.push(BaseClass {
                                                is_direct_base: false,
                                                type_: Type::new(&base.type_)
                                                    .replace_type_var_likes(db, &mut |t| {
                                                        mro[mro_index].type_.expect_class_generics()
                                                            [t.index()]
                                                        .clone()
                                                    }),
                                            });
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
                                mro.push(BaseClass {
                                    type_: DbType::NamedTuple(named_tuple.clone()),
                                    is_direct_base: true,
                                });
                                class_type = ClassType::NamedTuple(named_tuple);
                            }
                            CalculatedBaseClass::NewNamedTuple => {
                                let named_tuple = self
                                    .named_tuple_from_class(&i_s.with_class_context(self), *self);
                                mro.push(BaseClass {
                                    type_: DbType::NamedTuple(named_tuple.clone()),
                                    is_direct_base: true,
                                });
                                class_type = ClassType::NamedTuple(named_tuple);
                            }
                            CalculatedBaseClass::Generic => (),
                            CalculatedBaseClass::Unknown => {
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
        Box::new(ClassInfos {
            mro: mro.into_boxed_slice(),
            metaclass,
            incomplete_mro,
            class_type,
        })
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
        for (mro_index, c) in self.mro_maybe_without_object(i_s.db, true) {
            let TypeOrClass::Class(c) = c else {
                todo!()
            };
            protocol_member_count += c.class_storage.class_symbol_table.len();
            let symbol_table = &c.class_storage.class_symbol_table;
            for (name, _) in unsafe { symbol_table.iter_on_finished_table() } {
                // It is possible to match a Callable against a Protocol that only implements
                // __call__.
                if name == "__call__" {
                    let inf1 = Instance::new(c, None)
                        .lookup(i_s, None, name)
                        .into_inferred();
                    let t1 = inf1.as_type(i_s);
                    if t1.matches(i_s, matcher, other, variance).bool() {
                        continue;
                    }
                }

                if let Some(l) = other.lookup_without_error(i_s, name).into_maybe_inferred() {
                    let inf1 = Instance::new(c, None)
                        .lookup(i_s, None, name)
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
                                    &c.lookup(i_s, None, name).into_inferred().as_type(i_s),
                                    &cls.lookup(i_s, None, name).into_inferred().as_type(i_s),
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
    ) -> (LookupResult, Option<Class>) {
        for (mro_index, c) in self
            .mro_maybe_without_object(i_s.db, self.incomplete_mro(i_s.db))
            .skip(ignore_self as usize)
        {
            let result = c.lookup_symbol(i_s, name);
            if !matches!(result, LookupResult::None) {
                if let TypeOrClass::Class(c) = c {
                    return (result, Some(c));
                } else {
                    return (result, None);
                }
            }
        }
        (LookupResult::None, None)
    }

    pub fn lookup_and_class_and_maybe_ignore_self(
        &self,
        i_s: &InferenceState<'db, '_>,
        name: &str,
        ignore_self: bool,
    ) -> (LookupResult, Option<Class>) {
        self.lookup_with_or_without_descriptors_internal(i_s, None, name, false, ignore_self)
    }

    pub fn lookup_with_or_without_descriptors(
        &self,
        i_s: &InferenceState,
        node_ref: Option<NodeRef>,
        name: &str,
        use_descriptors: bool,
    ) -> LookupResult {
        self.lookup_with_or_without_descriptors_internal(
            i_s,
            node_ref,
            name,
            use_descriptors,
            false,
        )
        .0
    }

    pub fn lookup_with_or_without_descriptors_internal(
        &self,
        i_s: &InferenceState<'db, '_>,
        node_ref: Option<NodeRef>,
        name: &str,
        use_descriptors: bool,
        ignore_self: bool,
    ) -> (LookupResult, Option<Class>) {
        let class_infos = self.use_cached_class_infos(i_s.db);
        if class_infos.class_type == ClassType::Enum && use_descriptors && name == "_ignore_" {
            return (LookupResult::None, Some(*self));
        }
        let (lookup_result, in_class) =
            self.lookup_and_class_and_maybe_ignore_self_internal(i_s, name, ignore_self);
        let result = lookup_result.and_then(|inf| {
            if let Some(in_class) = in_class {
                let i_s = i_s.with_class_context(&in_class);
                inf.bind_class_descriptors(&i_s, self, in_class, node_ref, use_descriptors)
            } else {
                todo!()
            }
        });
        match result {
            Some(LookupResult::None) | None => {
                let result = match class_infos.metaclass {
                    MetaclassState::Some(link) => {
                        let instance = Instance::new(
                            Class::from_generic_class_components(
                                i_s.db,
                                link,
                                &ClassGenerics::None,
                            ),
                            None,
                        );
                        instance.lookup(i_s, node_ref, name)
                    }
                    MetaclassState::Unknown => LookupResult::any(),
                    MetaclassState::None => LookupResult::None,
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

    pub fn in_mro(&self, db: &'db Database, t: &DbType) -> bool {
        if let DbType::Class(c) = t {
            if self.node_ref.as_link() == c.link {
                return true;
            }
        }
        let class_infos = self.use_cached_class_infos(db);
        // TODO this might be an issue with generics.
        class_infos.mro.iter().any(|b| &b.type_ == t)
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
        let type_vars = self.type_vars(&InferenceState::new(format_data.db));
        if let Some(type_vars) = type_vars {
            result += &self.generics().format(format_data, Some(type_vars.len()));
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
        match self.use_cached_type_vars(i_s.db).is_some() {
            false => Inferred::from_saved_node_ref(self.node_ref),
            true => Inferred::from_type(self.as_type(i_s).into_db_type()),
        }
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
        let mut vec = vec![];
        let file = self.node_ref.file;
        match self.node().block().unpack() {
            BlockContent::Indented(stmts) => {
                for stmt in stmts {
                    match stmt.unpack() {
                        StmtContent::SimpleStmts(simple) => {
                            find_stmt_named_tuple_types(i_s, file, &mut vec, simple)
                        }
                        StmtContent::FunctionDef(_) => (),
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
        CallableContent {
            name: Some(name),
            class_name: None,
            defined_at: self.node_ref.as_link(),
            kind: FunctionKind::Function,
            type_vars: self.use_cached_type_vars(i_s.db).cloned(),
            params: CallableParams::Simple(Rc::from(vec)),
            result_type: DbType::None,
        }
    }

    fn enum_members(&self) -> Box<[EnumMemberDefinition]> {
        let mut members = vec![];
        for (name, name_index) in unsafe {
            self.class_storage
                .class_symbol_table
                .iter_on_finished_table()
        } {
            if name.starts_with('_') {
                continue;
            }
            let name_node_ref = NodeRef::new(self.node_ref.file, *name_index);
            if name_node_ref
                .add_to_node_index(-(NAME_TO_FUNCTION_DIFF as i64))
                .maybe_function()
                .is_none()
            {
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

    fn execute_functional_enum(
        &self,
        i_s: &InferenceState,
        args: &dyn Arguments,
        result_context: &mut ResultContext,
    ) -> Inferred {
        let mut iterator = args.iter();
        let Some(name_arg) = iterator.next() else {
            todo!()
        };
        let Some(fields_arg) = iterator.next() else {
            todo!()
        };
        if iterator.next().is_some() {
            todo!()
        }

        let ArgumentKind::Positional { node_ref: name_node_ref, .. } = name_arg.kind else {
            todo!();
            return Inferred::new_any()
        };
        let Some(name) = StringSlice::from_string_in_expression(name_node_ref.file_index(), name_node_ref.as_named_expression().expression()) else {
            todo!()
        };

        let ArgumentKind::Positional { node_ref: fields_node_ref, .. } = fields_arg.kind else {
            todo!();
            return Inferred::new_any()
        };
        let members = gather_functional_enum_members(i_s, fields_node_ref);

        Inferred::from_type(DbType::Type(Rc::new(DbType::Enum(Rc::new(Enum {
            name,
            class: self.node_ref.as_link(),
            members,
        })))))
    }

    pub fn execute(
        &self,
        i_s: &InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError<'db, '_>,
    ) -> Inferred {
        if self.use_cached_class_infos(i_s.db).class_type == ClassType::Enum
            // For whatever reason, auto is special, because
            && self.node_ref.as_link() != i_s.db.python_state.enum_auto_link()
        {
            return self.execute_functional_enum(i_s, args, result_context);
        }
        if let Some(generics) = self.type_check_init_func(
            i_s,
            args,
            result_context,
            on_type_error.with_custom_generate_diagnostic_string(&|_, _, _| {
                Some(format!("\"{}\"", self.name()))
            }),
        ) {
            let result = Inferred::from_type(DbType::Class(GenericClass {
                link: self.node_ref.as_link(),
                generics,
            }));
            debug!("Class execute: {}", result.format_short(i_s));
            result
        } else {
            Inferred::new_any()
        }
    }

    pub fn lookup(
        &self,
        i_s: &InferenceState,
        node_ref: Option<NodeRef>,
        name: &str,
    ) -> LookupResult {
        self.lookup_with_or_without_descriptors(i_s, node_ref, name, true)
    }

    pub fn qualified_name(&self, db: &Database) -> String {
        match self.class_storage.parent_scope {
            ParentScope::Module => base_qualified_name!(self, db, self.name()),
            ParentScope::Class(node_index) => {
                let parent_class =
                    Self::with_undefined_generics(NodeRef::new(self.node_ref.file, node_index));
                format!("{}.{}", parent_class.qualified_name(db), self.name())
            }
            ParentScope::Function(node_index) => {
                let node_ref = NodeRef::new(self.node_ref.file, node_index);
                let line = self
                    .node_ref
                    .file
                    .byte_to_line_column(self.node().start())
                    .0;
                // Add the position like `foo.Bar@7`
                base_qualified_name!(self, db, format!("{}@{line}", self.name()))
            }
        }
    }

    fn module(&self) -> Module<'a> {
        Module::new(self.node_ref.file)
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
        slice_type
            .file
            .inference(i_s)
            .compute_type_application_on_class(
                *self,
                *slice_type,
                matches!(result_context, ResultContext::AssignmentNewDefinition),
            )
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

pub enum TypeOrClass<'a> {
    Type(Type<'a>),
    Class(Class<'a>),
}

impl<'a> TypeOrClass<'a> {
    pub fn lookup_symbol(&self, i_s: &InferenceState, name: &str) -> LookupResult {
        match self {
            Self::Class(class) => class.lookup_symbol(i_s, name),
            Self::Type(t) => t.lookup_symbol(i_s, name),
        }
    }

    pub fn lookup(&self, i_s: &InferenceState, name: &str) -> LookupResult {
        match self {
            Self::Class(class) => class.lookup(i_s, None, name),
            Self::Type(t) => todo!(),
        }
    }

    pub fn name(&self) -> &str {
        match self {
            Self::Class(class) => class.name(),
            Self::Type(t) => todo!(),
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
            &mut || todo!(),
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
                AssignmentContent::WithAnnotation(target, annot, default) => match target {
                    Target::Name(name) => {
                        file.inference(i_s).ensure_cached_annotation(annot);
                        let t = use_cached_annotation_type(i_s.db, file, annot).into_db_type();
                        vec.push(CallableParam {
                            param_specific: ParamSpecific::PositionalOrKeyword(t),
                            has_default: default.is_some(),
                            name: Some(StringSlice::from_name(file.file_index(), name.name())),
                        })
                    }
                    _ => todo!(),
                },
                _ => todo!(),
            },
            _ => todo!(),
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
            let s1 = format_pretty_callable(i_s, c1);
            let s2 = format_pretty_callable(i_s, c2);
            notes.push("    Expected:".into());
            notes.push(format!("        {s1}").into());
            notes.push("    Got:".into());
            notes.push(format!("        {s2}").into());
        }
        _ => notes.push(
            format!(
                r#"    {name}: expected "{}", got "{}""#,
                t1.format_short(i_s.db),
                t2.format_short(i_s.db)
            )
            .into(),
        ),
    }
}
