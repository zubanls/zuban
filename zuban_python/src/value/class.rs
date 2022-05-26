use std::fmt;

use parsa_python_ast::{Argument, ArgumentsIterator, ClassDef};

use super::{
    BoundMethod, CallableClass, Function, Instance, LookupResult, Module, OnTypeError, TupleClass,
    TypingClass, Value, ValueKind,
};
use crate::arguments::{Arguments, ArgumentsType};
use crate::database::{
    ClassInfos, ClassStorage, ComplexPoint, Database, DbType, FormatStyle, GenericsList, Locality,
    MroIndex, PointLink, Specific, TypeVarManager, TypeVarType, TypeVarUsage, TypeVars, Variance,
};
use crate::debug;
use crate::file::{BaseClass, PythonFile, TypeComputation};
use crate::file_state::File;
use crate::generics::{Generics, Type, TypeVarMatcher};
use crate::getitem::SliceType;
use crate::inference_state::InferenceState;
use crate::inferred::{FunctionOrOverload, Inferred};
use crate::node_ref::NodeRef;

#[derive(Debug, Clone, Copy)]
pub enum ClassLike<'db, 'a> {
    Class(Class<'db, 'a>),
    Tuple(TupleClass<'a>),
    Callable(CallableClass<'a>),
    FunctionType(Function<'db, 'a>),
    Type(Class<'db, 'a>),
    TypeWithDbType(&'a DbType),
    TypingClass(TypingClass),
    TypingClassType(TypingClass),
    AnyType,
}

impl<'db, 'a> ClassLike<'db, 'a> {
    pub fn matches(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        value_class: Type<'db, '_>,
        mut matcher: Option<&mut TypeVarMatcher<'db, '_>>,
        variance: Variance,
    ) -> bool {
        // Note: we need to handle the MRO _in order_, so we need to extract
        // the elements from the set first, then handle them, even if we put
        // them back in a set afterwards.
        // TODO use type_var_remap
        match value_class {
            Type::ClassLike(c) => {
                match variance {
                    Variance::Covariant => {
                        for (mro_index, class_like) in c.mro(i_s) {
                            if self.check_match(i_s, matcher.as_deref_mut(), &class_like, variance)
                            {
                                return true;
                            }
                        }
                    }
                    Variance::Invariant => {
                        if self.check_match(i_s, matcher.as_deref_mut(), &c, variance) {
                            return true;
                        }
                    }
                    Variance::Contravariant => todo!(),
                    Variance::Bivariant => todo!(),
                }
                // TODO this should probably be checked before normal mro checking?!
                if let Self::Class(c1) = self {
                    if c1.class_infos(i_s).is_protocol {
                        return match c {
                            ClassLike::Class(c2) => c1.check_protocol_match(i_s, c2),
                            _ => false,
                        };
                    }
                }
                false
            }
            Type::TypeVar(t) => false,
            Type::Union(list) => false,
            Type::None | Type::Unknown => true, // TODO should be false
            Type::Any => true,
        }
    }

    fn check_match(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        mut matcher: Option<&mut TypeVarMatcher<'db, '_>>,
        other: &Self,
        variance: Variance,
    ) -> bool {
        let mut matches = match self {
            Self::Class(c1) => match other {
                Self::Class(c2) => {
                    if c1.reference == c2.reference {
                        let type_vars = c1.type_vars(i_s);
                        return c1.generics().matches(
                            i_s,
                            matcher.as_deref_mut(),
                            c2.generics(),
                            variance,
                            Some(type_vars),
                        );
                    }
                    false
                }
                _ => false,
            },
            Self::Type(_) | Self::TypeWithDbType(_) => {
                matches!(other, Self::Type(_) | Self::TypeWithDbType(_))
            }
            Self::Tuple(_) => matches!(other, Self::Tuple(_)),
            Self::Callable(c) => matches!(other, Self::Callable(_) | Self::FunctionType(_)),
            Self::FunctionType(f) => unreachable!(),
            Self::TypingClass(c) => match other {
                Self::Tuple(c2) => c.specific == Specific::TypingTuple,
                _ => todo!(),
            },
            Self::TypingClassType(c) => todo!(),
            Self::AnyType => todo!(),
        };
        if matches {
            let (class_generics, class_result_generics) = self.generics();
            let (value_generics, value_result_generics) = other.generics();

            matches &=
                class_generics.matches(i_s, matcher.as_deref_mut(), value_generics, variance, None);
            // Result generics are only relevant for callables/functions
            if let Some(class_result_generics) = class_result_generics {
                matches &= class_result_generics.matches(
                    i_s,
                    matcher,
                    value_result_generics.unwrap(),
                    variance,
                    None,
                );
            }
        }
        matches
    }

    pub fn matches_type_var(&self, t1: &TypeVarUsage) -> bool {
        if let ClassLike::TypeWithDbType(DbType::TypeVar(t2)) = self {
            t1.index == t2.index && t1.type_ == t2.type_
        } else {
            false
        }
    }

    fn generics(&self) -> (Generics<'db, '_>, Option<Generics<'db, '_>>) {
        match self {
            Self::Class(c) => (c.generics(), None),
            Self::Type(c) => (Generics::Class(c), None),
            Self::TypeWithDbType(g) => (Generics::DbType(g), None),
            Self::Tuple(c) => (c.generics(), None),
            Self::Callable(c) => (c.param_generics(), Some(c.result_generics())),
            Self::FunctionType(f) => (Generics::FunctionParams(f), Some(f.result_generics())),
            Self::TypingClass(_) | Self::TypingClassType(_) | Self::AnyType => {
                (Generics::None, None)
            }
        }
    }

    pub fn as_string(&self, i_s: &mut InferenceState<'db, '_>, style: FormatStyle) -> String {
        match self {
            Self::Class(c) => c.as_string(i_s, style),
            Self::Type(c) => format!("Type[{}]", c.as_string(i_s, style)),
            Self::TypeWithDbType(g) => g.as_type_string(i_s.database, None, style),
            Self::Tuple(c) => c.as_type_string(i_s.database, style),
            Self::Callable(c) => c.description(i_s),
            Self::FunctionType(f) => f.as_type_string(i_s, style),
            Self::TypingClass(c) => todo!(),
            Self::TypingClassType(c) => todo!(),
            // TODO this does not respect formatstyle
            Self::AnyType => "builtins.type".to_owned(),
        }
    }

    pub fn mro(&self, i_s: &mut InferenceState<'db, '_>) -> MroIterator<'db, '_> {
        match self {
            Self::Class(c) => c.mro(i_s),
            _ => MroIterator {
                database: i_s.database,
                generics: None,
                class: Some(*self),
                iterator: [].iter(),
                mro_index: 0,
                returned_object: false,
            },
        }
    }

    pub fn lookup_symbol(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        name: &str,
    ) -> LookupResult<'db> {
        match self {
            Self::Class(c) => c.lookup_symbol(i_s, name),
            Self::Type(c) => todo!(),
            _ => todo!(),
        }
    }

    pub fn as_db_type(&self, i_s: &mut InferenceState<'db, '_>) -> DbType {
        match self {
            Self::Class(c) => c.as_db_type(i_s),
            Self::Type(c) => DbType::Type(Box::new(c.as_db_type(i_s))),
            Self::TypeWithDbType(g) => (*g).clone(),
            Self::Tuple(t) => t.as_db_type(),
            Self::Callable(c) => c.as_db_type(),
            Self::FunctionType(f) => todo!(),
            Self::TypingClass(c) => c.as_db_type(),
            Self::TypingClassType(c) => todo!(),
            Self::AnyType => DbType::Type(Box::new(DbType::Any)),
        }
    }
}

#[derive(Clone, Copy)]
pub struct Class<'db, 'a> {
    pub reference: NodeRef<'db>,
    pub class_storage: &'db ClassStorage,
    generics: Generics<'db, 'a>,
    type_var_remap: Option<&'db GenericsList>,
}

impl<'db, 'a> Class<'db, 'a> {
    pub fn new(
        reference: NodeRef<'db>,
        class_storage: &'db ClassStorage,
        generics: Generics<'db, 'a>,
        type_var_remap: Option<&'db GenericsList>,
    ) -> Self {
        Self {
            reference,
            class_storage,
            generics,
            type_var_remap,
        }
    }

    #[inline]
    pub fn from_position(
        reference: NodeRef<'db>,
        generics: Generics<'db, 'a>,
        type_var_remap: Option<&'db GenericsList>,
    ) -> Option<Self> {
        let complex = reference.complex().unwrap();
        match complex {
            ComplexPoint::Class(c) => Some(Self::new(reference, c, generics, type_var_remap)),
            _ => unreachable!("Probably an issue with indexing: {:?}", &complex),
        }
    }

    fn init_func(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        on_type_error: OnTypeError<'db, '_>,
    ) -> (Function<'db, '_>, Option<GenericsList>, bool) {
        let (init, class) = self.lookup_and_class(i_s, "__init__");
        let has_generics = !matches!(self.generics, Generics::None);
        let cls = class.unwrap_or_else(|| todo!());
        match init.into_maybe_inferred().unwrap().init_as_function(cls) {
            Some(FunctionOrOverload::Function(func)) => {
                // TODO does this work with inheritance and type var remapping
                let type_vars = self.type_vars(i_s);
                let list = if has_generics {
                    self.generics.as_generics_list(i_s)
                } else {
                    TypeVarMatcher::calculate_and_return(
                        i_s,
                        Some(self),
                        &func,
                        args,
                        true,
                        Some(type_vars),
                        TypeVarType::Class,
                        on_type_error,
                    )
                };
                return (func, list, false);
            }
            Some(FunctionOrOverload::Overload(overloaded_function)) => {
                if let Some((func, list)) = overloaded_function.find_matching_function(
                    i_s,
                    args,
                    class.as_ref(),
                    on_type_error,
                ) {
                    if has_generics {
                        todo!()
                    }
                    return (func, list, true);
                } else {
                    todo!()
                }
            }
            None => (),
        };
        unreachable!("Should never happen, because there's always object.__init__")
    }

    pub fn simple_init_func(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
    ) -> Function<'db, '_> {
        let (init, class) = self.lookup_and_class(i_s, "__init__");
        let class = class.unwrap_or_else(|| todo!());
        match init.into_maybe_inferred().unwrap().init_as_function(class) {
            Some(FunctionOrOverload::Function(func)) => func,
            _ => unreachable!(),
        }
    }

    fn node(&self) -> ClassDef<'db> {
        ClassDef::by_index(&self.reference.file.tree, self.reference.node_index)
    }

    pub fn type_vars(&self, i_s: &mut InferenceState<'db, '_>) -> &'db TypeVars {
        &self.class_infos(i_s).type_vars
    }

    pub fn class_infos(&self, i_s: &mut InferenceState<'db, '_>) -> &'db ClassInfos {
        let reference = self.reference.add_to_node_index(1);
        let point = reference.point();
        if point.calculated() {
            match reference.complex().unwrap() {
                ComplexPoint::ClassInfos(class_infos) => class_infos,
                _ => unreachable!(),
            }
        } else {
            reference.insert_complex(
                ComplexPoint::ClassInfos(self.calculate_class_infos(i_s)),
                Locality::Todo,
            );
            debug_assert!(reference.point().calculated());
            self.class_infos(i_s)
        }
    }

    fn calculate_class_infos(&self, i_s: &mut InferenceState<'db, '_>) -> Box<ClassInfos> {
        debug!("Calculate class infos for {}", self.name());
        let mut mro = vec![];
        let mut type_vars = TypeVarManager::default();
        let mut i_s = i_s.with_annotation_instance();
        let mut is_protocol = false;
        let mut incomplete_mro = false;
        if let Some(arguments) = self.node().arguments() {
            // Calculate the type var remapping
            for argument in arguments.iter() {
                match argument {
                    Argument::Positional(n) => {
                        let mut inference = self.reference.file.inference(&mut i_s);
                        let base = TypeComputation::new(&mut inference, &mut |_, type_var| {
                            let index = type_vars.add(type_var.clone());
                            TypeVarUsage {
                                type_var,
                                index,
                                type_: TypeVarType::Class,
                            }
                        })
                        .compute_base_class(n.expression());
                        match base {
                            BaseClass::DbType(t) => {
                                let mro_index = mro.len();
                                mro.push(t);
                                let class = match &mro.last().unwrap() {
                                    DbType::Class(link) => {
                                        let r = NodeRef::from_link(i_s.database, *link);
                                        Some(Self::from_position(r, Generics::None, None).unwrap())
                                    }
                                    DbType::GenericClass(link, generics) => Some(
                                        Class::from_position(
                                            NodeRef::from_link(i_s.database, *link),
                                            Generics::new_list(generics),
                                            None,
                                        )
                                        .unwrap(),
                                    ),
                                    DbType::Tuple(content) => todo!(),
                                    DbType::Callable(content) => todo!(),
                                    _ => {
                                        incomplete_mro = true;
                                        mro.pop();
                                        None
                                    }
                                };
                                if let Some(class) = class {
                                    for base in class.class_infos(&mut i_s).mro.iter() {
                                        mro.push(base.remap_type_vars(&mut |t| {
                                            mro[mro_index]
                                                .expect_generics()
                                                .nth(t.index)
                                                .unwrap()
                                                .clone()
                                        }));
                                    }
                                }
                            }
                            BaseClass::Protocol => is_protocol = true,
                            BaseClass::Generic => (),
                        };
                    }
                    Argument::Keyword(_, _) => (), // Ignore for now -> part of meta class
                    Argument::Starred(_) | Argument::DoubleStarred(_) => (), // Nobody probably cares about this
                }
            }
        }
        Box::new(ClassInfos {
            type_vars: type_vars.into_boxed_slice(),
            mro: mro.into_boxed_slice(),
            incomplete_mro,
            is_protocol,
        })
    }

    fn check_protocol_match(&self, i_s: &mut InferenceState<'db, '_>, other: Self) -> bool {
        for c in self.class_infos(i_s).mro.iter() {
            let symbol_table = &self.class_storage.class_symbol_table;
            for (class_name, _) in unsafe { symbol_table.iter_on_finished_table() } {
                if let Some(l) = other.lookup_internal(i_s, class_name).into_maybe_inferred() {
                    // TODO check signature details here!
                } else {
                    return false;
                }
            }
        }
        true
    }

    fn lookup_symbol(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> LookupResult<'db> {
        match self.class_storage.class_symbol_table.lookup_symbol(name) {
            None => LookupResult::None,
            Some(node_index) => {
                let inf = self
                    .reference
                    .file
                    .inference(&mut i_s.with_class_context(self))
                    .infer_name_by_index(node_index);
                LookupResult::GotoName(
                    PointLink::new(self.reference.file.file_index(), node_index),
                    inf,
                )
            }
        }
    }

    fn lookup_and_class(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        name: &str,
    ) -> (LookupResult<'db>, Option<Class<'db, '_>>) {
        for (mro_index, c) in self.mro(i_s) {
            let result = c.lookup_symbol(i_s, name);
            if !matches!(result, LookupResult::None) {
                if let ClassLike::Class(c) = c {
                    return (result, Some(c));
                } else {
                    todo!()
                    //return (result, None);
                }
            }
        }
        (LookupResult::None, None)
    }

    pub fn generics(&self) -> Generics<'db, '_> {
        if let Some(type_var_remap) = self.type_var_remap {
            Generics::List(type_var_remap, Some(&self.generics))
        } else {
            self.generics
        }
    }

    pub fn mro(&self, i_s: &mut InferenceState<'db, '_>) -> MroIterator<'db, '_> {
        let class_infos = self.class_infos(i_s);
        MroIterator {
            database: i_s.database,
            generics: Some(self.generics),
            class: Some(ClassLike::Class(*self)),
            mro_index: 0,
            iterator: class_infos.mro.iter(),
            returned_object: false,
        }
    }

    pub fn as_string(&self, i_s: &mut InferenceState<'db, '_>, style: FormatStyle) -> String {
        let mut result = match style {
            FormatStyle::Short => self.name().to_owned(),
            FormatStyle::Qualified => self.qualified_name(i_s.database),
        };
        let type_var_count = self.class_infos(i_s).type_vars.len();
        if type_var_count > 0 {
            result += &self.generics().as_string(i_s, style, Some(type_var_count));
        }
        result
    }

    fn as_db_type(&self, i_s: &mut InferenceState<'db, '_>) -> DbType {
        let lst = self.generics().as_generics_list(i_s);
        let link = self.reference.as_link();
        lst.map(|lst| DbType::GenericClass(link, lst))
            .unwrap_or_else(|| DbType::Class(link))
    }
}

impl<'db, 'a> Value<'db, 'a> for Class<'db, 'a> {
    fn kind(&self) -> ValueKind {
        ValueKind::Class
    }

    fn name(&self) -> &'db str {
        self.node().name().as_str()
    }

    fn module(&self, db: &'db Database) -> Module<'db> {
        Module::new(db, self.reference.file)
    }

    fn lookup_internal(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> LookupResult<'db> {
        self.lookup_and_class(i_s, name).0
    }

    fn should_add_lookup_error(&self, i_s: &mut InferenceState<'db, '_>) -> bool {
        !self.class_infos(i_s).incomplete_mro
    }

    fn execute(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        on_type_error: OnTypeError<'db, '_>,
    ) -> Inferred<'db> {
        // TODO locality!!!
        let (func, generics_list, is_overload) = self.init_func(i_s, args, on_type_error);
        if args.outer_execution().is_some() || !self.type_vars(i_s).is_empty() || is_overload {
            debug!(
                "Class execute: {}{}",
                self.name(),
                match generics_list.as_ref() {
                    Some(generics_list) =>
                        Generics::new_list(generics_list).as_string(i_s, FormatStyle::Short, None),
                    None => "".to_owned(),
                }
            );
            let inf = Inferred::new_unsaved_complex(match generics_list {
                None => ComplexPoint::ExecutionInstance(
                    self.reference.as_link(),
                    Box::new(args.as_execution(&func).unwrap()),
                ),
                Some(generics_list) => {
                    ComplexPoint::Instance(self.reference.as_link(), Some(generics_list))
                }
            });
            if !matches!(self.generics, Generics::None) {
                let instance = Instance::new(*self, &inf);
                let m = BoundMethod::new(&instance, MroIndex(0), &func);
                m.execute(i_s, args, on_type_error);
            }
            inf
        } else {
            // TODO this is weird.
            match args.type_() {
                ArgumentsType::Normal(file, primary_node_index) => {
                    Inferred::new_unsaved_specific(Specific::InstanceWithArguments)
                }
            }
        }
    }

    fn get_item(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        slice_type: &SliceType<'db>,
    ) -> Inferred<'db> {
        slice_type
            .file
            .inference(i_s)
            .compute_type_get_item_on_class(*self, *slice_type)
    }

    fn as_class(&self) -> Option<&Self> {
        Some(self)
    }

    fn as_class_like(&self) -> Option<ClassLike<'db, 'a>> {
        Some(ClassLike::Class(*self))
    }

    fn description(&self, i_s: &mut InferenceState<'db, '_>) -> String {
        format!(
            "{} {}",
            format!("{:?}", self.kind()).to_lowercase(),
            self.as_string(i_s, FormatStyle::Short),
        )
    }

    fn class(&self, i_s: &mut InferenceState<'db, '_>) -> ClassLike<'db, 'a> {
        ClassLike::Type(*self)
    }
}

impl fmt::Debug for Class<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("Class")
            .field("file", &self.reference.file)
            .field("name", &self.name())
            .field("generics", &self.generics)
            .field("type_var_remap", &self.type_var_remap)
            .finish()
    }
}

struct BasesIterator<'db> {
    file: &'db PythonFile,
    args: Option<ArgumentsIterator<'db>>,
}

impl<'db> BasesIterator<'db> {
    fn next(&mut self, i_s: &mut InferenceState<'db, '_>) -> Option<Inferred<'db>> {
        if let Some(args) = self.args.as_mut() {
            match args.next() {
                Some(Argument::Positional(p)) => {
                    return Some(self.file.inference(i_s).infer_named_expression(p))
                }
                None => (),
                other => todo!("{:?}", other),
            }
        }
        None
    }
}

pub struct MroIterator<'db, 'a> {
    database: &'db Database,
    generics: Option<Generics<'db, 'a>>,
    class: Option<ClassLike<'db, 'a>>,
    iterator: std::slice::Iter<'db, DbType>,
    mro_index: u32,
    returned_object: bool,
}

impl<'db, 'a> Iterator for MroIterator<'db, 'a> {
    type Item = (MroIndex, ClassLike<'db, 'a>);

    fn next(&mut self) -> Option<Self::Item> {
        if self.class.is_some() {
            self.mro_index += 1;
            Some((
                MroIndex(0),
                std::mem::replace(&mut self.class, None).unwrap(),
            ))
        } else if let Some(c) = self.iterator.next() {
            let r = Some((
                MroIndex(self.mro_index),
                match c {
                    DbType::Class(c) => ClassLike::Class(
                        Class::from_position(
                            NodeRef::from_link(self.database, *c),
                            self.generics.unwrap(),
                            None,
                        )
                        .unwrap(),
                    ),
                    DbType::GenericClass(c, generics) => ClassLike::Class(
                        Class::from_position(
                            NodeRef::from_link(self.database, *c),
                            self.generics.unwrap(),
                            Some(generics),
                        )
                        .unwrap(),
                    ),
                    _ => todo!("{:?}", c),
                },
            ));
            self.mro_index += 1;
            r
        } else if !self.returned_object {
            self.returned_object = true;
            Class::from_position(self.database.python_state.object(), Generics::None, None)
                .map(|c| (MroIndex(self.mro_index), ClassLike::Class(c)))
        } else {
            None
        }
    }
}
