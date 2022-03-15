use parsa_python_ast::{Argument, ArgumentsIterator, ClassDef, SliceType as ASTSliceType};

use super::{CallableClass, Function, Module, TupleClass, TypingClass, Value, ValueKind};
use crate::arguments::{Arguments, ArgumentsType};
use crate::database::{
    ClassInfos, ClassStorage, ComplexPoint, Database, FormatStyle, GenericPart, GenericsList,
    Locality, MroIndex, PointLink, Specific, TypeVarIndex,
};
use crate::debug;
use crate::diagnostics::IssueType;
use crate::file::PythonFile;
use crate::generics::{search_type_vars, GenericOption, Generics, TypeVarMatcher};
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
    TypeWithGenericPart(&'a GenericPart),
    TypingClass(TypingClass),
    AnyType,
}

impl<'db, 'a> ClassLike<'db, 'a> {
    pub fn matches(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        value_class: GenericOption<'db, '_>,
        mut matcher: Option<&mut TypeVarMatcher<'db, '_>>,
    ) -> bool {
        // Note: we need to handle the MRO _in order_, so we need to extract
        // the elements from the set first, then handle them, even if we put
        // them back in a set afterwards.
        // TODO use type_var_remap
        match value_class {
            GenericOption::ClassLike(c) => {
                for (mro_index, class_like) in c.mro(i_s) {
                    if self.check_match(i_s, matcher.as_deref_mut(), &class_like) {
                        return true;
                    }
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
            GenericOption::TypeVar(_, node_ref) => todo!(),
            GenericOption::Union(list) => false,
            GenericOption::None | GenericOption::Unknown => true, // TODO should be false
            GenericOption::Any => true,
        }
    }

    fn check_match(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        mut matcher: Option<&mut TypeVarMatcher<'db, '_>>,
        other: &Self,
    ) -> bool {
        let mut matches = match self {
            Self::Class(c1) => match other {
                Self::Class(c2) => c1.reference == c2.reference,
                _ => false,
            },
            Self::Type(_) | Self::TypeWithGenericPart(_) => {
                matches!(other, Self::Type(_) | Self::TypeWithGenericPart(_))
            }
            Self::Tuple(_) => matches!(other, Self::Tuple(_)),
            Self::Callable(c) => matches!(other, Self::Callable(_) | Self::FunctionType(_)),
            Self::FunctionType(f) => unreachable!(),
            Self::TypingClass(c) => todo!(),
            Self::AnyType => todo!(),
        };
        if matches {
            let (class_generics, class_result_generics) = self.generics();
            let (value_generics, value_result_generics) = other.generics();

            matches &= class_generics.matches(i_s, matcher.as_deref_mut(), value_generics);
            // Result generics are only relevant for callables/functions
            if let Some(class_result_generics) = class_result_generics {
                matches &=
                    class_result_generics.matches(i_s, matcher, value_result_generics.unwrap());
            }
        }
        matches
    }

    #[inline]
    fn generics(&self) -> (Generics<'db, '_>, Option<Generics<'db, '_>>) {
        match self {
            Self::Class(c) => (c.generics(), None),
            Self::Type(c) => (Generics::Class(c), None),
            Self::TypeWithGenericPart(g) => (Generics::GenericPart(g), None),
            Self::Tuple(c) => (c.generics(), None),
            Self::Callable(c) => (c.param_generics(), Some(c.result_generics())),
            Self::FunctionType(f) => (Generics::FunctionParams(f), Some(f.result_generics())),
            Self::TypingClass(_) | Self::AnyType => (Generics::None, None),
        }
    }

    pub fn as_string(&self, i_s: &mut InferenceState<'db, '_>, style: FormatStyle) -> String {
        match self {
            Self::Class(c) => c.as_string(i_s, style),
            Self::Type(c) => format!("Type[{}]", c.as_string(i_s, style)),
            Self::TypeWithGenericPart(g) => {
                format!("Type[{}]", g.as_type_string(i_s.database, None, style))
            }
            Self::Tuple(c) => c.as_type_string(i_s.database, style),
            Self::Callable(c) => c.description(i_s),
            Self::FunctionType(f) => f.as_type_string(i_s, style),
            Self::TypingClass(c) => todo!(),
            Self::AnyType => "Type[Any]".to_owned(),
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
    ) -> Option<Inferred<'db>> {
        match self {
            Self::Class(c) => c.lookup_symbol(i_s, name),
            Self::Type(c) => todo!(),
            _ => todo!(),
        }
    }

    pub fn as_generic_part(&self, i_s: &mut InferenceState<'db, '_>) -> GenericPart {
        match self {
            Self::Class(c) => c.as_generic_part(i_s),
            Self::Type(c) => GenericPart::Type(Box::new(c.as_generic_part(i_s))),
            Self::TypeWithGenericPart(g) => GenericPart::Type(Box::new((*g).clone())),
            Self::Tuple(t) => t.as_generic_part(),
            Self::Callable(c) => c.as_generic_part(),
            Self::FunctionType(f) => todo!(),
            Self::TypingClass(c) => c.as_generic_part(),
            Self::AnyType => GenericPart::Type(Box::new(GenericPart::Any)),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Class<'db, 'a> {
    pub reference: NodeRef<'db>,
    pub(super) class_storage: &'db ClassStorage,
    generics: Generics<'db, 'a>,
    pub type_var_remap: Option<&'db GenericsList>,
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

    pub fn init_func(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
    ) -> (Function<'db, '_>, Option<GenericsList>) {
        let (init, class) = self.lookup_and_class(i_s, "__init__");
        match init.init_as_function(self) {
            Some(FunctionOrOverload::Function(func)) => {
                // TODO does this work with inheritance and type var remapping
                let type_vars = self.type_vars(i_s);
                let list = TypeVarMatcher::calculate_and_return(
                    i_s,
                    &func,
                    args,
                    true,
                    Some(type_vars),
                    Specific::ClassTypeVar,
                );
                return (func, list);
            }
            Some(FunctionOrOverload::Overload(overloaded_function)) => {
                if let Some((func, list)) =
                    overloaded_function.find_matching_function(i_s, args, class.as_ref())
                {
                    return (func, list);
                } else {
                    todo!()
                }
            }
            None => (),
        };
        unreachable!("Should never happen, because there's always object.__init__")
    }

    pub fn node(&self) -> ClassDef<'db> {
        ClassDef::by_index(&self.reference.file.tree, self.reference.node_index)
    }

    pub fn type_vars(&self, i_s: &mut InferenceState<'db, '_>) -> &'db [PointLink] {
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
        let mut type_vars = vec![];
        let mut i_s = i_s.with_annotation_instance();
        let mut is_protocol = false;
        let mut incomplete_mro = false;
        if let Some(arguments) = self.node().arguments() {
            // First search for type vars
            for argument in arguments.iter() {
                if let Argument::Positional(n) = argument {
                    search_type_vars(
                        &mut i_s,
                        self.reference.file,
                        &n.expression(),
                        &mut |_, _| Some(Specific::ClassTypeVar),
                        &mut type_vars,
                        false,
                    );
                }
            }
            // Then calculate the type var remapping
            for argument in arguments.iter() {
                match argument {
                    Argument::Positional(n) => {
                        let inf = self
                            .reference
                            .file
                            .inference(&mut i_s)
                            .infer_named_expression(n);
                        inf.run_mut(
                            &mut i_s,
                            &mut |i_s, v| {
                                if let Some(class) = v.as_class() {
                                    let mro_index = mro.len();
                                    // TODO handle Tuple and other ClassLike's here
                                    mro.push(create_mro_class(
                                        i_s,
                                        self.reference,
                                        &type_vars,
                                        class,
                                    ));
                                    for base in class.class_infos(i_s).mro.iter() {
                                        mro.push(base.remap_type_vars(&mut |i| {
                                            mro[mro_index].expect_generics().nth(i).unwrap().clone()
                                        }));
                                    }
                                } else if let Some(t) = v.as_typing_with_generics(i_s) {
                                    if t.specific == Specific::TypingProtocol {
                                        is_protocol = true;
                                    }
                                } else if let Some(t) = v.as_typing_class() {
                                    if t.specific == Specific::TypingProtocol {
                                        is_protocol = true;
                                    }
                                }
                            },
                            || incomplete_mro = true,
                        )
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
                if let Some(l) = other.lookup_internal(i_s, class_name) {
                    // TODO check signature details here!
                } else {
                    return false;
                }
            }
        }
        true
    }

    fn lookup_symbol(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        name: &str,
    ) -> Option<Inferred<'db>> {
        self.class_storage
            .class_symbol_table
            .lookup_symbol(name)
            .map(|node_index| {
                self.reference
                    .file
                    .inference(i_s)
                    .infer_name_by_index(node_index)
            })
    }

    fn lookup_and_class(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        name: &str,
    ) -> (Inferred<'db>, Option<Class<'db, '_>>) {
        for (mro_index, c) in self.mro(i_s) {
            if let Some(inf) = c.lookup_symbol(i_s, name) {
                if let ClassLike::Class(c) = c {
                    return (inf, Some(c));
                } else {
                    return (inf, None);
                }
            }
        }
        (Inferred::new_unknown(), None)
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
            let generics_string = match self.type_var_remap {
                Some(type_var_remap) => format!(
                    "[{}]",
                    type_var_remap.as_string(
                        i_s.database,
                        Some(&mut |index| self.generics.nth(i_s, index)),
                        style,
                    )
                ),
                None => self.generics.as_string(i_s, style, Some(type_var_count)),
            };

            result += &generics_string;
        }
        result
    }

    pub fn as_generic_part(&self, i_s: &mut InferenceState<'db, '_>) -> GenericPart {
        let lst = self.generics.as_generics_list(i_s);
        let link = self.reference.as_link();
        lst.map(|lst| GenericPart::GenericClass(link, lst))
            .unwrap_or_else(|| GenericPart::Class(link))
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

    fn lookup_internal(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        name: &str,
    ) -> Option<Inferred<'db>> {
        Some(self.lookup_and_class(i_s, name).0)
    }

    fn should_add_lookup_error(&self, i_s: &mut InferenceState<'db, '_>) -> bool {
        !self.class_infos(i_s).incomplete_mro
    }

    fn execute(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
    ) -> Inferred<'db> {
        // TODO locality!!!
        if args.outer_execution().is_some() || !self.type_vars(i_s).is_empty() {
            if !matches!(self.generics, Generics::None) {
                todo!()
            }
            let (func, generics_list) = self.init_func(i_s, args);
            debug!(
                "Class execute: {}{}",
                self.name(),
                match generics_list.as_ref() {
                    Some(generics_list) =>
                        Generics::new_list(generics_list).as_string(i_s, FormatStyle::Short, None),
                    None => "".to_owned(),
                }
            );
            Inferred::new_unsaved_complex(match generics_list {
                None => ComplexPoint::ExecutionInstance(
                    self.reference.as_link(),
                    Box::new(args.as_execution(&func).unwrap()),
                ),
                Some(generics_list) => {
                    ComplexPoint::Instance(self.reference.as_link(), Some(generics_list))
                }
            })
        } else {
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
        // TODO both the type argument issues and are not implemented for other classlikes like
        // tuple/callable/type, which can also have late bound type vars and too many/few given
        // type vars!
        let count_given = match slice_type.ast_node {
            ASTSliceType::Slices(s) => s.iter().count(),
            _ => 1,
        };
        let expected = self.class_infos(i_s).type_vars.len();
        if count_given != expected {
            slice_type.as_node_ref().add_typing_issue(
                i_s.database,
                IssueType::TypeArgumentIssue(self.name().to_owned(), expected, count_given),
            );
        }
        Inferred::new_unsaved_specific(Specific::SimpleGeneric)
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
    iterator: std::slice::Iter<'db, GenericPart>,
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
                    GenericPart::Class(c) => ClassLike::Class(
                        Class::from_position(
                            NodeRef::from_link(self.database, *c),
                            self.generics.unwrap(),
                            None,
                        )
                        .unwrap(),
                    ),
                    GenericPart::GenericClass(c, generics) => ClassLike::Class(
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

fn create_type_var_remap<'db>(
    i_s: &mut InferenceState<'db, '_>,
    original_class: NodeRef<'db>,
    original_type_vars: &[PointLink],
    generic: GenericOption<'db, '_>,
) -> GenericPart {
    match generic {
        GenericOption::ClassLike(class) => create_mro_class(
            i_s,
            original_class,
            original_type_vars,
            match &class {
                ClassLike::Class(class) => class,
                _ => todo!(),
            },
        ),
        GenericOption::TypeVar(type_var_index, reference) => {
            GenericPart::TypeVar(type_var_index, reference.as_link())
        }
        GenericOption::Union(list) => todo!(),
        GenericOption::Unknown | GenericOption::None | GenericOption::Any => todo!(),
    }
}

fn create_mro_class<'db>(
    i_s: &mut InferenceState<'db, '_>,
    original_class: NodeRef<'db>,
    original_type_vars: &[PointLink],
    class: &Class<'db, '_>,
) -> GenericPart {
    let type_vars = if class.reference == original_class {
        // We need to use the original type vars here, because there can be a recursion in there,
        // like `class str(Sequence[str])`, which means that the class info must not be fetched,
        // because it does not exist yet, i.e. it would lead to a stack overflow.
        original_type_vars
    } else {
        class.type_vars(i_s)
    };
    if type_vars.is_empty() {
        GenericPart::Class(class.reference.as_link())
    } else {
        let iterator = class.generics.iter();
        let mut type_var_remap = GenericsList::new_unknown(type_vars.len());
        let mut i = 0;
        iterator.run_on_all_generic_options(i_s, |i_s, generic_option| {
            let r = create_type_var_remap(i_s, original_class, original_type_vars, generic_option);
            type_var_remap.set_generic(TypeVarIndex::new(i), r);
            i += 1;
        });
        GenericPart::GenericClass(class.reference.as_link(), type_var_remap)
    }
}
