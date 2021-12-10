use parsa_python_ast::{Argument, ArgumentsIterator, ClassDef};

use super::{Function, TupleClass, Value, ValueKind};
use crate::arguments::{Arguments, ArgumentsType};
use crate::database::{
    ClassInfos, ComplexPoint, Database, GenericPart, GenericsList, Locality, MroClass, Point,
    PointLink, Specific, TypeVarRemap,
};
use crate::debug;
use crate::file::PythonFile;
use crate::generics::{search_type_vars, Generics, TypeVarMatcher};
use crate::getitem::SliceType;
use crate::inference_state::InferenceState;
use crate::inferred::{FunctionOrOverload, Inferred, NodeReference};
use crate::utils::SymbolTable;

#[derive(Debug, Clone, Copy)]
pub enum ClassLike<'db, 'a> {
    ClassRef(&'a Class<'db, 'a>),
    Class(Class<'db, 'a>),
    Tuple(TupleClass<'a>),
}

impl<'db, 'a> ClassLike<'db, 'a> {
    pub fn infer_type_vars(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        value: Inferred<'db>,
        matcher: &mut TypeVarMatcher<'db, '_>,
    ) {
        // Note: we need to handle the MRO _in order_, so we need to extract
        // the elements from the set first, then handle them, even if we put
        // them back in a set afterwards.
        let mut some_class_matches = false;
        // TODO use type_var_remap
        value.run(
            i_s,
            &mut |i_s, v| {
                let check_class = v.class(i_s);
                for class_like in check_class.mro(i_s) {
                    if self.matches_without_generics(&class_like) {
                        some_class_matches = true;
                        let mut value_generics = class_like.generics().iter();
                        let mut generics = self.generics().iter();
                        while let Some(generic) = generics.next(i_s) {
                            let value_generic = value_generics.next(i_s);
                            if let Some(inf) = value_generic {
                                if let Some(point) = generic.maybe_numbered_type_var() {
                                    matcher.add_type_var(i_s, point, &inf)
                                } else if let Some(c) = generic.maybe_class_like(i_s) {
                                    c.infer_type_vars(i_s, inf, matcher);
                                    todo!()
                                }
                            }
                        }
                        //break;
                    }
                }
            },
            || todo!(),
        );
        if !some_class_matches {
            matcher.does_not_match();
        }
    }

    fn matches_without_generics(&self, other: &Self) -> bool {
        match self {
            Self::ClassRef(c1) => match other {
                Self::ClassRef(c2) => c1.reference == c2.reference,
                Self::Class(c2) => c1.reference == c2.reference,
                _ => false,
            },
            Self::Class(c1) => match other {
                Self::ClassRef(c2) => c1.reference == c2.reference,
                Self::Class(c2) => c1.reference == c2.reference,
                _ => false,
            },
            Self::Tuple(_) => matches!(other, Self::Tuple(_)),
        }
    }

    fn generics(&self) -> Generics<'db, '_> {
        match self {
            Self::ClassRef(c) => c.generics,
            Self::Class(c) => c.generics,
            Self::Tuple(c) => c.generics(),
        }
    }

    pub fn as_string(&self, i_s: &mut InferenceState<'db, '_>) -> String {
        match self {
            Self::ClassRef(c) => c.as_str(i_s),
            Self::Class(c) => c.as_str(i_s),
            Self::Tuple(c) => format!("Tuple{}", self.generics().as_str(i_s)),
        }
    }

    fn mro(&self, i_s: &mut InferenceState<'db, '_>) -> MroIterator<'db, '_> {
        match self {
            Self::ClassRef(c) => c.mro(i_s),
            Self::Class(c) => c.mro(i_s),
            Self::Tuple(c) => MroIterator {
                database: i_s.database,
                generics: self.generics(),
                class: Some(*self),
                iterator: [].iter(),
                returned_object: false,
            },
        }
    }

    fn lookup_symbol(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        name: &str,
    ) -> Option<Inferred<'db>> {
        match self {
            Self::ClassRef(c) => c.lookup_symbol(i_s, name),
            Self::Class(c) => c.lookup_symbol(i_s, name),
            Self::Tuple(c) => todo!(),
        }
    }

    pub fn as_generic_part(&self, i_s: &mut InferenceState<'db, '_>) -> GenericPart {
        match self {
            Self::ClassRef(c) => c.as_generic_part(i_s),
            Self::Class(c) => c.as_generic_part(i_s),
            Self::Tuple(c) => todo!(),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Class<'db, 'a> {
    pub reference: NodeReference<'db>,
    pub(super) symbol_table: &'db SymbolTable,
    pub(super) generics: Generics<'db, 'a>,
    type_var_remap: Option<&'db [Option<TypeVarRemap>]>,
}

impl<'db, 'a> Class<'db, 'a> {
    pub fn new(
        reference: NodeReference<'db>,
        symbol_table: &'db SymbolTable,
        generics: Generics<'db, 'a>,
        type_var_remap: Option<&'db [Option<TypeVarRemap>]>,
    ) -> Self {
        Self {
            reference,
            symbol_table,
            generics,
            type_var_remap,
        }
    }

    #[inline]
    pub fn from_position(
        reference: NodeReference<'db>,
        generics: Generics<'db, 'a>,
        type_var_remap: Option<&'db [Option<TypeVarRemap>]>,
    ) -> Option<Self> {
        let complex = reference.complex().unwrap();
        match complex {
            ComplexPoint::Class(c) => Some(Self::new(
                reference,
                &c.symbol_table,
                generics,
                type_var_remap,
            )),
            _ => unreachable!("Probably an issue with indexing: {:?}", &complex),
        }
    }

    pub fn init_func(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
    ) -> (Function<'db>, Option<GenericsList>) {
        let init = self.lookup(i_s, "__init__");
        match init.init_as_function() {
            Some(FunctionOrOverload::Function(func)) => {
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
                let type_vars = self.type_vars(i_s);
                if let Some((func, list)) =
                    overloaded_function.find_matching_function(i_s, args, Some(type_vars))
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
            reference.insert_complex(ComplexPoint::ClassInfos(self.calculate_class_infos(i_s)));
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
                        inf.run(
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
                                        mro.push(base.remap_with_sub_class(&mro[mro_index]));
                                    }
                                } else if let Some(t) = v.as_typing_with_generics(i_s) {
                                    if t.specific == Specific::TypingProtocol {
                                        is_protocol = true;
                                    }
                                }
                            },
                            || todo!(),
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
            is_protocol,
        })
    }

    fn lookup_symbol(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        name: &str,
    ) -> Option<Inferred<'db>> {
        self.symbol_table.lookup_symbol(name).map(|node_index| {
            self.reference
                .file
                .inference(i_s)
                .infer_name_by_index(node_index)
        })
    }

    fn mro(&self, i_s: &mut InferenceState<'db, '_>) -> MroIterator<'db, '_> {
        let class_infos = self.class_infos(i_s);
        MroIterator {
            database: i_s.database,
            generics: self.generics,
            class: Some(ClassLike::ClassRef(self)),
            iterator: class_infos.mro.iter(),
            returned_object: false,
        }
    }

    pub fn as_str(&self, i_s: &mut InferenceState<'db, '_>) -> String {
        let generics_str = self.generics.as_str(i_s);
        let has_type_vars = self.class_infos(i_s).type_vars.len() > 0;
        format!(
            "{}{}",
            self.name(),
            if has_type_vars { &generics_str } else { "" }
        )
    }
}

impl<'db> Value<'db> for Class<'db, '_> {
    fn kind(&self) -> ValueKind {
        ValueKind::Class
    }

    fn name(&self) -> &'db str {
        self.node().name().as_str()
    }

    fn lookup(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> Inferred<'db> {
        for c in self.mro(i_s) {
            if let Some(inf) = c.lookup_symbol(i_s, name) {
                return inf;
            }
        }
        todo!("{:?}.{:?}", self.name(), name)
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
                    Some(generics_list) => Generics::List(generics_list).as_str(i_s),
                    None => "".to_owned(),
                }
            );
            Inferred::new_unsaved_complex(match generics_list {
                None => ComplexPoint::ExecutionInstance(
                    self.reference.as_link(),
                    Box::new(args.as_execution(&func)),
                ),
                Some(generics_list) => {
                    ComplexPoint::Instance(self.reference.as_link(), Some(generics_list))
                }
            })
        } else {
            let point = Point::new_simple_specific(Specific::InstanceWithArguments, Locality::Stmt);
            match args.type_() {
                ArgumentsType::Normal(file, primary_node) => {
                    Inferred::new_and_save(file, primary_node.index(), point)
                }
            }
        }
    }

    fn get_item(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        slice_type: &SliceType<'db>,
    ) -> Inferred<'db> {
        let point = Point::new_simple_specific(Specific::SimpleGeneric, Locality::Stmt);
        Inferred::new_and_save(slice_type.file(), slice_type.primary_index(), point)
    }

    fn as_class(&self) -> Option<&Self> {
        Some(self)
    }

    fn as_class_like(&self) -> Option<ClassLike<'db, '_>> {
        Some(ClassLike::ClassRef(self))
    }

    fn description(&self, i_s: &mut InferenceState<'db, '_>) -> String {
        format!(
            "{} {}",
            format!("{:?}", self.kind()).to_lowercase(),
            self.as_str(i_s),
        )
    }

    fn as_generic_part(&self, i_s: &mut InferenceState<'db, '_>) -> GenericPart {
        let lst = self.generics.as_generics_list(i_s);
        let link = self.reference.as_link();
        lst.map(|lst| GenericPart::GenericClass(link, lst))
            .unwrap_or_else(|| GenericPart::Class(link))
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

struct MroIterator<'db, 'a> {
    database: &'db Database,
    generics: Generics<'db, 'a>,
    class: Option<ClassLike<'db, 'a>>,
    iterator: std::slice::Iter<'db, MroClass>,
    returned_object: bool,
}

impl<'db, 'a> Iterator for MroIterator<'db, 'a> {
    type Item = ClassLike<'db, 'a>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.class.is_some() {
            return Some(std::mem::replace(&mut self.class, None).unwrap());
        }
        if let Some(c) = self.iterator.next() {
            Some(ClassLike::Class(
                Class::from_position(
                    NodeReference::from_link(self.database, c.class),
                    self.generics,
                    Some(&c.type_var_remap),
                )
                .unwrap(),
            ))
        } else if !self.returned_object {
            self.returned_object = true;
            Class::from_position(self.database.python_state.object(), Generics::None, None)
                .map(ClassLike::Class)
        } else {
            None
        }
    }
}

fn create_type_var_remap<'db>(
    i_s: &mut InferenceState<'db, '_>,
    original_class: NodeReference<'db>,
    original_type_vars: &[PointLink],
    generic: Inferred<'db>,
) -> Option<TypeVarRemap> {
    if let Some(point) = generic.maybe_numbered_type_var() {
        Some(TypeVarRemap::TypeVar(point.type_var_index()))
    } else {
        generic.maybe_class(i_s).map(|base_cls| {
            TypeVarRemap::MroClass(create_mro_class(
                i_s,
                original_class,
                original_type_vars,
                &base_cls,
            ))
        })
    }
}

fn create_mro_class<'db>(
    i_s: &mut InferenceState<'db, '_>,
    original_class: NodeReference<'db>,
    original_type_vars: &[PointLink],
    class: &Class<'db, '_>,
) -> MroClass {
    let type_vars = if class.reference == original_class {
        // We need to use the original type vars here, because there can be a recursion in there,
        // like `class str(Sequence[str])`, which means that the class info must not be fetched,
        // because it does not exist yet, i.e. it would lead to a stack overflow.
        original_type_vars
    } else {
        class.type_vars(i_s)
    };
    let mut iterator = class.generics.iter();
    let mut type_var_remap = Vec::with_capacity(type_vars.len());
    for type_var in type_vars {
        if let Some(generic) = iterator.next(i_s) {
            type_var_remap.push(create_type_var_remap(
                i_s,
                original_class,
                original_type_vars,
                generic,
            ));
        } else {
            type_var_remap.push(None);
        }
    }
    MroClass {
        class: class.reference.as_link(),
        type_var_remap: type_var_remap.into_boxed_slice(),
    }
}
