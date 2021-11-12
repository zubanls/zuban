use once_cell::unsync::OnceCell;
use parsa_python_ast::{Argument, ArgumentsIterator, ClassDef};

use super::{Function, Value, ValueKind};
use crate::arguments::{Arguments, ArgumentsType};
use crate::database::{
    ClassInfos, ComplexPoint, Database, GenericPart, Locality, MroClass, Point, PointLink,
    Specific, TypeVarIndex, TypeVarRemap,
};
use crate::debug;
use crate::file::PythonFile;
use crate::generics::{search_type_vars, Generics, TypeVarMatcher};
use crate::getitem::SliceType;
use crate::inference_state::InferenceState;
use crate::inferred::{Inferred, NodeReference};
use crate::utils::SymbolTable;

#[derive(Debug, Clone)]
pub struct Class<'db, 'a> {
    pub reference: NodeReference<'db>,
    pub(super) symbol_table: &'db SymbolTable,
    pub generics: Generics<'db, 'a>,
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
    ) -> Function<'db> {
        let init = self.lookup(i_s, "__init__");
        init.find_function_alternative()
    }

    pub fn node(&self) -> ClassDef<'db> {
        ClassDef::by_index(&self.reference.file.tree, self.reference.node_index)
    }

    pub fn type_vars(&self, i_s: &mut InferenceState<'db, '_>) -> &'db [PointLink] {
        &self.class_infos(i_s).type_vars
    }

    pub fn infer_type_vars(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        value: Inferred<'db>,
        matcher: &mut TypeVarMatcher<'db, '_>,
    ) {
        // Note: we need to handle the MRO _in order_, so we need to extract
        // the elements from the set first, then handle them, even if we put
        // them back in a set afterwards.
        // TODO use mro
        dbg!(self.name(), self.type_var_remap);
        value.run(i_s, &mut |i_s, v| {
            let check_class = v.class(i_s);
            for class in check_class.mro(i_s) {
                if class.reference == self.reference {
                    let mut value_generics = class.generics.iter();
                    let mut generics = self.generics.iter();
                    while let Some(generic) = generics.next(i_s) {
                        let value_generic = value_generics.next(i_s);
                        if let Some(inf) = value_generic {
                            if let Some(point) = generic.maybe_numbered_type_var() {
                                matcher.add_type_var(i_s, point, &inf)
                            } else if let Some(cls) = generic.expect_class(i_s) {
                                cls.infer_type_vars(i_s, inf, matcher);
                                todo!()
                            }
                        }
                    }
                    //break;
                }
            }
        });
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
                        inf.run(&mut i_s, &mut |i_s, v| {
                            if let Some(class) = v.as_class() {
                                mro.push(create_mro_class(i_s, class));
                                // TODO remapping type var ids for mro are not recalculated (which
                                // they should)
                                mro.extend(class.class_infos(i_s).mro.iter().cloned());
                            } else if let Some(t) = v.as_typing_with_generics(i_s) {
                                if t.specific == Specific::TypingProtocol {
                                    is_protocol = true;
                                }
                            }
                        })
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

    fn mro(&self, i_s: &mut InferenceState<'db, '_>) -> MroIterator<'db, '_> {
        let class_infos = self.class_infos(i_s);
        MroIterator {
            database: i_s.database,
            generics: &self.generics,
            class: Some(self),
            iterator: class_infos.mro.iter(),
        }
    }

    pub fn to_generic_part(&self, i_s: &mut InferenceState<'db, '_>) -> GenericPart {
        let lst = self.generics.as_generics_list(i_s);
        let link = self.reference.as_link();
        lst.map(|lst| GenericPart::GenericClass(link, lst))
            .unwrap_or_else(|| GenericPart::Class(link))
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
        if let Some(node_index) = self.symbol_table.lookup_symbol(name) {
            self.reference
                .file
                .inference(i_s)
                .infer_name_by_index(node_index)
        } else {
            // todo!("{:?}.{:?}", self.name(), name)
            // TODO inheritance
            i_s.database.python_state.object_init_as_inferred()
        }
    }

    fn execute(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
    ) -> Inferred<'db> {
        // TODO locality!!!
        if args.outer_execution().is_some() {
            Inferred::new_unsaved_complex(ComplexPoint::Instance(
                self.reference.as_link(),
                OnceCell::new(),
                Box::new(args.as_execution(&self.init_func(i_s, args))),
            ))
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
        match slice_type {
            SliceType::Simple(simple) => {
                Inferred::new_and_save(simple.file, simple.primary_index, point)
            }
            _ => todo!(),
        }
    }

    fn as_class(&self) -> Option<&Self> {
        Some(self)
    }

    fn description(&self, i_s: &mut InferenceState<'db, '_>) -> String {
        format!(
            "{} {}",
            format!("{:?}", self.kind()).to_lowercase(),
            self.as_str(i_s),
        )
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
    generics: &'a Generics<'db, 'a>,
    class: Option<&'a Class<'db, 'a>>,
    iterator: std::slice::Iter<'db, MroClass>,
}

impl<'db, 'a> Iterator for MroIterator<'db, 'a> {
    type Item = Class<'db, 'a>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.class.is_some() {
            return Some(std::mem::replace(&mut self.class, None).unwrap().clone());
        }
        self.iterator.next().map(|c| {
            Class::from_position(
                NodeReference::from_link(self.database, c.class),
                self.generics.clone(),
                Some(&c.type_var_remap),
            )
            .unwrap()
        })
    }
}

fn create_type_var_remap<'db>(
    i_s: &mut InferenceState<'db, '_>,
    generic: Inferred<'db>,
) -> Option<TypeVarRemap> {
    if let Some(point) = generic.maybe_numbered_type_var() {
        Some(TypeVarRemap::TypeVar(point.type_var_index()))
    } else {
        generic
            .expect_class(i_s)
            .map(|base_cls| TypeVarRemap::MroClass(create_mro_class(i_s, &base_cls)))
    }
}

fn create_mro_class<'db>(i_s: &mut InferenceState<'db, '_>, class: &Class<'db, '_>) -> MroClass {
    let type_vars = class.type_vars(i_s);
    let mut iterator = class.generics.iter();
    let mut type_var_remap = Vec::with_capacity(type_vars.len());
    for type_var in type_vars {
        if let Some(generic) = iterator.next(i_s) {
            type_var_remap.push(create_type_var_remap(i_s, generic));
        } else {
            type_var_remap.push(None);
        }
    }
    MroClass {
        class: class.reference.as_link(),
        type_var_remap: type_var_remap.into_boxed_slice(),
    }
}

struct TypeVarFinder(Vec<PointLink>);

impl TypeVarFinder {
    fn add(&mut self, definition: &NodeReference<'_>) -> TypeVarIndex {
        let link = definition.as_link();
        if let Some(index) = self.0.iter().position(|type_var| type_var == &link) {
            TypeVarIndex::new(index)
        } else {
            self.0.push(link);
            TypeVarIndex::new(self.0.len())
        }
    }
}
