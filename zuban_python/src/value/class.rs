use once_cell::unsync::OnceCell;
use parsa_python_ast::{Argument, ArgumentsIterator, ClassDef, NodeIndex};

use super::{Function, Value, ValueKind};
use crate::arguments::{Arguments, ArgumentsType};
use crate::database::{
    ClassInfos, ClassWithTypeVarIndex, ComplexPoint, Database, GenericPart, Locality, Point,
    PointLink, PointType, Specific, TypeVarRemap,
};
use crate::file::PythonFile;
use crate::file_state::File;
use crate::generics::{Generics, TypeVarMatcher};
use crate::getitem::SliceType;
use crate::inference_state::InferenceState;
use crate::inferred::{Inferred, NodeReference};
use crate::utils::SymbolTable;

#[derive(Debug, Clone)]
pub struct Class<'db, 'a> {
    pub(super) file: &'db PythonFile,
    pub(super) symbol_table: &'db SymbolTable,
    pub node_index: NodeIndex,
    pub generics: Generics<'db, 'a>,
    type_var_remap: Option<&'db [Option<TypeVarRemap>]>,
}

impl<'db, 'a> Class<'db, 'a> {
    pub fn new(
        file: &'db PythonFile,
        node_index: NodeIndex,
        symbol_table: &'db SymbolTable,
        generics: Generics<'db, 'a>,
        type_var_remap: Option<&'db [Option<TypeVarRemap>]>,
    ) -> Self {
        Self {
            file,
            node_index,
            symbol_table,
            generics,
            type_var_remap,
        }
    }

    #[inline]
    pub fn from_position(
        file: &'db PythonFile,
        node_index: NodeIndex,
        generics: Generics<'db, 'a>,
        type_var_remap: Option<&'db [Option<TypeVarRemap>]>,
    ) -> Option<Self> {
        let v = file.points.get(node_index);
        debug_assert_eq!(v.get_type(), PointType::Complex, "{:?}", v);
        let complex = file.complex_points.get(v.get_complex_index() as usize);
        match complex {
            ComplexPoint::Class(c) => Some(Self::new(
                file,
                node_index,
                &c.symbol_table,
                generics,
                type_var_remap,
            )),
            _ => unreachable!("Probably an issue with indexing: {:?}", &complex),
        }
    }

    pub fn get_init_func(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
    ) -> Function<'db> {
        let init = self.lookup(i_s, "__init__");
        init.find_function_alternative()
    }

    pub fn get_node(&self) -> ClassDef<'db> {
        ClassDef::by_index(&self.file.tree, self.node_index)
    }

    pub fn get_type_vars(&self, i_s: &mut InferenceState<'db, '_>) -> &'db [PointLink] {
        &self.get_class_infos(i_s).type_vars
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
        dbg!(self.get_name(), self.type_var_remap);
        value.run(i_s, &mut |i_s, v| {
            let check_class = v.class(i_s);
            for class in check_class.mro(i_s) {
                if class.node_index == self.node_index
                    && class.file.get_file_index() == self.file.get_file_index()
                {
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

    pub fn lookup_type_var(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        name: &str,
    ) -> Option<Inferred<'db>> {
        // TODO whyyy???
        let mut found_type_vars = vec![];
        if let Some(arguments) = self.get_node().arguments() {
            // TODO search names will probably not be used anymore in the future
            for n in arguments.search_names() {
                let inferred = self.file.get_inference(i_s).infer_name(n);
                if inferred.maybe_type_var(i_s).is_some() {
                    if n.as_str() == name {
                        let index = found_type_vars.len();
                        todo!();
                        //return self.generics.nth(i_s, index);
                    }
                    if !found_type_vars.contains(&n.as_str()) {
                        found_type_vars.push(n.as_str());
                    }
                }
            }
        }
        None
    }

    pub fn get_class_infos(&self, i_s: &mut InferenceState<'db, '_>) -> &'db ClassInfos {
        let node_index = self.node_index + 1;
        let point = self.file.points.get(node_index);
        if point.is_calculated() {
            let complex_index = point.get_complex_index();
            match self.file.complex_points.get(complex_index) {
                ComplexPoint::ClassInfos(class_infos) => class_infos,
                _ => unreachable!(),
            }
        } else {
            self.file.complex_points.insert(
                &self.file.points,
                node_index,
                ComplexPoint::ClassInfos(self.calculate_class_infos(i_s)),
            );
            debug_assert!(self.file.points.get(node_index).is_calculated());
            self.get_class_infos(i_s)
        }
    }

    fn calculate_class_infos(&self, i_s: &mut InferenceState<'db, '_>) -> Box<ClassInfos> {
        let mut mro = vec![];
        let mut type_vars = vec![];
        let mut maybe_add_type_var = |definition: &NodeReference| {
            let link = definition.as_link();
            if !type_vars.contains(&link) {
                type_vars.push(link);
            }
        };
        let mut i_s = i_s.with_annotation_instance();
        let mut is_protocol = false;
        if let Some(arguments) = self.get_node().arguments() {
            for argument in arguments.iter() {
                match argument {
                    Argument::Positional(n) => {
                        // TODO this probably causes certain problems with infer_annotation_expression
                        let inf = self.file.get_inference(&mut i_s).infer_named_expression(n);
                        dbg!(inf.description(&mut i_s));
                        inf.run(&mut i_s, &mut |i_s, v| {
                            if let Some(class) = v.as_class() {
                                let mut type_var_remap = vec![];
                                let mut iterator = class.generics.iter();
                                while let Some(g) = iterator.next(i_s) {
                                    if let Some(definition) = g.maybe_type_var(i_s) {
                                        maybe_add_type_var(&definition)
                                    } else {
                                        dbg!(g.debug_info(i_s));
                                        todo!()
                                    }
                                }
                                // TODO remapping type var ids is not correct
                                mro.push(ClassWithTypeVarIndex {
                                    class: PointLink {
                                        file: class.file.get_file_index(),
                                        node_index: class.node_index,
                                    },
                                    type_var_remap: type_var_remap.into_boxed_slice(),
                                });
                                mro.extend(class.get_class_infos(i_s).mro.iter().cloned());
                            } else if let Some(t) = v.as_typing_with_generics(i_s) {
                                if t.specific == Specific::TypingProtocol {
                                    is_protocol = true;
                                }
                                for arg in t.get_generics().as_args().iter_arguments() {
                                    if let Some(definition) = arg.infer(i_s).maybe_type_var(i_s) {
                                        maybe_add_type_var(&definition)
                                    }
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
        let class_infos = self.get_class_infos(i_s);
        MroIterator {
            database: i_s.database,
            generics: &self.generics,
            class: Some(self),
            iterator: class_infos.mro.iter(),
        }
    }

    pub fn to_generic_part(&self, i_s: &mut InferenceState<'db, '_>) -> GenericPart {
        let lst = self.generics.as_generics_list(i_s);
        let link = self.to_point_link();
        lst.map(|lst| GenericPart::GenericClass(link, lst))
            .unwrap_or_else(|| GenericPart::Class(link))
    }

    pub fn to_point_link(&self) -> PointLink {
        PointLink::new(self.file.get_file_index(), self.node_index)
    }

    pub fn as_str(&self, i_s: &mut InferenceState<'db, '_>) -> String {
        let generics_str = self.generics.as_str(i_s);
        let has_type_vars = self.get_class_infos(i_s).type_vars.len() > 0;
        format!(
            "{}{}",
            self.get_name(),
            if has_type_vars { &generics_str } else { "" }
        )
    }
}

impl<'db> Value<'db> for Class<'db, '_> {
    fn get_kind(&self) -> ValueKind {
        ValueKind::Class
    }

    fn get_name(&self) -> &'db str {
        self.get_node().name().as_str()
    }

    fn lookup(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> Inferred<'db> {
        if let Some(node_index) = self.symbol_table.lookup_symbol(name) {
            self.file.get_inference(i_s).infer_name_by_index(node_index)
        } else {
            // todo!("{:?}.{:?}", self.get_name(), name)
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
        if args.get_outer_execution().is_some() {
            Inferred::new_unsaved_complex(ComplexPoint::Instance(
                PointLink::new(self.file.get_file_index(), self.node_index),
                OnceCell::new(),
                Box::new(args.as_execution(&self.get_init_func(i_s, args))),
            ))
        } else {
            let point = Point::new_simple_specific(Specific::InstanceWithArguments, Locality::Stmt);
            match args.get_type() {
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
            format!("{:?}", self.get_kind()).to_lowercase(),
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
                    return Some(self.file.get_inference(i_s).infer_named_expression(p))
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
    iterator: std::slice::Iter<'db, ClassWithTypeVarIndex>,
}

impl<'db, 'a> Iterator for MroIterator<'db, 'a> {
    type Item = Class<'db, 'a>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.class.is_some() {
            return Some(std::mem::replace(&mut self.class, None).unwrap().clone());
        }
        self.iterator.next().map(|c| {
            let file = self.database.get_loaded_python_file(c.class.file);
            Class::from_position(
                file,
                c.class.node_index,
                self.generics.clone(),
                Some(&c.type_var_remap),
            )
            .unwrap()
        })
    }
}
