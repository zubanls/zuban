use parsa_python_ast::{Argument, ArgumentsIterator, ClassDef, NodeIndex};

use super::{Function, Value, ValueKind};
use crate::arguments::{Arguments, ArgumentsType};
use crate::database::{
    ClassInfos, ClassWithTypeVarIndex, ComplexPoint, Database, Locality, Point, PointLink,
    PointType, Specific, TypeVarRemap,
};
use crate::file::PythonFile;
use crate::file_state::File;
use crate::generics::Generics;
use crate::getitem::SliceType;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::utils::SymbolTable;

#[derive(Debug)]
pub struct Class<'db> {
    file: &'db PythonFile,
    symbol_table: &'db SymbolTable,
    node_index: NodeIndex,
    generics: Generics<'db>,
    type_var_remap: Option<&'db [Option<TypeVarRemap>]>,
}

impl<'db> Class<'db> {
    pub fn new(
        file: &'db PythonFile,
        node_index: NodeIndex,
        symbol_table: &'db SymbolTable,
        generics: Generics<'db>,
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

    pub fn from_position(
        file: &'db PythonFile,
        node_index: NodeIndex,
        generics: Generics<'db>,
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

    pub fn infer_type_vars(&self, i_s: &mut InferenceState<'db, '_>, value: Inferred<'db>) {
        // Note: we need to handle the MRO _in order_, so we need to extract
        // the elements from the set first, then handle them, even if we put
        // them back in a set afterwards.
        // TODO use mro
        if let Some(value) = value.expect_class() {
            todo!();
            ();
            for cls in value.mro(i_s.database) {
                if let Some(base_class) = value.as_class() {
                    if base_class.node_index == self.node_index
                        && base_class.file.get_file_index() == self.file.get_file_index()
                    {
                        let mut value_generics = base_class.generics.iter();
                        let mut generics = self.generics.iter();
                        while let Some(generic) = generics.next(i_s) {
                            dbg!(&generic);
                            let v = value_generics.next(i_s).unwrap_or_else(|| todo!());
                            if generic.is_type_var(i_s) {
                                todo!("report pls: {:?} is {:?}", generic, v)
                            } else if let Some(cls) = generic.expect_class() {
                                cls.infer_type_vars(i_s, v)
                            }
                        }
                        //break;
                    }
                }
                todo!()
            }
        }
        todo!();
    }

    pub fn lookup_type_var(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        name: &str,
    ) -> Option<Inferred<'db>> {
        // TODO whyyy???
        let mut found_type_vars = vec![];
        if let Some(arguments) = self.get_node().arguments() {
            for n in arguments.search_names() {
                let inferred = self.file.get_inference(i_s).infer_name(n);
                if inferred.is_type_var(i_s) {
                    if n.as_str() == name {
                        let index = found_type_vars.len();
                        return self.generics.get_nth(i_s, index, name);
                    }
                    if !found_type_vars.contains(&n.as_str()) {
                        found_type_vars.push(n.as_str());
                    }
                }
            }
        }
        None
    }

    fn get_class_infos(&self) -> &'db ClassInfos {
        let point = self.file.points.get(self.node_index + 1);
        let complex_index = point.get_complex_index();
        match self.file.complex_points.get(complex_index) {
            ComplexPoint::ClassInfos(class_infos) => class_infos,
            _ => unreachable!(),
        }
    }

    fn mro(&self, database: &'db Database) -> MroIterator<'db, '_> {
        let class_infos = self.get_class_infos();
        MroIterator {
            database,
            generics: &self.generics,
            iterator: class_infos.mro.iter(),
        }
    }
}

impl<'db> Value<'db> for Class<'db> {
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
                args.as_execution(&self.get_init_func(i_s, args)),
            ))
        } else {
            let point = Point::new_simple_language_specific(
                Specific::InstanceWithArguments,
                Locality::Stmt,
            );
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
        let point = Point::new_simple_language_specific(Specific::SimpleGeneric, Locality::Stmt);
        match slice_type {
            SliceType::Simple(simple) => {
                Inferred::new_and_save(simple.file, simple.primary_index, point)
            }
            _ => todo!(),
        }
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
    generics: &'a Generics<'db>,
    iterator: std::slice::Iter<'db, ClassWithTypeVarIndex>,
}

impl<'db> Iterator for MroIterator<'db, '_> {
    type Item = Class<'db>;

    fn next(&mut self) -> Option<Self::Item> {
        self.iterator.next().map(|c| {
            let file = self.database.get_loaded_python_file(c.class.file);
            Class::from_position(
                file,
                c.class.node_index,
                Generics::None,
                Some(&c.type_var_remap),
            )
            .unwrap()
        })
    }
}
