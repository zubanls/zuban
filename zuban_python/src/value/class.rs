use parsa_python_ast::{Argument, ArgumentsIterator, ClassDef, NodeIndex};

use super::{Function, Value, ValueKind};
use crate::arguments::{Arguments, ArgumentsType};
use crate::database::{ComplexPoint, Locality, Point, PointLink, Specific, TypeVarRemap};
use crate::file::PythonFile;
use crate::file_state::File;
use crate::generics::{CalculableGenerics, Generics};
use crate::getitem::SliceType;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::utils::SymbolTable;

#[derive(Debug)]
pub struct Class<'db, 'a> {
    file: &'db PythonFile,
    symbol_table: &'db SymbolTable,
    node_index: NodeIndex,
    generics: &'a dyn Generics<'db>,
    type_var_remap: Option<&'db [Option<TypeVarRemap>]>,
}

impl<'db, 'a> Class<'db, 'a> {
    pub fn new(
        file: &'db PythonFile,
        node_index: NodeIndex,
        symbol_table: &'db SymbolTable,
        generics: &'a dyn Generics<'db>,
    ) -> Self {
        Self {
            file,
            node_index,
            symbol_table,
            generics,
            type_var_remap: None,
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
            let mut bases = value.bases();
            while let Some(inf) = bases.next(i_s) {
                /*
                TODO Test why this is not working. Somehow lifetimes are screwed.
                inf.run_on_value(i_s, &|i_s: &mut InferenceState<'db, '_>, value| {
                    self.generics.get_nth(i_s, 0, "");
                    self.file.get_inference(i_s).infer_name_by_index(self.node_index)
                });
                */
                inf.run_on_value(i_s, &|i_s: &mut InferenceState<'db, '_>, value| {
                    // TODO FUUUUUUUUUUUUUUUUUUUUUUUU LIFETIMES IN CLOSURES
                    // This lifetime is valid, but the compiler is wrong...
                    let generics = unsafe { &*(self.generics as *const dyn Generics) };
                    dbg!(value.get_name());
                    if let Some(base_class) = value.as_class() {
                        if base_class.node_index == self.node_index
                            && base_class.file.get_file_index() == self.file.get_file_index()
                        {
                            let mut value_generics = base_class.generics.iter(i_s);
                            let generics = unsafe { &*(self.generics as *const dyn Generics) };
                            for generic in generics.iter(i_s) {
                                dbg!(&generic);
                                let v = value_generics.next().unwrap_or_else(|| todo!());
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
                });
            }
        }
        todo!();
    }

    fn bases(&self) -> BasesIterator<'db> {
        BasesIterator {
            file: self.file,
            args: self.get_node().arguments().map(|a| a.iter()),
        }
    }

    fn mro(&self) -> impl Iterator<Item = Class<'db, '_>> {
        std::iter::empty()
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

//struct MroIterator<'db, 'a> {
//}
