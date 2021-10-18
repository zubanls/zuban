use parsa_python_ast::{ClassDef, NodeIndex};

use super::{Function, Value, ValueKind};
use crate::arguments::{Arguments, ArgumentsType};
use crate::database::{ComplexPoint, Locality, Point, PointLink, Specific};
use crate::file::PythonFile;
use crate::file_state::File;
use crate::getitem::SliceType;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::utils::SymbolTable;

#[derive(Debug)]
pub struct Class<'db> {
    file: &'db PythonFile,
    symbol_table: &'db SymbolTable,
    node_index: NodeIndex,
}

impl<'db> Class<'db> {
    pub fn new(
        file: &'db PythonFile,
        node_index: NodeIndex,
        symbol_table: &'db SymbolTable,
    ) -> Self {
        Self {
            file,
            node_index,
            symbol_table,
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
        let value_class: Self = todo!();
        ();
        for base_class in value_class.mro() {
            if base_class.node_index == self.node_index
                && base_class.file.get_file_index() == self.file.get_file_index()
            {
                let mut value_generics = base_class.generics.iter();
                for generic in self.generics.iter() {
                    let v = value_generics.next().unwrap_or_else(todo!());
                    if generic.is_type_var() {
                        todo!("report pls: {} is {}", generic, v)
                    } else if let Some(cls) = generic.expect_class() {
                        cls.infer_type_vars(i_s, v)
                    }
                }
                break;
            }
        }
        todo!();
    }

    fn mro(&self) -> impl Iterator<Item = &Class> {
        std::iter::empty()
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
