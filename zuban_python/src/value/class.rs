use parsa_python_ast::{Argument, ClassDef, NodeIndex};

use super::{Function, Value, ValueKind};
use crate::arguments::{Arguments, ArgumentsType};
use crate::database::{ComplexPoint, Locality, Point, PointLink, Specific};
use crate::file::PythonFile;
use crate::file_state::File;
use crate::generics::TypeVarFinder;
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

struct ClassTypeVarFinder<'db, 'a> {
    file: &'db PythonFile,
    class: &'a Class<'db>,
    args: &'a dyn Arguments<'db>,
    calculated_type_vars: Option<Vec<(&'db str, Inferred<'db>)>>,
}

impl<'db, 'a> TypeVarFinder<'db, 'a> for ClassTypeVarFinder<'db, 'a> {
    fn lookup(&mut self, i_s: &mut InferenceState<'db, '_>, name: &str) -> Option<Inferred<'db>> {
        if let Some(type_vars) = &self.calculated_type_vars {
            for (type_var, result) in type_vars {
                if *type_var == name {
                    return Some(result.clone());
                }
            }
            None
        } else {
            self.calculate_type_vars(i_s);
            self.lookup(i_s, name)
        }
    }
}

impl<'db, 'a> ClassTypeVarFinder<'db, 'a> {
    fn new(file: &'db PythonFile, class: &'a Class<'db>, args: &'a dyn Arguments<'db>) -> Self {
        Self {
            file,
            class,
            args,
            calculated_type_vars: None,
        }
    }

    fn calculate_type_vars(&mut self, i_s: &mut InferenceState<'db, '_>) {
        let mut calculated_type_vars = vec![];
        if let Some(arguments) = self.class.get_node().arguments() {
            for arg in arguments.iter() {
                match arg {
                    Argument::Positional(a) => {
                        todo!()
                    }
                    _ => {
                        todo!()
                    }
                }
                /*
                    if !calculated_type_vars
                        .iter()
                        .any(|(n, _)| *n == name.get_code())
                    {
                        let inferred = self
                            .file
                            .get_inference(i_s)
                            .infer_expression(annotation.expression());
                        if inferred.is_type_var(i_s) {
                            calculated_type_vars.push((name.get_code(), p.infer(i_s)));
                        } else {
                            // TODO stuff like List[T]
                        }
                    }
                */
            }
        }
        self.calculated_type_vars = Some(calculated_type_vars);
    }
}
