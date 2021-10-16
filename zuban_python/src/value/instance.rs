use parsa_python_ast::{ClassDef, NodeIndex};

use super::{Value, ValueKind};
use crate::arguments::Arguments;
use crate::file::PythonFile;
use crate::generics::Generics;
use crate::getitem::SliceType;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::utils::SymbolTable;

#[derive(Debug)]
pub struct Instance<'db, 'a> {
    file: &'db PythonFile,
    symbol_table: &'db SymbolTable,
    inferred: &'a Inferred<'db>,
    node_index: NodeIndex,
    generics: &'a dyn Generics<'db>,
}

impl<'db, 'a> Instance<'db, 'a> {
    pub fn new(
        file: &'db PythonFile,
        node_index: NodeIndex,
        symbol_table: &'db SymbolTable,
        inferred: &'a Inferred<'db>,
        generics: &'a dyn Generics<'db>,
    ) -> Self {
        Self {
            file,
            node_index,
            symbol_table,
            inferred,
            generics,
        }
    }

    pub fn get_node(&self) -> ClassDef<'db> {
        ClassDef::by_index(&self.file.tree, self.node_index)
    }

    pub fn as_inferred(&self) -> &'a Inferred<'db> {
        self.inferred
    }

    pub fn lookup_type_var(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        name: &str,
    ) -> Option<Inferred<'db>> {
        let mut found_type_vars = vec![];
        if let Some(arguments) = self.get_node().arguments() {
            for n in arguments.search_names() {
                let inferred = self.file.get_inference(i_s).infer_name(n);
                if inferred.is_type_var(i_s) {
                    if n.as_str() == name {
                        let index = found_type_vars.len();
                        return self.generics.get_nth(i_s, index);
                    }
                    if !found_type_vars.contains(&n.as_str()) {
                        found_type_vars.push(n.as_str());
                    }
                }
            }
        }
        None
    }
}

impl<'db, 'a> Value<'db> for Instance<'db, 'a> {
    fn get_kind(&self) -> ValueKind {
        ValueKind::Object
    }

    fn get_name(&self) -> &'db str {
        self.get_node().name().as_str()
    }

    fn lookup(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> Inferred<'db> {
        if let Some(node_index) = self.symbol_table.lookup_symbol(name) {
            self.file
                .get_inference(i_s)
                .infer_name_by_index(node_index)
                .resolve_function_return(i_s)
                .bind(i_s, self)
        } else {
            todo!("{:?}", name)
        }
    }

    fn execute(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
    ) -> Inferred<'db> {
        todo!()
    }

    fn get_item(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        slice_type: &SliceType<'db>,
    ) -> Inferred<'db> {
        self.lookup(i_s, "__getitem__")
            .run_on_value(i_s, &|i_s, v| v.execute(i_s, &slice_type.as_args()))
    }

    fn as_instance(&self) -> Option<&Instance<'db, '_>> {
        Some(self)
    }
}
