use parsa::Node;
use parsa::NodeIndex;
use parsa_python::{
    NonterminalType, PyNode,
    PyNodeType::{Nonterminal, Terminal},
    TerminalType,
};

use super::{Value, ValueKind};
use crate::arguments::Arguments;
use crate::database::Database;
use crate::file::{Inferred, PythonFile};

#[derive(Debug)]
pub struct Function<'a> {
    file: &'a PythonFile,
    node_index: NodeIndex,
}

impl<'a> Function<'a> {
    pub fn new(file: &'a PythonFile, node_index: NodeIndex) -> Self {
        Self { file, node_index }
    }

    fn get_node(&self) -> PyNode<'a> {
        self.file.tree.get_node_by_index(self.node_index)
    }
}

impl<'a> Value<'a> for Function<'a> {
    fn get_kind(&self) -> ValueKind {
        ValueKind::Function
    }

    fn get_name(&self) -> &'a str {
        let func_node = self.file.tree.get_node_by_index(self.node_index);
        func_node.get_nth_child(1).get_nth_child(0).get_code()
    }

    fn lookup(&self, database: &'a Database, name: &str) -> Inferred<'a> {
        todo!()
    }

    fn execute(&self, database: &'a Database, args: &Arguments<'a>) -> Inferred<'a> {
        let return_annotation = self.get_node().get_nth_child(3);
        // Is an annotation
        if return_annotation.is_type(Nonterminal(NonterminalType::return_annotation)) {
            if let Some(inferred) =
                resolve_type_vars(database, self.file, return_annotation.get_nth_child(1))
            {
                inferred
            } else {
                todo!()
                /*
                inferred.run_on_value(database, |v| {
                    // TODO locality is wrong!!!!!1
                    let point = if v.get_kind() == ValueKind::Class {
                        Point::new_simple_language_specific(
                            Specific::AnnotationInstance,
                            Locality::Stmt,
                        )
                    } else {
                        Point::new_missing_or_unknown(self.file.get_file_index(), Locality::Stmt);
                        todo!();
                    };
                    Inferred::new_and_save(self.file, return_annotation, point)
                })
                }
                */
            }
        } else {
            todo!()
        }
    }
}

fn resolve_type_vars<'a>(
    database: &'a Database,
    file: &'a PythonFile,
    annotation: PyNode<'a>,
) -> Option<Inferred<'a>> {
    //let type_var = Ty
    let inferred = file.infer_expression(database, annotation);
    if inferred.is_type_var() {
        Some(inferred)
    } else {
        if !annotation.is_leaf() {
            for node in annotation.iter_children() {
                if node.is_type(Terminal(TerminalType::Name)) {
                    if let Some(resolved_type_var) = resolve_type_vars(database, file, node) {
                        todo!()
                    }
                }
            }
        }
        None
    }
}
