use parsa_python_ast::Expression;

use crate::file::PythonFile;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;

pub trait TypeVarFinder<'db, 'a> {
    fn lookup(&mut self, i_s: &mut InferenceState<'db, '_>, name: &str) -> Option<Inferred<'db>>;
}

pub fn resolve_type_vars<'db, 'a>(
    i_s: &mut InferenceState<'db, '_>,
    file: &'db PythonFile,
    expr: Expression<'db>,
    type_var_finder: &mut impl TypeVarFinder<'db, 'a>,
) -> Option<Inferred<'db>> {
    let inferred = file.get_inference(i_s).infer_expression(expr);
    if inferred.is_type_var(i_s) {
        type_var_finder
            .lookup(i_s, expr.get_legacy_node().get_code())
            .or_else(|| todo!())
    } else {
        /*
        if !node.is_leaf() {
            for node in node.iter_children() {
                if node.is_type(Terminal(TerminalType::Name)) {
                    if let Some(resolved_type_var) =
                        resolve_type_vars(i_s, file, node, type_var_finder)
                    {
                        todo!()
                    }
                }
            }
        }
        */
        None
    }
}

pub trait Generics<'db> {
    fn get_nth(&self, n: usize) -> Inferred<'db>;
}
