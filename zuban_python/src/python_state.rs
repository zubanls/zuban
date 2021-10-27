use std::ptr::null;
use parsa_python_ast::NodeIndex;

use crate::database::{Database, PointType, Specific, Point, Locality};
use crate::file::PythonFile;
use crate::inferred::Inferred;

pub struct PythonState {
    builtins: *const PythonFile,
    typing: *const PythonFile,
    object_init_method_node_index: NodeIndex,
}

impl PythonState {
    pub fn reserve() -> Self {
        Self {
            builtins: null(),
            typing: null(),
            object_init_method_node_index: 0,
        }
    }

    pub fn initialize(database: &mut Database, builtins: *const PythonFile, typing: *const PythonFile) {
        database.python_state.builtins = builtins;
        database.python_state.typing = typing;
        use crate::inference_state::InferenceState;
        use crate::value::{Module, Value};
        let mut i_s = InferenceState::new(database);
        let builtins = database.python_state.get_builtins();
        let obj = Module::new(builtins).lookup(&mut i_s, "object");
        let init = obj.run_on_value(&mut i_s, &mut |i_s, v| v.lookup(i_s, "__init__"));
        let func = init.find_function_alternative();
        let link = func.as_point_link();
        assert_eq!(
            builtins.points.get(link.node_index).get_type(),
            PointType::LanguageSpecific
        );
        assert_eq!(
            builtins.points.get(link.node_index).get_language_specific(),
            Specific::Function
        );
        database.python_state.object_init_method_node_index = link.node_index;

        typing_changes(database.python_state.get_typing());
    }

    #[inline]
    pub fn get_builtins(&self) -> &PythonFile {
        debug_assert!(!self.builtins.is_null());
        unsafe { &*self.builtins }
    }

    #[inline]
    pub fn get_typing(&self) -> &PythonFile {
        debug_assert!(!self.typing.is_null());
        unsafe { &*self.typing }
    }

    pub fn object_init_as_inferred(&self) -> Inferred {
        let builtins = self.get_builtins();
        Inferred::new_saved(
            builtins,
            self.object_init_method_node_index,
            builtins.points.get(self.object_init_method_node_index),
        )
    }
}

fn typing_changes(typing: &PythonFile) {
    typing.calculate_global_definitions_and_references();
    set_typing_inference(typing, "Protocol", Specific::TypingProtocol);
    set_typing_inference(typing, "Generic", Specific::TypingGeneric);
}

fn set_typing_inference(typing: &PythonFile, name: &str, specific: Specific) {
    let node_index = typing.symbol_table.lookup_symbol(name).unwrap();
    debug_assert!(!typing.points.get(node_index).is_calculated());
    typing.points.set(node_index, Point::new_simple_language_specific(specific, Locality::Stmt));
}
