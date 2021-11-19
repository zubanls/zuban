use parsa_python_ast::NodeIndex;
use std::ptr::null;

use crate::database::{Database, Locality, Point, PointLink, PointType, Specific};
use crate::file::PythonFile;
use crate::file_state::File;
use crate::inferred::Inferred;

pub struct PythonState {
    builtins: *const PythonFile,
    typing: *const PythonFile,
    object_node_index: NodeIndex,
}

impl PythonState {
    pub fn reserve() -> Self {
        Self {
            builtins: null(),
            typing: null(),
            object_node_index: 0,
        }
    }

    pub fn initialize(
        database: &mut Database,
        builtins: *const PythonFile,
        typing: *const PythonFile,
    ) {
        database.python_state.builtins = builtins;
        database.python_state.typing = typing;
        let builtins = database.python_state.builtins();
        builtins.calculate_global_definitions_and_references();
        database.python_state.object_node_index =
            builtins.symbol_table.lookup_symbol("object").unwrap();

        typing_changes(database.python_state.typing());
    }

    #[inline]
    pub fn builtins(&self) -> &PythonFile {
        debug_assert!(!self.builtins.is_null());
        unsafe { &*self.builtins }
    }

    #[inline]
    pub fn typing(&self) -> &PythonFile {
        debug_assert!(!self.typing.is_null());
        unsafe { &*self.typing }
    }

    pub fn builtins_point_link(&self, name: &str) -> PointLink {
        let builtins = self.builtins();
        let node_index = builtins.symbol_table.lookup_symbol(name).unwrap();
        let point = builtins.points.get(node_index);
        debug_assert_eq!(point.type_(), PointType::Redirect);
        PointLink::new(builtins.file_index(), point.node_index())
    }
}

fn typing_changes(typing: &PythonFile) {
    typing.calculate_global_definitions_and_references();
    set_typing_inference(typing, "Protocol", Specific::TypingProtocol);
    set_typing_inference(typing, "Generic", Specific::TypingGeneric);
}

fn set_typing_inference(typing: &PythonFile, name: &str, specific: Specific) {
    let node_index = typing.symbol_table.lookup_symbol(name).unwrap();
    debug_assert!(!typing.points.get(node_index).calculated());
    typing.points.set(
        node_index,
        Point::new_simple_specific(specific, Locality::Stmt),
    );
}
