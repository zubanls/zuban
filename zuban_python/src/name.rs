use std::rc::Rc;
use std::cell::{Cell, RefCell};
use std::path::{PathBuf};

use crate::value::Value;
use crate::cache::{ModuleIndex, StateDB};
use crate::module::Names;
use parsa::{CodeIndex, NodeIndex};

type Signatures = Vec<u8>;

struct TreePosition {
    position: CodeIndex,
    state_db: Rc<RefCell<StateDB>>,
}

enum ValueKind {
    // Taken from LSP, unused kinds are commented
	//File = 1,
	Module = 2,
	Namespace = 3,
	//Package = 4,
	Class = 5,
	Method = 6,
	Property = 7,
	Field = 8,
	//Constructor = 9,
	//Enum = 10,
	//Interface = 11,
	Function = 12,
	//Variable = 13,
	Constant = 14,
	String = 15,
	Number = 16,
	Boolean = 17,
	Array = 18,
	Dictionary = 19,  // Called "Object" in LSP
	//Key = 20,
	Null = 21,
	//EnumMember = 22,
	//Struct = 23,
	//Event = 24,
	//Operator = 25,
	TypeParameter = 26,
}

impl TreePosition {
    fn get_byte_position(&self) -> usize {
        unimplemented!();
    }

    fn get_line_and_column(&self) -> (usize, usize) {
        unimplemented!();
    }
}

trait Name {
    fn get_name(&self) -> String;

    fn get_module_path(&self) -> Option<PathBuf>;

    fn get_kind(&self) -> ValueKind;

    fn get_position(&self) -> TreePosition;

    fn get_definition_start_and_end_position(&self) -> (TreePosition, TreePosition);

    fn get_documentation(&self) -> String;

    fn get_description(&self) -> String;

    fn get_qualified_names(&self) -> Option<Vec<String>>;

    fn is_implementation(&self) -> bool {
        true
    }

    fn get_type_hint(&self) -> Option<&str> {
        None
    }

    fn get_signatures(&self) -> Signatures {
        vec!()
    }

    fn infer(&self) -> Names {
        vec!()
    }

    fn goto(&self) -> Names {
        vec!()
    }

    fn is_definition(&self) -> bool {
        false
    }
}

struct TreeName {
    module: ModuleIndex,
    is_alive: Rc<Cell<bool>>,
    state_db: Rc<RefCell<StateDB>>,
    tree_id: NodeIndex,
}

struct ValueName {
    value: dyn Value,
}


/*
impl Name for TreeName {
    fn get_name(&self) -> String {
        self.
    }

    fn is_implementation
}
*/
