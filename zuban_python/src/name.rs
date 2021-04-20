use std::rc::Rc;
use std::cell::{Cell, RefCell};

use crate::value::{Value, ValueKind};
use crate::cache::{ModuleIndex, StateDB};
use crate::module::{Module, Names};
use parsa::{CodeIndex, NodeIndex};

type Signatures = Vec<()>;

struct TreePosition {
    position: CodeIndex,
    state_db: Rc<RefCell<StateDB>>,
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
    fn get_name(&self) -> &str;

    fn get_module_path(&self) -> Option<&str>;

    // TODO
    //fn get_kind(&self) -> Option<ValueKind>;

    fn get_start_position(&self) -> TreePosition;

    fn get_end_position(&self) -> TreePosition;

    // TODO
    //fn get_definition_start_and_end_position(&self) -> (TreePosition, TreePosition);

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
    state_db: *mut StateDB,
    tree_id: NodeIndex,
}

impl TreeName {
    #[inline]
    fn get_state_db(&mut self) -> &mut StateDB {
        if !self.is_alive.get() {
            panic!("You should not access an old state of the project");
        }
        unsafe {&mut *self.state_db}
    }

    #[inline]
    fn get_module(&self) -> &dyn Module {
        // TODO comment why this is ok.
        #[allow(clippy::cast_ref_to_mut)]
        unsafe {&mut *(self as *const Self as *mut Self)}.get_state_db().get_module(self.module)
    }
}

struct ValueName {
    value: dyn Value,
}


impl Name for TreeName {
    fn get_name(&self) -> &str {
        //self.get_module().get_tree_node(self.tree_id).get_code()
        todo!()
    }

    fn get_module_path(&self) -> Option<&str> {
        self.get_module().get_path()
    }

    fn get_start_position(&self) -> TreePosition {
        //self.get_module().get_tree_node(self.tree_id).get_position()
        todo!();
    }

    fn get_end_position(&self) -> TreePosition {
        todo!();
    }

    fn get_documentation(&self) -> String {
        todo!()
    }

    fn get_description(&self) -> String {
        todo!()
    }

    fn get_qualified_names(&self) -> Option<Vec<String>> {
        todo!()
    }

    /*
    fn is_implementation(&self) {
    }
    */
}
