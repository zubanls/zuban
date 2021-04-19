use std::rc::Rc;
use std::cell::{Cell, RefCell};
use std::path::{PathBuf};

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
    fn get_name(&self) -> String;

    fn get_module_path(&self) -> Option<PathBuf>;

    fn get_kind(&self) -> Option<ValueKind>;

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
        let module = self.module;
        let x = self as *const Self;
        let y = x as *mut Self;
        let z = unsafe {&mut *y};
        z.get_state_db().get_module(module)
        //unsafe {&*(self as *const Self as *mut Self)}.get_state_db().get_module(self.module)
    }
}

struct ValueName {
    value: dyn Value,
}


/*
impl Name for TreeName {
    fn get_name(&self) -> String {
        self.get_module().get_name()
    }

    fn is_implementation
}
*/
