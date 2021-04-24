use crate::value::{Value, ValueKind};
use crate::cache::{ModuleIndex, StateDB};
use crate::module::{Module, Names};
use parsa::{CodeIndex, Node};

type Signatures = Vec<()>;

pub struct TreePosition {
    position: CodeIndex,
}

impl TreePosition {
    fn get_byte_position(&self) -> CodeIndex {
        self.position
    }

    fn get_line_and_column(&self) -> (CodeIndex, CodeIndex) {
        unimplemented!();
    }
}

pub trait Name<'a> {
    fn get_name(&self) -> &'a str;

    fn get_module_path(&self) -> Option<&str>;


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

    fn get_type_hint(&self) -> Option<String> {
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

pub trait ValueName {
    fn get_kind(&self) -> Option<ValueKind>;
}

pub struct TreeName<N> {
    state_db: *mut StateDB,
    module: ModuleIndex,
    tree_node: N,
}

impl<'a, N: Node<'a>> TreeName<N> {
    pub fn new(state_db: *mut StateDB, module: ModuleIndex, tree_node: N) -> Self {
        Self {state_db, tree_node, module}
    }
    #[inline]
    fn get_state_db(&mut self) -> &mut StateDB {
        unsafe {&mut *self.state_db}
    }

    #[inline]
    fn get_module(&self) -> &dyn Module {
        // TODO comment why this is ok.
        #[allow(clippy::cast_ref_to_mut)]
        unsafe {&mut *(self as *const Self as *mut Self)}.get_state_db().get_module(self.module)
    }
}

/*
struct ValueName {
    value: dyn Value,
}
*/


impl<'a, N: Node<'a>> Name<'a> for TreeName<N> {
    fn get_name(&self) -> &'a str {
        self.tree_node.get_code()
    }

    fn get_module_path(&self) -> Option<&str> {
        self.get_module().get_path()
    }

    fn get_start_position(&self) -> TreePosition {
        TreePosition {position: self.tree_node.start()}
    }

    fn get_end_position(&self) -> TreePosition {
        TreePosition {position: self.tree_node.end()}
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
