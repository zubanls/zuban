use crate::value::{Value, ValueKind};
use crate::cache::{ModuleIndex, Database};
use crate::file::Module;
use parsa::{CodeIndex, Node};

type Signatures = Vec<()>;
pub type Names<'a> = Vec<Box<dyn Name<'a>>>;
pub type ValueNames<'a> = Vec<Box<dyn ValueName<'a>>>;


pub struct TreePosition<'a> {
    module: &'a dyn Module,
    position: CodeIndex,
}

impl TreePosition<'_> {
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

    fn get_start_position(&self) -> TreePosition<'a>;

    fn get_end_position(&self) -> TreePosition<'a>;

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

    fn infer(&self) -> ValueNames<'a>;

    fn goto(&self) -> Names<'a>;

    fn is_definition(&self) -> bool {
        false
    }
}

pub trait ValueName<'a>: Name<'a> {
    fn get_kind(&self) -> ValueKind;
}

pub struct TreeName<'a, M: Module, N: Node<'a>> {
    database: &'a Database,
    module: &'a M,
    tree_node: N,
}

impl<'a, N: Node<'a>, M: Module> TreeName<'a, M, N> {
    pub fn new(database: &'a Database, module: &'a M, tree_node: N) -> Self {
        Self {database, tree_node, module}
    }
}

impl<'a, N: Node<'a>, M: Module> Name<'a> for TreeName<'a, M, N> {
    fn get_name(&self) -> &'a str {
        self.tree_node.get_code()
    }

    fn get_module_path(&self) -> Option<&str> {
        self.module.get_path()
    }

    fn get_start_position(&self) -> TreePosition<'a> {
        TreePosition {module: self.module, position: self.tree_node.start()}
    }

    fn get_end_position(&self) -> TreePosition<'a> {
        TreePosition {module: self.module, position: self.tree_node.end()}
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

    fn infer(&self) -> ValueNames<'a> {
        vec!()
    }

    fn goto(&self) -> Names<'a> {
        todo!()
    }
}

struct WithValueName<'a, V> {
    database: &'a Database,
    value: Box<V>,
}

impl<'a, V: Value<'a>> Name<'a> for WithValueName<'a, V> {
    fn get_name(&self) -> &'a str {
        self.value.get_name()
    }

    fn get_module_path(&self) -> Option<&str> {
        self.value.get_module().get_path()
    }

    fn get_start_position(&self) -> TreePosition<'a> {
        TreePosition {module: self.value.get_module(), position: todo!()}
    }

    fn get_end_position(&self) -> TreePosition<'a> {
        TreePosition {module: self.value.get_module(), position: todo!()}
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

    fn infer(&self) -> ValueNames<'a> {
        todo!()
    }

    fn goto(&self) -> Names<'a> {
        todo!()
    }

    /*
    fn is_implementation(&self) {
    }
    */
}

impl<'a, V: Value<'a>> ValueName<'a> for WithValueName<'a, V> {
    fn get_kind(&self) -> ValueKind {
        self.value.get_kind()
    }
}
