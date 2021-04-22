use parsa::{CodeIndex, NodeIndex, Node};
use parsa_python::PythonTree;

pub type Names = Vec<()>;
pub type Name = u32;

pub enum Leaf {
    Name(Name),
    String,
    Number,
    Keyword(String),
    Other,
    None
}

pub trait Module {
    fn get_path(&self) -> Option<&str>;

    fn get_implementation(&self, names: Names) -> Names {
        vec!()
    }
    
    fn get_leaf(&self, position: CodeIndex) -> Leaf;

    fn infer(&self, name: NodeIndex) -> Names;

    fn goto(&self, name: NodeIndex) -> Names;

    fn get_tree_node(&self, index: NodeIndex) -> Box<dyn Node + '_>;
}


struct PythonModule {
    path: String,
    tree: PythonTree,
}

impl Module for PythonModule {
    fn get_path(&self) -> Option<&str> {
        Some(&self.path)
    }

    fn get_implementation(&self, names: Names) -> Names {
        todo!()
    }

    fn get_leaf(&self, position: CodeIndex) -> Leaf {
        let node = self.tree.get_leaf_by_position(position);
        todo!()
    }

    fn infer(&self, name: NodeIndex) -> Names {
        todo!()
    }

    fn goto(&self, name: NodeIndex) -> Names {
        todo!()
    }

    fn get_tree_node(&self, index: NodeIndex) -> Box<dyn Node + '_> {
        Box::new(self.tree.get_node_by_index(index))
    }
}
