use parsa::{CodeIndex, NodeIndex, Node};
use parsa_python::{PythonTree, PythonTerminalType, PythonNodeType};
use crate::name::{Name, TreeName};
use crate::cache::StateDB;

pub type Names<'a> = Vec<Box<dyn Name<'a>>>;

pub enum Leaf<'a> {
    Name(Box<dyn Name<'a> + 'a>),
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
    
    fn get_leaf(&self, state_db: *mut StateDB, position: CodeIndex) -> Leaf;

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

    fn get_leaf(&self, state_db: *mut StateDB, position: CodeIndex) -> Leaf {
        let node = self.tree.get_leaf_by_position(position);
        match node.get_type() {
            PythonNodeType::Terminal(t) | PythonNodeType::ErrorTerminal(t) => {
                use crate::cache::ModuleIndex;
                match t {
                    PythonTerminalType::Name => Leaf::Name(Box::new(
                        TreeName::new(state_db, ModuleIndex(1), node)
                    )),
                    _ => Leaf::None,
                }
            }
            PythonNodeType::ErrorKeyword | PythonNodeType::Keyword => {
                Leaf::Keyword(node.get_code().to_owned())
            }
            PythonNodeType::Nonterminal(_) | PythonNodeType::ErrorNonterminal(_) => panic!(),
        }
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
