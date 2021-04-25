use parsa::{CodeIndex, NodeIndex, Node};
use parsa_python::{PythonTree, PythonTerminalType, PythonNodeType};
use crate::name::{Name, Names, TreeName};
use crate::cache::StateDB;

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
    
    fn get_leaf<'a>(&'a self, state_db: &'a StateDB, position: CodeIndex) -> Leaf<'a>;

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

    fn get_leaf<'a>(&'a self, state_db: &'a StateDB, position: CodeIndex) -> Leaf<'a> {
        let node = self.tree.get_leaf_by_position(position);
        match node.get_type() {
            PythonNodeType::Terminal(t) | PythonNodeType::ErrorTerminal(t) => {
                match t {
                    PythonTerminalType::Name => Leaf::Name(Box::new(
                        TreeName::new(state_db, self, node)
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

    fn get_tree_node(&self, index: NodeIndex) -> Box<dyn Node + '_> {
        Box::new(self.tree.get_node_by_index(index))
    }
}
