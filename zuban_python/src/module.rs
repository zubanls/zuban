use parsa::{CodeIndex, NodeIndex, Node};

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

    fn get_tree_node(&self, name: NodeIndex) -> &dyn Node;
}
