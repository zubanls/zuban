use parsa::{CodeIndex, NodeIndex};

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
    fn get_implementation(&self, names: Names) -> Names {
        vec!()
    }
    
    fn get_leaf(&self, position: CodeIndex) -> Leaf {
        panic!();
    }

    fn infer(&self, name: NodeIndex) -> Names {
        vec!()
    }

    fn goto(&self, name: NodeIndex) -> Names {
        vec!()
    }

    fn get_name(&self, name: NodeIndex) -> &str;
}
