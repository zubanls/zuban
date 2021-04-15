use parsa::CodeIndex;

pub type Names = Vec<()>;
pub type Leaf = ();

pub trait Module {
    fn get_implementation(&self, names: Names) -> Names {
        vec!()
    }
    
    fn get_leaf(&self, position: CodeIndex) -> Leaf {
        panic!();
    }
}
