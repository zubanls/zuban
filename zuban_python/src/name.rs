use std::fmt;
use std::borrow::Borrow;
use crate::value::{Value, ValueKind};
use crate::database::{Database};
use crate::file::{File, PythonFile};
use parsa::{CodeIndex, Node};
use parsa_python::{PyNode, PyNodeType, TerminalType};

type Signatures = Vec<()>;
pub type Names<'a> = Vec<Box<dyn Name<'a>>>;
pub type ValueNames<'a> = Vec<Box<dyn ValueName<'a> + 'a>>;


pub struct TreePosition<'a> {
    file: &'a dyn File,
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

pub trait Name<'a>: fmt::Debug {
    fn get_name(&self) -> &'a str;

    fn get_file_path(&self) -> &str;

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
        vec![]
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

pub struct TreeName<'a, F: File, N: Node<'a>> {
    database: &'a Database,
    file: &'a F,
    tree_node: N,
}

impl<'a, F: File, N: Node<'a>> fmt::Debug for TreeName<'a, F, N> where Self: LanguageTreeName<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("TreeName")
         .field("file", &self.get_file_path())
         .field("name", &self.get_name())
         .finish()
    }
}

impl<'a, F: File, N: Node<'a>> TreeName<'a, F, N> {
    pub fn new(database: &'a Database, file: &'a F, tree_node: N) -> Self {
        Self {database, tree_node, file}
    }
}

pub trait LanguageTreeName<'a> {
    fn tree_infer(&self) -> ValueNames<'a>;
    fn tree_goto(&self) -> Names<'a>;
}

impl<'a> LanguageTreeName<'a> for TreeName<'a, PythonFile, PyNode<'a>> {
    fn tree_infer(&self) -> ValueNames<'a> {
        if let PyNodeType::Terminal(TerminalType::Name) = self.tree_node.get_type() {
            self.file.infer_name(self.database, self.tree_node)
        } else {
            vec![]
        }
    }

    fn tree_goto(&self) -> Names<'a> {
        todo!()
    }
}

impl<'a, F: File, N: Node<'a>> Name<'a> for TreeName<'a, F, N>
        where TreeName<'a, F, N>: LanguageTreeName<'a> {
    fn get_name(&self) -> &'a str {
        self.tree_node.get_code()
    }

    fn get_file_path(&self) -> &str {
        self.database.get_file_path(self.file.get_file_index())
    }

    fn get_start_position(&self) -> TreePosition<'a> {
        TreePosition {file: self.file, position: self.tree_node.start()}
    }

    fn get_end_position(&self) -> TreePosition<'a> {
        TreePosition {file: self.file, position: self.tree_node.end()}
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
        self.tree_infer()
    }

    fn goto(&self) -> Names<'a> {
        self.tree_goto()
    }
}

pub struct WithValueName<'a, T> {
    database: &'a Database,
    value: T,
}

impl<'a, T> WithValueName<'a, T> {
    pub fn new(database: &'a Database, value: T) -> Self {
        Self {database, value}
    }
}

impl<'a, T: fmt::Debug> fmt::Debug for WithValueName<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("WithValueName")
         .field("value", &self.value)
         .finish()
    }
}

impl<'a, T: Value<'a>> Name<'a> for WithValueName<'a, T> {
    fn get_name(&self) -> &'a str {
        self.value.borrow().get_name()
    }

    fn get_file_path(&self) -> &str {
        todo!()
        //self.value.get_file().get_path()
    }

    fn get_start_position(&self) -> TreePosition<'a> {
        todo!()
        //TreePosition {file: self.value.get_file(), position: todo!()}
    }

    fn get_end_position(&self) -> TreePosition<'a> {
        todo!()
        //TreePosition {file: self.value.get_file(), position: todo!()}
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

impl<'a, T: Value<'a>> ValueName<'a> for WithValueName<'a, T> {
    fn get_kind(&self) -> ValueKind {
        self.value.borrow().get_kind()
    }
}
