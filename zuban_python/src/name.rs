use crate::database::Database;
use crate::file::PythonFile;
use crate::file_state::File;
use crate::inference_state::InferenceState;
use crate::value::{Value, ValueKind};
use parsa::{CodeIndex, Node};
use parsa_python::{PyNode, PyNodeType, TerminalType};
use std::fmt;

type Signatures = Vec<()>;
pub type Names<'db> = Vec<Box<dyn Name<'db>>>;
pub type ValueNames<'db> = Vec<Box<dyn ValueName<'db> + 'db>>;

pub struct TreePosition<'db> {
    file: &'db dyn File,
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

pub trait Name<'db>: fmt::Debug {
    fn get_name(&self) -> &'db str;

    fn get_file_path(&self) -> &str;

    fn get_start_position(&self) -> TreePosition<'db>;

    fn get_end_position(&self) -> TreePosition<'db>;

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

    fn infer(&self) -> ValueNames<'db>;

    fn goto(&self) -> Names<'db>;

    fn is_definition(&self) -> bool {
        false
    }
}

pub trait ValueName<'db>: Name<'db> {
    fn get_kind(&self) -> ValueKind;
}

pub struct TreeName<'db, F: File, N: Node<'db>> {
    database: &'db Database,
    file: &'db F,
    tree_node: N,
}

impl<'db, F: File, N: Node<'db>> fmt::Debug for TreeName<'db, F, N>
where
    Self: LanguageTreeName<'db>,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("TreeName")
            .field("file", &self.get_file_path())
            .field("name", &self.get_name())
            .finish()
    }
}

impl<'db, F: File, N: Node<'db>> TreeName<'db, F, N> {
    pub fn new(database: &'db Database, file: &'db F, tree_node: N) -> Self {
        Self {
            database,
            tree_node,
            file,
        }
    }
}

pub trait LanguageTreeName<'db> {
    fn tree_infer(&self) -> ValueNames<'db>;
    fn tree_goto(&self) -> Names<'db>;
}

impl<'db> LanguageTreeName<'db> for TreeName<'db, PythonFile, PyNode<'db>> {
    fn tree_infer(&self) -> ValueNames<'db> {
        if let PyNodeType::Terminal(TerminalType::Name) = self.tree_node.get_type() {
            let mut i_s = InferenceState::new(self.database);
            self.file
                .get_inference(&mut i_s, None)
                .infer_name(self.tree_node)
                .to_value_names(&mut i_s)
        } else {
            vec![]
        }
    }

    fn tree_goto(&self) -> Names<'db> {
        todo!()
    }
}

impl<'db, F: File, N: Node<'db>> Name<'db> for TreeName<'db, F, N>
where
    TreeName<'db, F, N>: LanguageTreeName<'db>,
{
    fn get_name(&self) -> &'db str {
        self.tree_node.get_code()
    }

    fn get_file_path(&self) -> &str {
        self.database.get_file_path(self.file.get_file_index())
    }

    fn get_start_position(&self) -> TreePosition<'db> {
        TreePosition {
            file: self.file,
            position: self.tree_node.start(),
        }
    }

    fn get_end_position(&self) -> TreePosition<'db> {
        TreePosition {
            file: self.file,
            position: self.tree_node.end(),
        }
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

    fn infer(&self) -> ValueNames<'db> {
        self.tree_infer()
    }

    fn goto(&self) -> Names<'db> {
        self.tree_goto()
    }
}

pub struct WithValueName<'db, T> {
    database: &'db Database,
    value: T,
}

impl<'db, T> WithValueName<'db, T> {
    pub fn new(database: &'db Database, value: T) -> Self {
        Self { database, value }
    }
}

impl<'db, T: fmt::Debug> fmt::Debug for WithValueName<'db, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("WithValueName")
            .field("value", &self.value)
            .finish()
    }
}

impl<'db, T: Value<'db>> Name<'db> for WithValueName<'db, T> {
    fn get_name(&self) -> &'db str {
        self.value.get_name()
    }

    fn get_file_path(&self) -> &str {
        todo!()
        //self.value.get_file().get_path()
    }

    fn get_start_position(&self) -> TreePosition<'db> {
        todo!()
        //TreePosition {file: self.value.get_file(), position: todo!()}
    }

    fn get_end_position(&self) -> TreePosition<'db> {
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

    fn infer(&self) -> ValueNames<'db> {
        todo!()
    }

    fn goto(&self) -> Names<'db> {
        todo!()
    }

    /*
    fn is_implementation(&self) {
    }
    */
}

impl<'db, T: Value<'db>> ValueName<'db> for WithValueName<'db, T> {
    fn get_kind(&self) -> ValueKind {
        self.value.get_kind()
    }
}
