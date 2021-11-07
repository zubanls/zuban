use crate::database::Database;
use crate::file::PythonFile;
use crate::file_state::File;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::value::{Value, ValueKind};
use parsa_python_ast::{CodeIndex, Name as ASTName};
use std::fmt;
use std::mem;

type Signatures = Vec<()>;
pub type Names<'db> = Vec<Box<dyn Name<'db>>>;

pub struct TreePosition<'db> {
    file: &'db dyn File,
    position: CodeIndex,
}

impl TreePosition<'_> {
    fn byte_position(&self) -> CodeIndex {
        self.position
    }

    fn line_and_column(&self) -> (CodeIndex, CodeIndex) {
        unimplemented!();
    }
}

pub trait Name<'db>: fmt::Debug {
    fn name(&self) -> &'db str;

    fn file_path(&self) -> &str;

    fn start_position(&self) -> TreePosition<'db>;

    fn end_position(&self) -> TreePosition<'db>;

    // TODO
    //fn get_definition_start_and_end_position(&self) -> (TreePosition, TreePosition);

    fn documentation(&self) -> String;

    fn description(&self) -> String;

    fn qualified_names(&self) -> Option<Vec<String>>;

    fn is_implementation(&self) -> bool {
        true
    }

    fn type_hint(&self) -> Option<String> {
        None
    }

    fn signatures(&self) -> Signatures {
        vec![]
    }

    fn infer(&self) -> Inferred<'db>;

    fn goto(&self) -> Names<'db>;

    fn is_definition(&self) -> bool {
        false
    }
}

pub trait ValueName<'db>: Name<'db> {
    fn get_kind(&self) -> ValueKind;
}

pub struct TreeName<'db, F: File, N> {
    database: &'db Database,
    file: &'db F,
    ast_name: N,
}

impl<'db> fmt::Debug for TreeName<'db, PythonFile, ASTName<'db>> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("TreeName")
            .field("file", &self.file_path())
            .field("name", &self.name())
            .finish()
    }
}

impl<'db, F: File, N> TreeName<'db, F, N> {
    pub fn new(database: &'db Database, file: &'db F, ast_name: N) -> Self {
        Self {
            database,
            ast_name,
            file,
        }
    }
}

impl<'db> Name<'db> for TreeName<'db, PythonFile, ASTName<'db>> {
    fn name(&self) -> &'db str {
        self.ast_name.as_str()
    }

    fn file_path(&self) -> &str {
        self.database.get_file_path(self.file.file_index())
    }

    fn start_position(&self) -> TreePosition<'db> {
        TreePosition {
            file: self.file,
            position: self.ast_name.start(),
        }
    }

    fn end_position(&self) -> TreePosition<'db> {
        TreePosition {
            file: self.file,
            position: self.ast_name.end(),
        }
    }

    fn documentation(&self) -> String {
        todo!()
    }

    fn description(&self) -> String {
        todo!()
    }

    fn qualified_names(&self) -> Option<Vec<String>> {
        todo!()
    }

    /*
    fn is_implementation(&self) {
    }
    */

    fn infer(&self) -> Inferred<'db> {
        let mut i_s = InferenceState::new(self.database);
        self.file.get_inference(&mut i_s).infer_name(self.ast_name)
    }

    fn goto(&self) -> Names<'db> {
        todo!()
    }
}

pub struct WithValueName<'db, 'a> {
    database: &'db Database,
    value: &'a dyn Value<'db>,
}

impl<'db, 'a> WithValueName<'db, 'a> {
    pub fn new(database: &'db Database, value: &'a dyn Value<'db>) -> Self {
        Self { database, value }
    }
}

impl<'db, 'a> fmt::Debug for WithValueName<'db, 'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("WithValueName")
            .field("value", &self.value)
            .finish()
    }
}

impl<'db, 'a> Name<'db> for WithValueName<'db, 'a> {
    fn name(&self) -> &'db str {
        self.value.name()
    }

    fn file_path(&self) -> &str {
        todo!()
        //self.value.get_file().get_path()
    }

    fn start_position(&self) -> TreePosition<'db> {
        todo!()
        //TreePosition {file: self.value.get_file(), position: todo!()}
    }

    fn end_position(&self) -> TreePosition<'db> {
        todo!()
        //TreePosition {file: self.value.get_file(), position: todo!()}
    }

    fn documentation(&self) -> String {
        todo!()
    }

    fn description(&self) -> String {
        todo!()
    }

    fn qualified_names(&self) -> Option<Vec<String>> {
        todo!()
    }

    fn infer(&self) -> Inferred<'db> {
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

impl<'db, 'a> ValueName<'db> for WithValueName<'db, 'a> {
    fn get_kind(&self) -> ValueKind {
        self.value.get_kind()
    }
}

pub enum ValueNameIterator<T> {
    Single(T),
    Multiple(Vec<T>),
    Finished,
}

impl<'db, T> Iterator for ValueNameIterator<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Single(t) => {
                let result = mem::replace(self, Self::Finished);
                // Is this really the best way to do this? Please tell me!!!
                if let Self::Single(t) = result {
                    Some(t)
                } else {
                    unreachable!()
                }
            }
            Self::Multiple(list) => list.pop(),
            Self::Finished => None,
        }
    }
}
