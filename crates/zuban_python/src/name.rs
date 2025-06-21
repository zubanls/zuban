use std::fmt;

use parsa_python_cst::{Name as CSTName, NameParent};
use vfs::NormalizedPath;

use crate::{
    database::{Database, ParentScope},
    file::PythonFile,
    inference_state::InferenceState,
    inferred::Inferred,
    node_ref::NodeRef,
};

pub type Names<'db> = Vec<Box<dyn Name<'db>>>;

pub trait Name<'db>: fmt::Debug {
    fn name(&self) -> &str;
    fn file_path(&self) -> &NormalizedPath;
    fn documentation(&self) -> String;
    fn description(&self) -> String;
    fn qualified_name(&self) -> String;
    fn is_implementation(&self) -> bool {
        true
    }
    fn kind(&self) -> SymbolKind;
    /*
    fn type_hint(&self) -> Option<String> {
        None
    }
    fn signatures(&self) -> Signatures {
        vec![]
    }
    */
}

#[derive(Debug)]
pub(crate) struct TreeName<'db> {
    db: &'db Database,
    file: &'db PythonFile,
    parent_scope: ParentScope,
    cst_name: CSTName<'db>,
}

impl<'db> TreeName<'db> {
    pub fn new(
        db: &'db Database,
        file: &'db PythonFile,
        parent_scope: ParentScope,
        cst_name: CSTName<'db>,
    ) -> Self {
        Self {
            db,
            cst_name,
            parent_scope,
            file,
        }
    }

    pub(crate) fn infer(&self) -> Inferred {
        let i_s = &InferenceState::new(self.db, self.file);
        match self.cst_name.parent() {
            NameParent::NameDef(_) => todo!(),
            NameParent::Atom(atom) => {
                if let Some(expr) = atom.maybe_expression_parent() {
                    let n = NodeRef::new(self.file, expr.index());
                    if let Some(inf) = n.maybe_inferred(i_s) {
                        return inf;
                    }
                }
            }
            NameParent::Primary(_) => todo!(),
            NameParent::PrimaryTarget(_) => todo!(),
            NameParent::Kwarg(_) => todo!(),
            NameParent::KeywordPattern(_) => todo!(),
            NameParent::ImportFromAsName(_) => todo!(),
            NameParent::DottedName(_) => todo!(),
            NameParent::FStringConversion(_) => todo!(),
        }
        /*
        let p = node_ref.point();
        if p.calculated() {
            if p.kind() == PointKind::Redirect {
                let redirected_to = p.as_redirected_node_ref(self.db);
            }
        }
        */
        Inferred::new_never(crate::type_::NeverCause::Other) // TODO
    }
}

impl<'db> Name<'db> for TreeName<'db> {
    fn name(&self) -> &str {
        self.cst_name.as_str()
    }

    fn file_path(&self) -> &NormalizedPath {
        self.db.file_path(self.file.file_index)
    }

    fn documentation(&self) -> String {
        unimplemented!()
    }

    fn description(&self) -> String {
        unimplemented!()
    }

    fn qualified_name(&self) -> String {
        self.parent_scope.qualified_name(
            self.db,
            NodeRef::new(self.file, self.cst_name.index()),
            self.cst_name.as_code(),
        )
    }

    fn is_implementation(&self) -> bool {
        // TODO this is incomplete
        !self.file.is_stub()
    }

    fn kind(&self) -> SymbolKind {
        SymbolKind::Object
    }
}

/*
struct WithValueName<'db, 'a, 'b> {
    db: &'db Database,
    value: &'b dyn Value<'db, 'a>,
}

impl<'db, 'a, 'b> WithValueName<'db, 'a, 'b> {
    pub fn new(db: &'db Database, value: &'b dyn Value<'db, 'a>) -> Self {
        Self { db, value }
    }
}

impl fmt::Debug for WithValueName<'_, '_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("WithValueName")
            .field("value", &self.value)
            .finish()
    }
}

impl<'db> Name<'db> for WithValueName<'db, '_, '_> {
    fn name(&self) -> &str {
        unimplemented!()
        //self.value.name()
    }

    fn file_path(&self) -> &str {
        unimplemented!()
        //self.value.file().path()
    }

    fn start_position(&self) -> TreePosition<'db> {
        unimplemented!()
        //TreePosition {file: self.value.file(), position: unimplemented!()}
    }

    fn end_position(&self) -> TreePosition<'db> {
        unimplemented!()
        //TreePosition {file: self.value.file(), position: unimplemented!()}
    }

    fn documentation(&self) -> String {
        unimplemented!()
    }

    fn description(&self) -> String {
        unimplemented!()
    }

    fn qualified_names(&self) -> Option<Vec<String>> {
        unimplemented!()
    }

    fn infer(&self) -> Inferred {
        unimplemented!()
    }

    fn goto(&self) -> Names<'db> {
        unimplemented!()
    }

    /*
    fn is_implementation(&self) {
    }
    */
}

enum ValueNameIterator<T> {
    Single(T),
    Multiple(Vec<T>),
    Finished,
}

impl<T> Iterator for ValueNameIterator<T> {
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
*/

#[derive(Debug, Eq, PartialEq)]
pub enum SymbolKind {
    Unknown = 0,
    // Taken from LSP, unused kinds are commented
    //File = 1,
    Module = 2,
    Namespace = 3,
    //Package = 4,
    Class = 5,
    Method = 6,
    Property = 7,
    Field = 8,
    //Constructor = 9,
    //Enum = 10,
    //Interface = 11,
    Function = 12,
    //Variable = 13,
    Constant = 14,
    String = 15,
    Number = 16,
    Bool = 17,
    Array = 18,
    Object = 19, // From JavaScript objects -> Basically an instance
    //Key = 20,
    Null = 21,
    //EnumMember = 22,
    //Struct = 23,
    //Event = 24,
    //Operator = 25,
    TypeParameter = 26,
}
