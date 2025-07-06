use std::fmt;

use parsa_python_cst::Name as CSTName;
use vfs::NormalizedPath;

use crate::{
    database::{Database, ParentScope},
    file::{File as _, PythonFile},
    node_ref::NodeRef,
    type_::{DbString, Type},
    PositionInfos,
};

pub type Range<'a> = (PositionInfos<'a>, PositionInfos<'a>);
pub type Names = Vec<Box<dyn Name>>;

pub trait Name: fmt::Debug {
    fn name(&self) -> &str;
    fn code(&self) -> &str;
    fn file_path(&self) -> &NormalizedPath;
    fn qualified_name(&self) -> String;
    fn is_implementation(&self) -> bool {
        true
    }
    fn kind(&self) -> SymbolKind;

    fn name_range(&self) -> Range;
    // Can e.g. be the full name
    fn target_range(&self) -> Range;
    fn target_range_code(&self) -> &str {
        let (start, end) = self.target_range();
        start.code_until(end)
    }
}

#[derive(Debug)]
pub struct ValueName<'x> {
    pub(crate) db: &'x Database,
    pub(crate) type_: &'x Type,
    pub(crate) name: &'x dyn Name,
}

impl Name for ValueName<'_> {
    fn name(&self) -> &str {
        self.name.name()
    }
    fn file_path(&self) -> &NormalizedPath {
        self.name.file_path()
    }
    fn code(&self) -> &str {
        self.name.code()
    }
    fn qualified_name(&self) -> String {
        self.name.qualified_name()
    }
    fn kind(&self) -> SymbolKind {
        self.name.kind()
    }
    fn name_range(&self) -> Range {
        self.name.name_range()
    }
    fn target_range(&self) -> Range {
        self.name.target_range()
    }
}

impl ValueName<'_> {
    pub fn type_description(&self) -> Box<str> {
        self.type_.format_short(self.db)
    }

    /// This is mostly for testing, you should probably not use this.
    pub fn is_instance(&self) -> bool {
        !matches!(self.type_, Type::Type(_) | Type::Callable(_))
    }
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
}

impl<'db> Name for TreeName<'db> {
    fn name(&self) -> &str {
        self.cst_name.as_str()
    }

    fn file_path(&self) -> &NormalizedPath {
        self.db.file_path(self.file.file_index)
    }
    fn code(&self) -> &str {
        self.file.tree.code()
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

    fn name_range(&self) -> Range {
        (
            self.file
                .byte_to_position_infos(self.db, self.cst_name.start()),
            self.file
                .byte_to_position_infos(self.db, self.cst_name.end()),
        )
    }
    fn target_range(&self) -> Range {
        if let Some(name_def) = self.cst_name.name_def() {
            let (start, end) = name_def.definition_range();
            (
                self.file.byte_to_position_infos(self.db, start),
                self.file.byte_to_position_infos(self.db, end),
            )
        } else {
            // This should not really happen
            self.name_range()
        }
    }
}

#[derive(Debug)]
pub struct ModuleName<'db> {
    db: &'db Database,
    file: &'db PythonFile,
    parent_scope: ParentScope,
    name: DbString,
}

impl<'db> Name for ModuleName<'db> {
    fn name(&self) -> &str {
        self.name.as_str(self.db)
    }

    fn file_path(&self) -> &NormalizedPath {
        self.db.file_path(self.file.file_index)
    }
    fn code(&self) -> &str {
        self.file.tree.code()
    }

    fn qualified_name(&self) -> String {
        self.file.qualified_name(self.db)
    }

    fn is_implementation(&self) -> bool {
        // TODO this is incomplete
        !self.file.is_stub()
    }

    fn kind(&self) -> SymbolKind {
        SymbolKind::Module
    }

    fn name_range(&self) -> Range {
        unimplemented!()
    }
    fn target_range(&self) -> Range {
        todo!()
    }
}

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
