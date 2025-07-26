use std::borrow::Cow;

use parsa_python_cst::{ClassDef, FunctionDef, Name as CSTName, Scope};
use vfs::NormalizedPath;

use crate::{
    completion::ScopesIterator,
    database::{Database, ParentScope},
    file::{ClassNodeRef, File as _, FuncNodeRef, PythonFile},
    inference_state::InferenceState,
    node_ref::NodeRef,
    type_::{LookupResult, Type},
    type_helpers::Class,
    PositionInfos,
};

pub type Range<'a> = (PositionInfos<'a>, PositionInfos<'a>);

#[derive(Debug)]
pub enum Name<'db> {
    TreeName(TreeName<'db>),
    ModuleName(ModuleName<'db>),
    NodeName(NodeName<'db>),
}

#[derive(Debug)]
pub struct ValueName<'x> {
    pub(crate) db: &'x Database,
    pub(crate) type_: &'x Type,
    pub name: Name<'x>,
}

impl ValueName<'_> {
    pub fn type_description(&self) -> Box<str> {
        self.type_.format_short(self.db)
    }

    /// This is mostly for testing, you should probably not use this.
    pub fn is_instance(&self) -> bool {
        !matches!(
            self.type_,
            Type::Type(_) | Type::Callable(_) | Type::Module(_) | Type::FunctionOverload(_)
        )
    }
}

impl<'x> Name<'x> {
    pub fn name(&self) -> &str {
        match self {
            Name::TreeName(n) => n.cst_name.as_str(),
            Name::ModuleName(n) => n.file.name_and_parent_dir(n.db).0,
            Name::NodeName(n) => n.name,
        }
    }

    pub fn code(&self) -> &str {
        self.file().tree.code()
    }

    pub(crate) fn file(&self) -> &'x PythonFile {
        match self {
            Name::TreeName(TreeName { file, .. })
            | Name::ModuleName(ModuleName { file, .. })
            | Name::NodeName(NodeName {
                node_ref: NodeRef { file, .. },
                ..
            }) => file,
        }
    }

    pub(crate) fn db(&self) -> &'x Database {
        match self {
            Name::TreeName(tree_name) => tree_name.db,
            Name::ModuleName(module_name) => module_name.db,
            Name::NodeName(node_name) => node_name.db,
        }
    }

    pub fn file_path(&self) -> &NormalizedPath {
        match self {
            Name::TreeName(TreeName { db, file, .. })
            | Name::ModuleName(ModuleName { db, file, .. })
            | Name::NodeName(NodeName {
                db,
                node_ref: NodeRef { file, .. },
                ..
            }) => file.file_path(db),
        }
    }

    pub fn relative_path(&self, base: &NormalizedPath) -> &str {
        let p = self.file_path();
        if let Ok(stripped) = p.as_ref().strip_prefix(base.as_ref()) {
            stripped.to_str().unwrap()
        } else {
            p
        }
    }

    pub fn qualified_name(&self) -> String {
        match self {
            Name::TreeName(n) => {
                let parent_scope = match n.parent_scope {
                    Scope::Module => ParentScope::Module,
                    Scope::Class(class_def) => ParentScope::Class(class_def.index()),
                    Scope::Function(function_def) => ParentScope::Function(function_def.index()),
                    Scope::Lambda(_) => {
                        return ParentScope::qualified_name_for_unreachable_scope(
                            n.db,
                            NodeRef::new(n.file, n.cst_name.index()),
                            n.cst_name.as_code(),
                        )
                    }
                };
                parent_scope.qualified_name(
                    n.db,
                    NodeRef::new(n.file, n.cst_name.index()),
                    n.cst_name.as_code(),
                )
            }
            Name::ModuleName(n) => n.file.qualified_name(n.db),
            Name::NodeName(n) => n.name.to_string(),
        }
    }

    pub fn qualified_name_of_file(&self) -> String {
        self.file().qualified_name(self.db())
    }

    pub fn is_implementation(&self) -> bool {
        !self.file().is_stub()
    }

    pub fn in_stub(&self) -> bool {
        self.file().is_stub()
    }

    pub fn kind(&self) -> SymbolKind {
        match self {
            Name::TreeName(_) => SymbolKind::Object,
            Name::ModuleName(_) => SymbolKind::Module,
            Name::NodeName(_) => SymbolKind::Object,
        }
    }

    pub fn name_range(&self) -> Range {
        match self {
            Name::TreeName(n) => (
                n.file.byte_to_position_infos(n.db, n.cst_name.start()),
                n.file.byte_to_position_infos(n.db, n.cst_name.end()),
            ),
            Name::ModuleName(n) => {
                let start_of_file = n.file.byte_to_position_infos(n.db, 0);
                (start_of_file, start_of_file)
            }
            Name::NodeName(name) => {
                let n = name.node_ref;
                let start = n.node_start_position();
                let end = n.node_end_position();
                (
                    n.file.byte_to_position_infos(name.db, start),
                    n.file.byte_to_position_infos(name.db, end),
                )
            }
        }
    }
    // Can e.g. be the full name
    pub fn target_range(&self) -> Range {
        match self {
            Name::TreeName(n) => {
                if let Some(name_def) = n.cst_name.name_def() {
                    let (start, end) = name_def.definition_range();
                    (
                        n.file.byte_to_position_infos(n.db, start),
                        n.file.byte_to_position_infos(n.db, end),
                    )
                } else {
                    // This should not really happen
                    self.name_range()
                }
            }
            _ => self.name_range(),
        }
    }

    pub fn target_range_code(&self) -> &str {
        let (start, end) = self.target_range();
        start.code_until(end)
    }

    pub(crate) fn goto_non_stub(&self) -> Option<Name<'x>> {
        match self {
            Name::TreeName(n) => {
                let file = n.file.normal_file_of_stub_file(n.db)?;
                self.goto_helper(n, file)
            }
            Name::ModuleName(n) => {
                let file = n.file.normal_file_of_stub_file(n.db)?;
                Some(Self::ModuleName(ModuleName { db: n.db, file }))
            }
            Name::NodeName(_) => None,
        }
    }

    fn goto_helper(&self, n: &TreeName<'x>, to_file: &'x PythonFile) -> Option<Self> {
        let db = n.db;
        let result = to_file.ensure_module_symbols_flow_analysis(db);
        debug_assert!(result.is_ok());

        let scopes = ScopesIterator {
            file: self.file(),
            only_reachable: true,
            current: Some(n.parent_scope),
        };
        let ref_ = lookup_parent_scope_in_other_file(db, to_file, scopes)?
            .lookup(db, n.cst_name.as_code())?;
        Some(Self::TreeName(TreeName::with_unknown_parent_scope(
            db,
            ref_.file,
            ref_.maybe_name()?,
        )))
    }

    pub(crate) fn goto_stub(&self) -> Option<Name<'x>> {
        match self {
            Name::TreeName(n) => {
                let file = n.file.stub_file_of_normal_file(n.db)?;
                self.goto_helper(n, file)
            }
            Name::ModuleName(n) => {
                let file = n.file.stub_file_of_normal_file(n.db)?;
                Some(Self::ModuleName(ModuleName { db: n.db, file }))
            }
            Name::NodeName(_) => None,
        }
    }

    pub fn documentation(&self) -> Cow<'x, str> {
        let result = match self {
            Name::TreeName(n) => n.cst_name.clean_docstring(),
            Name::ModuleName(n) => n.file.tree.root().clean_docstring(),
            Name::NodeName(_) => Cow::Borrowed(""),
        };
        if result.is_empty() && self.file().is_stub() {
            if let Some(name) = self.goto_non_stub() {
                debug_assert!(!name.file().is_stub());
                return name.documentation();
            }
        }
        result
    }
}

enum FileOrClass<'a> {
    File(&'a PythonFile),
    Class(Class<'a>),
}

impl<'a> FileOrClass<'a> {
    fn lookup(&self, db: &'a Database, name: &str) -> Option<NodeRef<'a>> {
        match self {
            FileOrClass::File(file) => file.lookup_symbol(name),
            FileOrClass::Class(class) => {
                let i_s = &InferenceState::from_class(db, class);
                let LookupResult::GotoName { name, .. } = class.lookup_symbol(i_s, name) else {
                    return None;
                };
                Some(NodeRef::from_link(db, name))
            }
        }
    }
}

fn lookup_parent_scope_in_other_file<'db>(
    db: &'db Database,
    file: &'db PythonFile,
    mut reachable_scopes: ScopesIterator,
) -> Option<FileOrClass<'db>> {
    match reachable_scopes.next()? {
        Scope::Module => Some(FileOrClass::File(file)),
        Scope::Class(c) => {
            let from_parent = lookup_parent_scope_in_other_file(db, file, reachable_scopes)?;
            let cls = from_parent
                .lookup(db, c.name().as_code())?
                .maybe_name_of_class()?;
            Some(FileOrClass::Class(Class::with_self_generics(
                db,
                ClassNodeRef::new(file, cls.index()),
            )))
        }
        Scope::Function(_) | Scope::Lambda(_) => return None,
    }
}

#[derive(Debug)]
pub struct TreeName<'db> {
    pub(crate) db: &'db Database,
    pub(crate) file: &'db PythonFile,
    pub(crate) parent_scope: Scope<'db>,
    pub(crate) cst_name: CSTName<'db>,
}

impl<'db> TreeName<'db> {
    pub(crate) fn new(
        db: &'db Database,
        file: &'db PythonFile,
        parent_scope: Scope<'db>,
        cst_name: CSTName<'db>,
    ) -> Self {
        Self {
            db,
            cst_name,
            parent_scope,
            file,
        }
    }

    pub(crate) fn with_unknown_parent_scope(
        db: &'db Database,
        file: &'db PythonFile,
        cst_name: CSTName<'db>,
    ) -> Self {
        let mut parent_scope = cst_name.parent_scope();
        // The parent scope of a function/class name is not the respective func/class
        match parent_scope {
            Scope::Class(class_def) => {
                if class_def.name_def().name_index() == cst_name.index() {
                    parent_scope = parent_scope_to_scope(
                        file,
                        ClassNodeRef::new(file, class_def.index())
                            .class_storage()
                            .parent_scope,
                    )
                }
            }
            Scope::Function(function_def) => {
                if function_def.name_def().name_index() == cst_name.index() {
                    parent_scope = parent_scope_to_scope(
                        file,
                        FuncNodeRef::new(file, function_def.index()).parent_scope(),
                    )
                }
            }
            _ => (),
        }
        Self {
            db,
            cst_name,
            parent_scope,
            file,
        }
    }

    pub(crate) fn with_parent_scope(
        db: &'db Database,
        file: &'db PythonFile,
        parent_scope: ParentScope,
        cst_name: CSTName<'db>,
    ) -> Self {
        Self {
            db,
            cst_name,
            parent_scope: parent_scope_to_scope(file, parent_scope),
            file,
        }
    }
}

fn parent_scope_to_scope(file: &PythonFile, parent_scope: ParentScope) -> Scope {
    match parent_scope {
        ParentScope::Module => Scope::Module,
        ParentScope::Function(f) => Scope::Function(FunctionDef::by_index(&file.tree, f)),
        ParentScope::Class(c) => Scope::Class(ClassDef::by_index(&file.tree, c)),
    }
}

#[derive(Debug)]
pub struct NodeName<'db> {
    db: &'db Database,
    node_ref: NodeRef<'db>,
    name: &'db str,
}

impl<'db> NodeName<'db> {
    pub(crate) fn new(db: &'db Database, node_ref: NodeRef<'db>, name: &'db str) -> Self {
        Self { db, node_ref, name }
    }
}

#[derive(Debug)]
pub struct ModuleName<'db> {
    pub(crate) db: &'db Database,
    pub(crate) file: &'db PythonFile,
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
