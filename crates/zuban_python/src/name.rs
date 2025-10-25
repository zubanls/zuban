use std::borrow::Cow;

use lsp_types::SymbolKind;
use parsa_python_cst::{
    ClassDef, DefiningStmt, FunctionDef, Name as CSTName, NameParent, NodeIndex, Scope, TypeLike,
};
use vfs::NormalizedPath;

use crate::{
    PositionInfos,
    completion::ScopesIterator,
    database::{Database, ParentScope},
    file::{ClassNodeRef, File, FuncNodeRef, PythonFile},
    format_data::FormatData,
    inference_state::InferenceState,
    node_ref::NodeRef,
    type_::{LookupResult, Type},
    type_helpers::Class,
    utils::SymbolTable,
};

pub type Range<'a> = (PositionInfos<'a>, PositionInfos<'a>);

#[derive(Debug)]
pub enum Name<'db, 'x> {
    TreeName(TreeName<'db>),
    ModuleName(ModuleName<'db>),
    NodeName(NodeName<'db, 'x>),
}

#[derive(Debug)]
pub struct ValueName<'db, 'x> {
    pub(crate) type_: &'x Type,
    pub name: Name<'db, 'x>,
}

impl ValueName<'_, '_> {
    pub fn type_description(&self) -> Box<str> {
        self.type_.format_short(self.name.db())
    }

    pub fn maybe_pretty_function_type(&self) -> Option<Box<str>> {
        match self.type_ {
            Type::Callable(c) => Some(c.format_pretty(&FormatData::new_short(self.name.db()))),
            _ => None,
        }
    }

    /// This is mostly for testing, you should probably not use this.
    pub fn is_instance(&self) -> bool {
        !matches!(
            self.type_,
            Type::Type(_) | Type::Callable(_) | Type::Module(_) | Type::FunctionOverload(_)
        )
    }
}

impl<'db, 'x> Name<'db, 'x> {
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

    pub(crate) fn file(&self) -> &'db PythonFile {
        match self {
            Name::TreeName(TreeName { file, .. })
            | Name::ModuleName(ModuleName { file, .. })
            | Name::NodeName(NodeName {
                node_ref: NodeRef { file, .. },
                ..
            }) => file,
        }
    }

    pub(crate) fn db(&self) -> &'db Database {
        match self {
            Name::TreeName(tree_name) => tree_name.db,
            Name::ModuleName(module_name) => module_name.db,
            Name::NodeName(node_name) => node_name.db,
        }
    }

    pub fn file_uri(&self) -> String {
        self.db().vfs.file_path(self.file().file_index).as_uri()
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

    pub fn path_relative_to_workspace(&self) -> String {
        let db = self.db();
        self.file().file_entry(db).relative_path(&*db.vfs.handler)
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
                        );
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

    pub fn simple_qualified_name_of_parent_without_file(&self) -> Option<String> {
        match self {
            Name::TreeName(n) => {
                fn qualified(file: &PythonFile, scope: Scope) -> Option<String> {
                    match scope {
                        Scope::Class(class_def) => {
                            let parent_scope = ClassNodeRef::new(file, class_def.index())
                                .class_storage()
                                .parent_scope;
                            let name = class_def.name().as_code();
                            match parent_scope {
                                ParentScope::Module => Some(name.into()),
                                ParentScope::Function(_) => None,
                                ParentScope::Class(cls_index) => {
                                    let parent = qualified(
                                        file,
                                        Scope::Class(
                                            ClassNodeRef::new(file, cls_index)
                                                .maybe_class()
                                                .unwrap(),
                                        ),
                                    )?;
                                    Some(format!("{parent}.{name}"))
                                }
                            }
                        }
                        Scope::Function(_) | Scope::Module | Scope::Lambda(_) => None,
                    }
                }
                qualified(n.file, n.parent_scope)
            }
            Name::ModuleName(_) | Name::NodeName(_) => None,
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

    pub fn is_definition(&self) -> bool {
        match self {
            Name::TreeName(n) => n.cst_name.name_def().is_some(),
            Name::ModuleName(_) => true,
            Name::NodeName(_) => false,
        }
    }

    pub fn lsp_kind(&self) -> SymbolKind {
        match self {
            Name::TreeName(tree_name) => tree_name.lsp_kind(),
            Name::ModuleName(_) => SymbolKind::MODULE,
            Name::NodeName(_) => SymbolKind::OBJECT,
        }
    }

    pub fn name_range(&self) -> Range<'db> {
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
    pub fn target_range(&self) -> Range<'_> {
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

    pub(crate) fn goto_non_stub(&self) -> Option<Name<'db, 'x>> {
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

    fn goto_helper(&self, n: &TreeName<'db>, to_file: &'db PythonFile) -> Option<Self> {
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

    pub(crate) fn goto_stub(&self) -> Option<Name<'db, 'x>> {
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

    pub fn origin_kind(&self) -> &'static str {
        match self {
            Name::TreeName(tree_name) => match tree_name.cst_name.parent() {
                NameParent::NameDef(name_def) => match name_def.expect_defining_stmt() {
                    DefiningStmt::FunctionDef(func) => {
                        if func.name_def().index() == name_def.index() {
                            "function"
                        } else {
                            "param"
                        }
                    }
                    DefiningStmt::ClassDef(_) => "class",
                    DefiningStmt::ImportName(_) | DefiningStmt::ImportFromAsName(_) => "import",
                    DefiningStmt::Lambda(_) => "param",
                    DefiningStmt::TypeAlias(_) => "type",
                    _ => "variable",
                },
                NameParent::Kwarg(_) => "param",
                NameParent::ImportFromAsName(_) | NameParent::DottedImportName(_) => "pattern",
                NameParent::KeywordPattern(_) | NameParent::DottedPatternName(_) => "pattern",
                NameParent::FStringConversion(_) => "fstring-conversion",
                _ => "reference",
            },
            Name::ModuleName(_) => "module",
            Name::NodeName(_) => "object",
        }
    }

    pub fn documentation(&self) -> Cow<'db, str> {
        let result = match self {
            Name::TreeName(n) => n.cst_name.clean_docstring(),
            Name::ModuleName(n) => n.file.tree.root().clean_docstring(),
            Name::NodeName(_) => Cow::Borrowed(""),
        };
        if result.is_empty()
            && self.file().is_stub()
            && let Some(name) = self.goto_non_stub()
        {
            debug_assert!(!name.file().is_stub());
            return name.documentation();
        }
        result
    }

    pub fn class_symbols(&self) -> Option<impl ExactSizeIterator<Item = NameSymbol<'db>>> {
        match self {
            Self::TreeName(tree_name) => {
                let cls = tree_name.cst_name.name_def()?.maybe_name_of_class()?;
                let cls_storage = ClassNodeRef::new(tree_name.file, cls.index()).class_storage();
                Some(NameSymbol::symbol_iterator_from_symbol_table(
                    &tree_name.db,
                    tree_name.file,
                    Scope::Class(cls),
                    &cls_storage.class_symbol_table,
                ))
            }
            _ => None,
        }
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
        Scope::Function(_) | Scope::Lambda(_) => None,
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

    fn lsp_kind(&self) -> SymbolKind {
        let Some(name_def) = self.cst_name.name_def() else {
            return SymbolKind::OBJECT;
        };
        match name_def.expect_type() {
            TypeLike::Assignment(_) => match self.parent_scope {
                Scope::Class(_) => SymbolKind::FIELD,
                _ => SymbolKind::VARIABLE,
            },
            TypeLike::ClassDef(_) => SymbolKind::CLASS,
            TypeLike::Function(_) => match self.parent_scope {
                Scope::Class(_) => {
                    if name_def.as_code() == "__init__" {
                        SymbolKind::CONSTRUCTOR
                    } else {
                        SymbolKind::METHOD
                    }
                }
                _ => SymbolKind::FUNCTION,
            },
            TypeLike::TypeAlias(_) => SymbolKind::INTERFACE,
            TypeLike::TypeParam(_) => SymbolKind::TYPE_PARAMETER,
            TypeLike::ImportFromAsName(_)
            | TypeLike::DottedAsName(_)
            | TypeLike::ParamName(_)
            | TypeLike::Other => SymbolKind::VARIABLE,
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

fn parent_scope_to_scope(file: &PythonFile, parent_scope: ParentScope) -> Scope<'_> {
    match parent_scope {
        ParentScope::Module => Scope::Module,
        ParentScope::Function(f) => Scope::Function(FunctionDef::by_index(&file.tree, f)),
        ParentScope::Class(c) => Scope::Class(ClassDef::by_index(&file.tree, c)),
    }
}

#[derive(Debug)]
pub struct NodeName<'db, 'x> {
    db: &'db Database,
    node_ref: NodeRef<'db>,
    name: &'x str,
}

impl<'db, 'x> NodeName<'db, 'x> {
    pub(crate) fn new(db: &'db Database, node_ref: NodeRef<'db>, name: &'x str) -> Self {
        Self { db, node_ref, name }
    }
}

#[derive(Debug)]
pub struct ModuleName<'db> {
    pub(crate) db: &'db Database,
    pub(crate) file: &'db PythonFile,
}

pub struct NameSymbol<'db> {
    db: &'db Database,
    file: &'db PythonFile,
    parent_scope: Scope<'db>,
    pub symbol: &'db str,
    node_index: NodeIndex,
}

impl<'db> NameSymbol<'db> {
    pub(crate) fn symbol_iterator_from_symbol_table(
        db: &'db Database,
        file: &'db PythonFile,
        parent_scope: Scope<'db>,
        symbol_table: &'db SymbolTable,
    ) -> impl ExactSizeIterator<Item = Self> {
        symbol_table.iter().map(move |(symbol, &node_index)| Self {
            db,
            file,
            parent_scope,
            symbol,
            node_index,
        })
    }

    pub fn as_name(&self) -> Name<'db, 'static> {
        Name::TreeName(TreeName {
            db: self.db,
            file: self.file,
            parent_scope: self.parent_scope,
            cst_name: NodeRef::new(self.file, self.node_index).expect_name(),
        })
    }
}
