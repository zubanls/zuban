use std::{borrow::Cow, collections::HashSet};

use parsa_python_cst::{ClassDef, CompletionNode, FunctionDef, NodeIndex, RestNode, Scope};
use vfs::{Directory, DirectoryEntry, Entries, FileIndex, Parent};

use crate::{
    database::{Database, ParentScope},
    debug,
    file::{ClassNodeRef, File as _, FuncNodeRef, PythonFile},
    imports::{global_import, ImportResult},
    inference::{unpack_union_types, with_i_s_non_self, PositionalDocument},
    inference_state::InferenceState,
    inferred::Inferred,
    recoverable_error,
    type_::{CallableParam, Enum, EnumMemberDefinition, Namespace, Type},
    type_helpers::{is_private, Class, TypeOrClass},
    InputPosition,
};

type CompletionInfo<'db> = (CompletionNode<'db>, RestNode<'db>);

impl<'db> PositionalDocument<'db, CompletionInfo<'db>> {
    pub fn for_completion(db: &'db Database, file: &'db PythonFile, pos: InputPosition) -> Self {
        let position = pos.to_code_index(file);
        let (scope, node, rest) = file.tree.completion_node(position);
        let result = file.ensure_calculated_diagnostics(db);
        debug!(
            "Complete on position {}->{pos:?} on leaf {node:?} with rest {:?}",
            file.file_path(&db),
            rest.as_code()
        );
        debug_assert!(result.is_ok());
        Self {
            db,
            file,
            scope,
            node: (node, rest),
        }
    }
}

pub(crate) struct CompletionResolver<'db, C, T> {
    pub infos: PositionalDocument<'db, CompletionInfo<'db>>,
    pub on_result: C,
    items: Vec<(CompletionSortPriority<'db>, T)>,
    added_names: HashSet<Cow<'db, str>>,
    should_start_with: Option<&'db str>,
}

impl<'db, C: for<'a> Fn(&dyn Completion) -> T, T> CompletionResolver<'db, C, T> {
    pub fn complete(
        db: &'db Database,
        file: &'db PythonFile,
        position: InputPosition,
        on_result: C,
    ) -> Vec<T> {
        let _panic_context = utils::panic_context::enter(format!(
            "completions for {} position {position:?}",
            file.file_path(db)
        ));
        let mut slf = Self {
            infos: PositionalDocument::for_completion(db, file, position),
            on_result,
            items: vec![],
            added_names: Default::default(),
            should_start_with: None,
        };
        slf.fill_items();
        slf.items.sort_by_key(|item| item.0);
        slf.items.into_iter().map(|(_, item)| item).collect()
    }

    fn fill_items(&mut self) {
        self.should_start_with = Some(self.infos.node.1.as_code());
        let file = self.infos.file;
        let db = self.infos.db;
        match &self.infos.node.0 {
            CompletionNode::Attribute { base } => {
                let inf = self.infos.infer_primary_or_atom(*base);
                self.add_attribute_completions(inf)
            }
            CompletionNode::Global => {
                let reachable_scopes = &mut ReachableScopesIterator {
                    file,
                    current: Some(self.infos.scope),
                };
                for scope in reachable_scopes {
                    let node_index = match scope {
                        Scope::Module => self.add_module_completions(file),
                        Scope::Class(cls) => {
                            let storage = ClassNodeRef::new(file, cls.index()).class_storage();
                            for (symbol, _node_index) in storage.class_symbol_table.iter() {
                                self.maybe_add_tree_name(symbol)
                            }
                            self.add_star_imports_completions(
                                file,
                                cls.index(),
                                &mut Default::default(),
                            )
                        }
                        Scope::Function(func) => {
                            func.on_name_def_in_scope(&mut |name_def| {
                                self.maybe_add_tree_name(name_def.as_code())
                            });
                            self.add_star_imports_completions(
                                file,
                                func.index(),
                                &mut Default::default(),
                            )
                        }
                        Scope::Lambda(lambda) => {
                            // TODO lambda
                        }
                    };
                }
                self.add_module_completions(db.python_state.builtins())
            }
            CompletionNode::ImportName { path: None } => self.add_global_import_completions(),
            CompletionNode::ImportName {
                path: Some((name_def, rest_path)),
            } => {
                let mut result = global_import(db, file, name_def.as_code());
                if let Some(dotted) = rest_path {
                    self.infos.with_i_s(|i_s| {
                        result = file
                            .inference(i_s)
                            .cache_import_dotted_name(*dotted, result.take())
                    });
                }
                self.add_import_result_completions(result)
            }
            CompletionNode::ImportFromFirstPart { dots: _, base } => {
                // TODO use dots
                if let Some(base) = base {
                    self.add_import_result_completions(self.infos.with_i_s(|i_s| {
                        self.infos
                            .file
                            .inference(i_s)
                            .cache_import_dotted_name(*base, None)
                    }))
                } else {
                    self.add_global_import_completions()
                }
            }
            CompletionNode::ImportFromTarget { base, dots } => {
                let inf = self.infos.infer_dotted_import_name(*dots, *base);
                self.add_attribute_completions(inf)
            }
            CompletionNode::AsNewName => (),
            CompletionNode::NecessaryKeyword(keyword) => {
                let keyword = *keyword;
                let result = (self.on_result)(&KeywordCompletion { keyword });
                self.items
                    .push((CompletionSortPriority::Default(keyword), result))
            }
            CompletionNode::AfterDefKeyword => (),
            CompletionNode::AfterClassKeyword => (),
        }
    }

    fn add_import_result_completions(&mut self, import_result: Option<ImportResult>) {
        match import_result {
            Some(ImportResult::File(file_index)) => {
                let file = self.infos.db.loaded_python_file(file_index);
                self.add_submodule_completions(file)
            }
            Some(ImportResult::Namespace(namespace)) => self.add_namespace_completions(&namespace),
            None | Some(ImportResult::PyTypedMissing) => (),
        }
    }

    fn add_module_completions(&mut self, file: &'db PythonFile) {
        self.add_specific_module_completions(file, &mut HashSet::default());
        self.add_submodule_completions(file)
    }

    fn add_namespace_completions(&mut self, namespace: &Namespace) {
        for dir in namespace.directories.iter() {
            self.directory_entries_completions(Directory::entries(
                &*self.infos.db.vfs.handler,
                &dir,
            ))
        }
    }

    fn add_module_type_completions(&mut self) {
        // Theoretically all object dunder methods are also importable, but I think
        // they offer no real value
        self.add_class_symbols_with_check(
            self.infos.db.python_state.module_instance().class,
            false,
            |name| ["__init__", "__getattr__", "__path__"].contains(&name),
        );
    }

    fn add_specific_module_completions(
        &mut self,
        file: &'db PythonFile,
        already_visited: &mut HashSet<FileIndex>,
    ) {
        let db = self.infos.db;
        for (symbol, _node_index) in file.symbol_table.iter() {
            self.maybe_add_tree_name(symbol)
        }
        if !file.star_imports.is_empty() {
            if !already_visited.insert(file.file_index) {
                // Avoid recursing
                return;
            };
            self.add_star_imports_completions(file, 0, already_visited)
        }
    }

    fn add_star_imports_completions(
        &mut self,
        file: &PythonFile,
        scope: NodeIndex,
        already_visited: &mut HashSet<FileIndex>,
    ) {
        for star_import in file.star_imports.iter() {
            if star_import.scope == scope {
                if let Some(f) = file
                    .name_resolution_for_inference(&InferenceState::new(self.infos.db, file))
                    .star_import_file(star_import)
                {
                    self.add_specific_module_completions(f, already_visited)
                }
            }
        }
    }

    fn add_global_import_completions(&mut self) {
        for workspace in self.infos.db.vfs.workspaces.iter() {
            self.directory_entries_completions(&workspace.entries)
        }
    }

    fn add_submodule_completions(&mut self, file: &'db PythonFile) {
        let db = self.infos.db;
        let (file_entry, is_package) = file.file_entry_and_is_package(db);
        if is_package {
            if let Parent::Directory(dir) = &file_entry.parent {
                let dir = dir.upgrade().unwrap();
                self.directory_entries_completions(Directory::entries(&*db.vfs.handler, &dir))
            }
        }
    }

    fn directory_entries_completions(&mut self, entries: &Entries) {
        for entry in &entries.iter() {
            let name: &str = match entry {
                DirectoryEntry::File(f) => {
                    if let Some(stripped_name) = f
                        .name
                        .strip_suffix(".py")
                        .or_else(|| f.name.strip_suffix(".pyi"))
                    {
                        if stripped_name == "__init__" {
                            continue;
                        }
                        stripped_name
                    } else {
                        continue;
                    }
                }
                DirectoryEntry::Directory(dir) => &dir.name,
                DirectoryEntry::MissingEntry(_) => continue,
            };
            // Unsafe: The name always lives as long as 'db, because file entries are
            // only cleaned up once this lifetime is released.
            let name: &'db str = unsafe { std::mem::transmute(name) };
            if !self.maybe_add(name) {
                continue;
            }
            let result = (self.on_result)(&CompletionDirEntry {
                db: self.infos.db,
                name,
                entry,
            });
            self.items
                .push((CompletionSortPriority::new_symbol(name), result))
        }
    }

    fn add_attribute_completions(&mut self, inf: Inferred) {
        let db = self.infos.db;
        let file = self.infos.file;
        with_i_s_non_self(db, file, self.infos.scope, |i_s| {
            self.add_attribute_completions_for_type(i_s, &inf.as_cow_type(i_s))
        })
    }

    fn add_attribute_completions_for_type(&mut self, i_s: &InferenceState, t: &Type) {
        let db = self.infos.db;
        for t in unpack_union_types(db, Cow::Borrowed(t)).iter_with_unpacked_unions(db) {
            match t {
                Type::Type(t) => self.add_for_mro(i_s, t, false),
                Type::Module(module) => {
                    self.add_module_completions(self.infos.db.loaded_python_file(*module));
                    self.add_module_type_completions()
                }
                Type::Namespace(ns) => {
                    self.add_namespace_completions(ns);
                    self.add_module_type_completions()
                }
                Type::Intersection(intersection) => {
                    for t in intersection.iter_entries() {
                        self.add_attribute_completions_for_type(i_s, t)
                    }
                }
                Type::RecursiveType(rec) => {
                    self.add_attribute_completions_for_type(i_s, rec.calculated_type(db))
                }
                t => self.add_for_mro(i_s, t, true),
            }
        }
    }

    fn add_for_mro(&mut self, i_s: &InferenceState, t: &Type, is_instance: bool) {
        if let Type::Self_ = t {
            if let Some(cls) = i_s.current_class() {
                self.add_for_mro(i_s, &cls.as_type(i_s.db), is_instance)
            } else {
                recoverable_error!("TODO caught Self that is not within a class");
            }
        }
        if let Type::Any(_) = t {
            // I decided to not return any completions here to signal the user a difference between
            // object and Any. This essentially removes all the dunder methods that are present on
            // object.
            return;
        }

        for (_, type_or_class) in t.mro(self.infos.db) {
            self.add_for_type_or_class(type_or_class, is_instance)
        }
    }

    fn add_for_type_or_class(&mut self, type_or_class: TypeOrClass, is_instance: bool) {
        let db = self.infos.db;
        match type_or_class {
            TypeOrClass::Type(t) => match t.as_ref() {
                Type::Super {
                    class,
                    mro_index: _,
                    ..
                } => {
                    // TODO this is not fully correct, because some base classes might have been
                    // skipped with the mro_index
                    for base in class.class(db).bases(db) {
                        self.add_for_type_or_class(base, is_instance)
                    }
                }
                Type::Dataclass(dataclass) => {
                    self.add_class_symbols(dataclass.class(db), is_instance)
                }
                Type::Enum(enum_) => self.add_enum_completions(enum_, is_instance),
                Type::EnumMember(member) => self.add_enum_completions(&member.enum_, is_instance),
                // TypedDicts have no relevant completions, the base class takes care of it
                Type::TypedDict(_) => (),
                Type::NamedTuple(nt) => {
                    for param in nt.params() {
                        let comp = NamedTupleMemberCompletion {
                            db,
                            param,
                            file: nt.__new__.defined_at.file,
                        };
                        if !self.maybe_add_cow(Cow::Owned(comp.label().into())) {
                            continue;
                        }
                        let result = (self.on_result)(&comp);
                        // TODO fix this name for sorting
                        self.items
                            .push((CompletionSortPriority::Default(""), result))
                    }
                    let tup_cls = db.python_state.tuple_class_with_generics_to_be_defined();
                    self.add_class_symbols(tup_cls, is_instance)
                }
                _ => {
                    debug!("TODO ignored completions for type {t:?}");
                }
            },
            TypeOrClass::Class(c) => self.add_class_symbols(c, is_instance),
        }
    }

    fn add_class_symbols(&mut self, c: Class, is_instance: bool) {
        self.add_class_symbols_with_check(c, is_instance, |_| false)
    }

    fn add_class_symbols_with_check(
        &mut self,
        c: Class,
        is_instance: bool,
        should_ignore: impl Fn(&str) -> bool,
    ) {
        let storage = c.node_ref.to_db_lifetime(self.infos.db).class_storage();
        for (symbol, _node_index) in storage.class_symbol_table.iter() {
            if !self.maybe_add(symbol) || is_private(symbol) || should_ignore(symbol) {
                continue;
            }
            let result = (self.on_result)(&CompletionTreeName {
                db: self.infos.db,
                file: self.infos.file,
                name: symbol,
                kind: CompletionKind::Field,
            });
            self.items
                .push((CompletionSortPriority::new_symbol(symbol), result))
        }
        if is_instance {
            for (symbol, _node_index) in storage.self_symbol_table.iter() {
                if !self.maybe_add(symbol) || is_private(symbol) || should_ignore(symbol) {
                    continue;
                }
                let result = (self.on_result)(&CompletionTreeName {
                    db: self.infos.db,
                    file: self.infos.file,
                    name: symbol,
                    kind: CompletionKind::Field,
                });
                self.items
                    .push((CompletionSortPriority::new_symbol(symbol), result))
            }
        }
    }

    fn add_enum_completions(&mut self, enum_: &Enum, is_instance: bool) {
        for member in &enum_.members {
            if !self.maybe_add_cow(Cow::Owned(member.name(self.infos.db).into())) {
                continue;
            }
            let result = (self.on_result)(&EnumMemberCompletion {
                db: self.infos.db,
                enum_: &enum_,
                member,
            });
            self.items
                .push((CompletionSortPriority::EnumMember, result))
        }
        if !enum_.from_functional_definition(self.infos.db) {
            self.add_class_symbols(enum_.class(self.infos.db), is_instance)
        }
    }

    fn maybe_add(&mut self, symbol: &'db str) -> bool {
        self.maybe_add_cow(Cow::Borrowed(symbol))
    }

    fn maybe_add_cow(&mut self, symbol: Cow<'db, str>) -> bool {
        if let Some(starts_with) = self.should_start_with {
            if !symbol.starts_with(starts_with) {
                return false;
            }
        }
        self.added_names.insert(symbol)
    }

    fn maybe_add_tree_name(&mut self, symbol: &'db str) {
        if !self.maybe_add(symbol) {
            return;
        }
        let result = (self.on_result)(&CompletionTreeName {
            db: self.infos.db,
            file: self.infos.file,
            name: symbol,
            kind: CompletionKind::Variable,
        });
        self.items
            .push((CompletionSortPriority::new_symbol(symbol), result))
    }
}

pub struct ReachableScopesIterator<'db> {
    file: &'db PythonFile,
    current: Option<Scope<'db>>,
}

impl<'db> Iterator for ReachableScopesIterator<'db> {
    type Item = Scope<'db>;

    fn next(&mut self) -> Option<Self::Item> {
        let result = self.current.take()?;
        let mut parent_scope = |scope| match scope {
            Scope::Module => Ok(()),
            Scope::Class(c) => Err(ClassNodeRef::new(self.file, c.index())
                .class_storage()
                .parent_scope),
            Scope::Function(f) => Err(FuncNodeRef::new(self.file, f.index()).parent_scope()),
            Scope::Lambda(l) => {
                self.current = Some(l.parent_scope());
                Ok(())
            }
        };
        let mut check = result;
        loop {
            match parent_scope(check) {
                // Case was already handled
                Ok(()) => {
                    return Some(result);
                }
                Err(ParentScope::Module) => {
                    self.current = Some(Scope::Module);
                    return Some(result);
                }
                Err(ParentScope::Function(f)) => {
                    self.current = Some(Scope::Function(FunctionDef::by_index(&self.file.tree, f)));
                    return Some(result);
                }
                Err(ParentScope::Class(c)) => {
                    // Parent classes are not reachable for name lookups and therefore need to be
                    // skipped
                    check = Scope::Class(ClassDef::by_index(&self.file.tree, c));
                }
            }
        }
    }
}

pub trait Completion {
    fn label(&self) -> &str;
    fn kind(&self) -> CompletionKind;
    fn file_path(&self) -> Option<&str>;
    fn deprecated(&self) -> bool {
        false
    }
    fn documentation(&self) -> Option<&str> {
        None
    }
}

struct CompletionTreeName<'db> {
    db: &'db Database,
    file: &'db PythonFile,
    name: &'db str,
    kind: CompletionKind,
}

impl<'db> Completion for CompletionTreeName<'db> {
    fn label(&self) -> &str {
        self.name
    }

    fn kind(&self) -> CompletionKind {
        self.kind
    }

    fn file_path(&self) -> Option<&str> {
        Some(self.file.file_path(self.db))
    }
}

#[expect(dead_code)]
struct CompletionDirEntry<'db, 'x> {
    db: &'db Database,
    name: &'db str,
    entry: &'x DirectoryEntry,
}

impl Completion for CompletionDirEntry<'_, '_> {
    fn label(&self) -> &str {
        self.name
    }

    fn kind(&self) -> CompletionKind {
        CompletionKind::Module
    }

    fn file_path(&self) -> Option<&str> {
        // TODO
        /*
        match &self.entry {
            DirectoryEntry::File(file_entry) => file_entry.absolute_path(),
            DirectoryEntry::Directory(_) => ...,
            DirectoryEntry::MissingEntry(missing_entry) => unreachable!(),
        }
        */
        None
    }
}

struct KeywordCompletion {
    keyword: &'static str,
}

impl Completion for KeywordCompletion {
    fn label(&self) -> &str {
        self.keyword
    }

    fn kind(&self) -> CompletionKind {
        CompletionKind::Keyword
    }

    fn file_path(&self) -> Option<&str> {
        None
    }
}

struct EnumMemberCompletion<'db> {
    db: &'db Database,
    enum_: &'db Enum,
    member: &'db EnumMemberDefinition,
}

impl Completion for EnumMemberCompletion<'_> {
    fn label(&self) -> &str {
        self.member.name(self.db)
    }

    fn kind(&self) -> CompletionKind {
        CompletionKind::EnumMember
    }

    fn file_path(&self) -> Option<&str> {
        Some(&self.db.file_path(self.enum_.defined_at.file))
    }
}

struct NamedTupleMemberCompletion<'db> {
    db: &'db Database,
    file: FileIndex,
    param: &'db CallableParam,
}

impl Completion for NamedTupleMemberCompletion<'_> {
    fn label(&self) -> &str {
        self.param.name.as_ref().unwrap().as_str(self.db)
    }

    fn kind(&self) -> CompletionKind {
        CompletionKind::Field
    }

    fn file_path(&self) -> Option<&str> {
        Some(&self.db.file_path(self.file))
    }
}

#[derive(Ord, PartialOrd, Eq, PartialEq, Copy, Clone)]
enum CompletionSortPriority<'db> {
    //Literal,    // e.g. TypedDict literal
    //NamedParam, // e.g. def foo(*, bar) => `foo(b` completes to bar=
    EnumMember,
    Default(&'db str),
    Dunder(&'db str), // e.g. __eq__
}

impl<'db> CompletionSortPriority<'db> {
    fn new_symbol(symbol: &'db str) -> Self {
        if symbol.starts_with("__") && symbol.ends_with("__") {
            Self::Dunder(symbol)
        } else {
            Self::Default(symbol)
        }
    }
}

/// Copied from LSP
#[derive(Copy, Clone)]
pub enum CompletionKind {
    Text = 1,
    Method = 2,
    Function = 3,
    Constructor = 4,
    Field = 5,
    Variable = 6,
    Class = 7,
    Interface = 8,
    Module = 9,
    Property = 10,
    Unit = 11,
    Value = 12,
    Enum = 13,
    Keyword = 14,
    Snippet = 15,
    Color = 16,
    File = 17,
    Reference = 18,
    Folder = 19,
    EnumMember = 20,
    Constant = 21,
    Struct = 22,
    Event = 23,
    Operator = 24,
    TypeParameter = 25,
}
