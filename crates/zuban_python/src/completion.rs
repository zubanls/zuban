use std::collections::HashSet;

use parsa_python_cst::{CompletionNode, RestNode};
use vfs::{Directory, DirectoryEntry, Entries, FileIndex, Parent};

use crate::{
    database::Database,
    debug,
    file::{File as _, PythonFile},
    imports::{global_import, ImportResult},
    inference::{unpack_union_types, with_i_s_non_self, PositionalDocument},
    inference_state::InferenceState,
    inferred::Inferred,
    recoverable_error,
    type_::Type,
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
    added_names: HashSet<&'db str>,
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
        match &self.infos.node.0 {
            CompletionNode::Attribute { base } => {
                let inf = self.infos.infer_primary_or_atom(*base);
                self.add_attribute_completions(inf)
            }
            CompletionNode::Global => {
                self.add_module_completions(self.infos.file);
                self.add_module_completions(self.infos.db.python_state.builtins());
            }
            CompletionNode::ImportName { path: None } => self.add_global_completions(),
            CompletionNode::ImportName {
                path: Some((name_def, rest_path)),
            } => {
                if rest_path.is_some() {
                    todo!()
                }
                let mut result = global_import(self.infos.db, self.infos.file, name_def.as_code());
                if let Some(rest_path) = rest_path {
                    self.infos.with_i_s(|i_s| {
                        //
                    });
                }
                self.add_import_result_completions(result)
            }
            CompletionNode::ImportFromFirstPart { dots, base } => {
                if let Some(base) = base {
                    self.add_import_result_completions(self.infos.with_i_s(|i_s| {
                        self.infos
                            .file
                            .inference(i_s)
                            .cache_import_dotted_name(*base, None)
                    }))
                } else {
                    self.add_global_completions()
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
            Some(ImportResult::Namespace(rc)) => {
                //  TODO namespace completions
            }
            None | Some(ImportResult::PyTypedMissing) => (),
        }
    }

    fn add_module_completions(&mut self, file: &'db PythonFile) {
        self.add_specific_module_completions(file, &mut HashSet::default());
        self.add_submodule_completions(file)
    }

    fn add_specific_module_completions(
        &mut self,
        file: &'db PythonFile,
        already_visited: &mut HashSet<FileIndex>,
    ) {
        let db = self.infos.db;
        for (symbol, _node_index) in file.symbol_table.iter() {
            if !self.maybe_add(symbol) {
                continue;
            }
            let result = (self.on_result)(&CompletionTreeName {
                db,
                file,
                name: symbol,
                kind: CompletionKind::Variable,
            });
            self.items
                .push((CompletionSortPriority::new_symbol(symbol), result))
        }
        if !file.star_imports.is_empty() {
            if !already_visited.insert(file.file_index) {
                // Avoid recursing
                return;
            };
            for star_import in file.star_imports.iter() {
                if star_import.in_module_scope() {
                    if let Some(f) = file
                        .name_resolution_for_inference(&InferenceState::new(db, file))
                        .star_import_file(star_import)
                    {
                        self.add_specific_module_completions(f, already_visited)
                    }
                }
            }
        }
    }

    fn add_global_completions(&mut self) {
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
            for t in unpack_union_types(db, inf.as_cow_type(i_s)).iter_with_unpacked_unions(db) {
                match t {
                    Type::Type(t) => self.add_for_mro(i_s, t, false),
                    Type::Module(module) => {
                        self.add_module_completions(self.infos.db.loaded_python_file(*module));
                        // Theoretically all object dunder methods are also importable, but I think
                        // they offer no real value
                        self.add_class_symbols_with_check(
                            i_s.db.python_state.module_instance().class,
                            false,
                            |name| ["__init__", "__getattr__", "__path__"].contains(&name),
                        );
                    }
                    t => self.add_for_mro(i_s, t, true),
                }
            }
        })
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
        match type_or_class {
            TypeOrClass::Type(t) => match t.as_ref() {
                Type::Super {
                    class,
                    mro_index: _,
                    ..
                } => {
                    // TODO this is not fully correct, because some base classes might have been
                    // skipped with the mro_index
                    for base in class.class(self.infos.db).bases(self.infos.db) {
                        self.add_for_type_or_class(base, is_instance)
                    }
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

    fn maybe_add(&mut self, symbol: &'db str) -> bool {
        if let Some(starts_with) = self.should_start_with {
            if !symbol.starts_with(starts_with) {
                return false;
            }
        }
        self.added_names.insert(symbol)
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
            DirectoryEntry::Directory(_) => todo!(),
            DirectoryEntry::MissingEntry(missing_entry) => unreachable!(),
        }
        */
        None
    }
}

struct KeywordCompletion {
    keyword: &'static str,
}

impl<'db> Completion for KeywordCompletion {
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

#[derive(Ord, PartialOrd, Eq, PartialEq, Copy, Clone)]
enum CompletionSortPriority<'db> {
    //Literal,    // e.g. TypedDict literal
    //NamedParam, // e.g. def foo(*, bar) => `foo(b` completes to bar=
    //EnumMember(&'db str),
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
