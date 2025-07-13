use std::collections::HashSet;

use parsa_python_cst::{CompletionNode, RestNode};

use crate::{
    database::Database,
    debug,
    file::{File as _, PythonFile},
    imports::ImportResult,
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
        debug!(
            "Complete on position {}->{pos:?} on leaf {node:?}",
            file.file_path(&db),
        );
        let result = file.ensure_calculated_diagnostics(db);
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
            CompletionNode::ImportName { path } => todo!(),
            CompletionNode::DottedImportName { base } => {
                if let Some(import_result) = self.infos.with_i_s(|i_s| {
                    self.infos
                        .file
                        .inference(i_s)
                        .cache_import_dotted_name(*base, None)
                }) {
                    match import_result {
                        ImportResult::File(file_index) => {}
                        ImportResult::Namespace(rc) => todo!(),
                        ImportResult::PyTypedMissing => (),
                    }
                }
            }
            CompletionNode::ImportFromTarget { base } => {
                let inf = self.infos.infer_dotted_import_name(*base);
                self.add_attribute_completions(inf)
            }
        }
    }

    fn add_module_completions(&mut self, file: &'db PythonFile) {
        for (symbol, _node_index) in file.symbol_table.iter() {
            if !self.maybe_add(symbol) {
                continue;
            }
            let result = (self.on_result)(&CompletionTreeName {
                db: self.infos.db,
                file: self.infos.file,
                name: symbol,
                kind: CompletionKind::Variable,
            });
            self.items
                .push((CompletionSortPriority::Default(symbol), result))
        }
    }

    fn add_attribute_completions(&mut self, inf: Inferred) {
        let db = self.infos.db;
        let file = self.infos.file;
        with_i_s_non_self(db, file, self.infos.scope, |i_s| {
            for t in unpack_union_types(db, inf.as_cow_type(i_s)).iter_with_unpacked_unions(db) {
                match t {
                    Type::Type(t) => self.add_for_mro(i_s, t, false),
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
                Type::Module(module) => {
                    self.add_module_completions(self.infos.db.loaded_python_file(*module))
                }
                _ => {
                    debug!("TODO ignored completions for type {t:?}");
                }
            },
            TypeOrClass::Class(c) => self.add_class_symbols(c, is_instance),
        }
    }

    fn add_class_symbols(&mut self, c: Class, is_instance: bool) {
        let storage = c.node_ref.to_db_lifetime(self.infos.db).class_storage();
        for (symbol, _node_index) in storage.class_symbol_table.iter() {
            if !self.maybe_add(symbol) || is_private(symbol) {
                continue;
            }
            let result = (self.on_result)(&CompletionTreeName {
                db: self.infos.db,
                file: self.infos.file,
                name: symbol,
                kind: CompletionKind::Field,
            });
            self.items
                .push((CompletionSortPriority::Default(symbol), result))
        }
        if is_instance {
            for (symbol, _node_index) in storage.self_symbol_table.iter() {
                if !self.maybe_add(symbol) || is_private(symbol) {
                    continue;
                }
                let result = (self.on_result)(&CompletionTreeName {
                    db: self.infos.db,
                    file: self.infos.file,
                    name: symbol,
                    kind: CompletionKind::Field,
                });
                self.items
                    .push((CompletionSortPriority::Default(symbol), result))
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

#[derive(Ord, PartialOrd, Eq, PartialEq, Copy, Clone)]
enum CompletionSortPriority<'db> {
    //Literal,    // e.g. TypedDict literal
    //NamedParam, // e.g. def foo(*, bar) => `foo(b` completes to bar=
    //EnumMember(&'db str),
    Default(&'db str),
    //Dunder, // e.g. __eq__
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
