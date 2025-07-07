use parsa_python_cst::{CompletionNode, PrimaryOrAtom};

use crate::{
    database::Database,
    debug,
    file::{File as _, PythonFile},
    inference::GotoResolver,
    type_helpers::{Class, TypeOrClass},
};

impl<'db, C: for<'a> Fn(&dyn Completion) -> T, T> GotoResolver<'db, C> {
    pub fn complete(&self) -> Vec<T> {
        let db = self.infos.db;
        let file = self.infos.file;
        let leaf = file.tree.completion_node(self.infos.position);
        debug!(
            "Complete on position {}->{:?} on leaf {leaf:?}",
            file.file_path(db),
            self.infos.position
        );
        let mut found: Vec<(CompletionSortPriority, T)> = vec![];
        match leaf {
            CompletionNode::Attribute { base, rest: _rest } => {
                let inf = match base {
                    PrimaryOrAtom::Primary(p) => self.infos.infer_primary(p),
                    PrimaryOrAtom::Atom(a) => self.infos.infer_atom(a),
                };

                self.infos.with_i_s(|i_s| {
                    for t in inf.as_type(i_s).iter_with_unpacked_unions(db) {
                        for (_, type_or_class) in t.mro(db) {
                            match type_or_class {
                                TypeOrClass::Type(_) => (),
                                TypeOrClass::Class(c) => self.add_class_symbols(&mut found, c),
                            }
                        }
                    }
                })
            }
            CompletionNode::Global { .. } => (),
        };
        found.sort_by_key(|item| item.0);
        found.into_iter().map(|(_, item)| item).collect()
    }

    fn add_class_symbols(&self, results: &mut Vec<(CompletionSortPriority<'db>, T)>, c: Class) {
        let storage = c.node_ref.to_db_lifetime(self.infos.db).class_storage();
        for (_symbol, _node_index) in storage.class_symbol_table.iter() {
            //
        }
        for (symbol, _node_index) in storage.self_symbol_table.iter() {
            let result = (self.on_result)(&CompletionTreeName {
                db: self.infos.db,
                file: self.infos.file,
                name: symbol,
                kind: CompletionKind::Field,
            });
            results.push((CompletionSortPriority::Default(symbol), result))
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
