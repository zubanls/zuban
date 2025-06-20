/*
 * Inference is a module for completions, goto, etc. This needs additional inference and not just
 * standard type checking. Type checking should always be done first.
 * */

use parsa_python_cst::{CodeIndex, NameOrKeywordLookup};

use crate::{
    database::Database,
    debug,
    file::{File, PythonFile},
    inference_state::InferenceState,
    inferred::Inferred,
    name::{Name, Names, TreeName},
    type_::Type,
    InputPosition,
};

pub(crate) struct PositionalDocument<'db> {
    db: &'db Database,
    file: &'db PythonFile,
    position: CodeIndex,
}

impl<'db> PositionalDocument<'db> {
    pub fn new(db: &'db Database, file: &'db PythonFile, position: InputPosition) -> Self {
        let position = match position {
            InputPosition::NthByte(pos) => pos as u32,
            InputPosition::Utf8Bytes { line, column } => file.line_column_to_byte(line, column),
            InputPosition::Utf16CodeUnits { line: _, column: _ } => todo!(),
            InputPosition::CodePoints { line: _, column: _ } => todo!(),
        };
        Self { db, file, position }
    }

    fn infer_position(&self) -> Option<Inferred> {
        let result = self.file.ensure_calculated_diagnostics(&self.db);
        debug_assert!(result.is_ok());
        let leaf = NameOrKeywordLookup::from_position(&self.file.tree, self.position);
        debug!(
            "Infer for position {}->{:?} on leaf {leaf:?}",
            self.file.file_path(&self.db),
            self.position
        );
        match leaf {
            NameOrKeywordLookup::Name(name) => {
                Some(TreeName::new(self.db, self.file, name).infer())
            }
            NameOrKeywordLookup::Keyword(_) => None,
            NameOrKeywordLookup::None => None,
        }
    }

    /*
    fn infer_operator_leaf(&self, _db: &Database, _leaf: Keyword) -> Inferred {
        /*
        if ["(", "[", "{", ")", "]", "}"]
            .iter()
            .any(|&x| x == leaf.as_str())
        {
            if let Some(primary) = leaf.maybe_primary_parent() {
                let i_s = InferenceState::new(db);
                return self
                    .inference(&i_s)
                    .infer_primary(primary, &mut ResultContext::Unknown);
            }
        }
        */
        unimplemented!()
    }

    pub fn infer_definition(&self) -> impl Iterator<Item = T> {
        /*
        let i_s = InferenceState::new(self.db);
        self.file
            .inference(&i_s)
            .infer_name_of_definition(self.cst_name);
        */
        match NameOrKeywordLookup::from_position(&self.file.tree, self.position) {
            NameOrKeywordLookup::Name(name) => TreeName::new(self.db, self.file, name).infer(),
            NameOrKeywordLookup::Keyword(_) => return vec![],
            NameOrKeywordLookup::None => return vec![],
        }
    }
    */

    pub fn complete(&self) -> Names<'db> {
        unimplemented!()
    }
}

pub(crate) struct GotoResolver<'db, C> {
    infos: PositionalDocument<'db>,
    on_result: C,
}

impl<'db, C: for<'a> Fn(&dyn Name<'a>) -> T + Copy + 'db, T> GotoResolver<'db, C> {
    pub(crate) fn new(infos: PositionalDocument<'db>, on_result: C) -> Self {
        Self { infos, on_result }
    }

    pub fn goto(&self, follow_imports: bool) -> impl Iterator<Item = T> {
        let callback = self.on_result;
        std::iter::empty().map(move |n| callback(n))
    }

    pub fn infer_type_definition(&self) -> impl Iterator<Item = T> + 'db {
        let inf = self.infos.infer_position();
        let callback = self.on_result;
        let file = self.infos.file;
        let db = self.infos.db;
        inf.map(|t| {
            t.as_type(&InferenceState::new(db, file))
                .into_iter_with_unpacked_unions(db, true)
        })
        .into_iter()
        .flatten()
        .filter_map(move |e| Some(callback(&type_to_name(db, file, &e.type_)?)))
    }

    pub fn infer_implementation(&self) -> impl Iterator<Item = T> + 'db {
        // TODO should goto stub
        self.infer_type_definition()
    }
}

fn type_to_name<'db>(db: &'db Database, file: &'db PythonFile, t: &Type) -> Option<TreeName<'db>> {
    let n = match t {
        Type::Class(c) => c.node_ref(db).node().name(),
        Type::None => todo!(),
        Type::Tuple(tup) => tup.class(db).node_ref.to_db_lifetime(db).node().name(),
        Type::Any(_) => return None,
        _ => unimplemented!("{t:?}"),
    };
    Some(TreeName::new(db, file, n))
}
