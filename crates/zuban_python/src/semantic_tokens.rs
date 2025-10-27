use anyhow::bail;

use lsp_types::SemanticTokenType;
use parsa_python_cst::{CodeIndex, Name as CstName};

use crate::{
    Document, InputPosition, PositionInfos,
    database::{Database, Specific},
    file::{File as _, PythonFile},
    inference_state::InferenceState,
    utils::join_with_commas,
};

impl<'project> Document<'project> {
    pub fn semantic_tokens(
        &self,
        range: Option<(InputPosition, InputPosition)>,
    ) -> anyhow::Result<impl Iterator<Item = SemanticToken<'_>>> {
        let file = self.project.db.loaded_python_file(self.file_index);
        let db = &self.project.db;
        let (start, end) = if let Some((start_input, end_input)) = range {
            let start = file.line_column_to_byte(start_input)?;
            let end = file.line_column_to_byte(end_input)?;
            if start.column_out_of_bounds {
                bail!("Start position {start_input:?} is out of scope");
            }
            if end.column_out_of_bounds {
                bail!("End position {end_input:?} is out of scope");
            }
            (start.byte, end.byte)
        } else {
            (0, u32::MAX)
        };
        let result = file.ensure_calculated_diagnostics(db);
        debug_assert!(result.is_ok());
        let i_s = InferenceState::new(db, file);
        Ok(file.tree.filter_all_names().filter_map(move |name| {
            if name.end() < start || name.start() > end {
                return None;
            }
            let mut properties = SemanticTokenProperties::default();

            let lsp_type = (|| {
                let inference = file.inference(&i_s);
                let inf = inference.check_point_cache(name.index())?;
                match inf.maybe_specific(db) {
                    Some(Specific::Function) => Some(SemanticTokenType::FUNCTION),
                    _ => None,
                }
            })()?;
            if let Some(name_def) = name.name_def() {
                properties.definition = true;
                properties.declaration = name_def.name_can_be_overwritten();
            }
            Some(SemanticToken {
                db,
                file,
                name,
                lsp_type,
                properties,
            })
        }))
    }
}

pub struct SemanticToken<'db> {
    db: &'db Database,
    file: &'db PythonFile,
    name: CstName<'db>,
    pub lsp_type: SemanticTokenType,
    pub properties: SemanticTokenProperties,
}

impl<'db> SemanticToken<'db> {
    pub fn position(&self) -> PositionInfos<'db> {
        self.file.byte_to_position_infos(self.db, self.name.start())
    }

    pub fn len(&self) -> CodeIndex {
        self.name.len()
    }

    pub fn content(&self) -> &'db str {
        self.name.as_code()
    }

    pub fn pretty_properties(&self) -> String {
        let mut pretty = vec![];
        let p = &self.properties;

        macro_rules! add {
            ($name:ident) => {
                if p.$name {
                    pretty.push(stringify!($name).trim_end_matches('_'))
                }
            };
        }
        add!(definition);
        add!(declaration);
        add!(in_stdlib);
        add!(read_only);
        add!(deprecated);
        add!(abstract_);
        add!(async_);
        add!(static_);

        if pretty.is_empty() {
            "none".into()
        } else {
            join_with_commas(pretty.into_iter())
        }
    }
}

#[derive(Default)]
pub struct SemanticTokenProperties {
    pub definition: bool,
    pub declaration: bool,
    pub in_stdlib: bool,
    pub read_only: bool,
    pub static_: bool,
    pub deprecated: bool,
    pub abstract_: bool,
    pub async_: bool,
}
