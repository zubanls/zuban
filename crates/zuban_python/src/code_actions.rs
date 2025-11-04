use crate::{Document, InputPosition, PositionInfos, debug, file::File as _};

impl<'project> Document<'project> {
    pub fn code_actions(
        &self,
        position: InputPosition,
        until: Option<InputPosition>,
    ) -> anyhow::Result<Vec<CodeAction>> {
        let db = &self.project.db;
        let file = db.loaded_python_file(self.file_index);
        let pos = file.line_column_to_byte(position)?;
        let until = if let Some(until) = until {
            file.line_column_to_byte(until)?
        } else {
            pos
        };
        for name in file.tree.filter_all_names(Some(pos.byte)) {
            // if name.start() > until
        }
        debug!(
            "Position for goto-like operation {}->{position:?}",
            file.file_path(db),
        );
        Ok(vec![])
    }
}

pub struct CodeAction<'code> {
    pub title: String,
    pub start_of_change: PositionInfos<'code>,
    pub end_of_change: PositionInfos<'code>,
    pub replacement: String,
}
