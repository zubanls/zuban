use crate::{Document, InputPosition, PositionInfos, debug, file::File as _};

impl<'project> Document<'project> {
    pub fn selection_ranges(
        &self,
        position: InputPosition,
    ) -> anyhow::Result<impl Iterator<Item = (PositionInfos<'project>, PositionInfos<'project>)>>
    {
        let db = &self.project.db;
        let file = db.loaded_python_file(self.file_index);
        let pos = file.line_column_to_byte(position)?;
        let ranges = file.tree.selection_ranges(pos.byte);
        debug!(
            "Position for selection ranges {}->{position:?}",
            file.file_path(db),
        );
        Ok(ranges.map(|range| {
            (
                file.byte_to_position_infos(db, range.start),
                file.byte_to_position_infos(db, range.end),
            )
        }))
    }
}
