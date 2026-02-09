use parsa_python_cst::NameParent;

use crate::{
    Document, InputPosition, PositionInfos,
    auto_imports::{ImportFinder, create_import_code_action},
    database::Specific,
    debug,
    file::File as _,
    node_ref::NodeRef,
};

impl<'project> Document<'project> {
    pub fn code_actions(
        &self,
        position: InputPosition,
        until: Option<InputPosition>,
    ) -> anyhow::Result<Vec<CodeAction<'_>>> {
        let db = &self.project.db;
        let file = db.loaded_python_file(self.file_index);
        let result = file.ensure_calculated_diagnostics(db);
        debug_assert!(result.is_ok());
        let pos = file.line_column_to_byte(position)?;
        let until = if let Some(until) = until {
            file.line_column_to_byte(until)?
        } else {
            pos
        };
        let mut actions: Vec<CodeAction> = vec![];
        for name in file.tree.filter_all_names(Some(pos.byte)) {
            if name.start() > until.byte {
                break;
            }
            let node_ref = NodeRef::new(file, name.index());
            if node_ref.point().maybe_calculated_and_specific() == Some(Specific::AnyDueToError)
                && matches!(name.parent(), NameParent::Atom { .. })
            {
                let name_str = name.as_code();
                for potential in ImportFinder::find_importable_name(db, name_str) {
                    let title = potential.title(db, name_str);
                    debug!("New potential auto import: {title}");
                    // It's probably very rare, but we never want duplicate titles
                    if !actions.iter().any(|action| action.title == title) {
                        actions.push(create_import_code_action(db, file, potential, title, name))
                    }
                }
            }
        }
        debug!(
            "Position for goto-like operation {}->{position:?}",
            file.file_path(db),
        );
        Ok(actions)
    }
}

pub struct CodeAction<'db> {
    pub title: String,
    pub start_of_change: PositionInfos<'db>,
    pub end_of_change: PositionInfos<'db>,
    pub replacement: String,
}
