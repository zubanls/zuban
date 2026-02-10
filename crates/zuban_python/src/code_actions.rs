use parsa_python_cst::{CodeIndex, NameParent};

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
        let check_range = pos.byte..until.byte;
        for diag in file.diagnostics(db) {
            let issue_start = diag.start_position().byte_position as CodeIndex;
            let issue_end = diag.end_position().byte_position as CodeIndex;
            if !diag.is_note()
                && intersects(&check_range, &(issue_start..issue_end))
                && let Some(insertion) = file.tree.insertion_point_for_type_ignore(issue_start)
            {
                let error_code = diag.mypy_error_code();
                if error_code == "syntax" {
                    // Syntax errors cannot be ignored
                    continue;
                }
                let pos = file.byte_to_position_infos(db, insertion.insertion_index);
                let mut add = |kind| {
                    if let Some(replacement) = insertion.format_for_kind(kind, error_code) {
                        actions.push(CodeAction {
                            title: format!(r##"Add "# {kind}: ignore[{error_code}]""##),
                            start_of_change: pos,
                            end_of_change: pos,
                            replacement,
                        })
                    }
                };
                add("type");
                add("zuban");
            }
        }
        debug!(
            "Position for goto-like operation {}->{position:?}",
            file.file_path(db),
        );
        Ok(actions)
    }
}

fn intersects<T: Ord>(a: &std::ops::Range<T>, b: &std::ops::Range<T>) -> bool {
    a.start <= b.end && b.start <= a.end
}

pub struct CodeAction<'db> {
    pub title: String,
    pub start_of_change: PositionInfos<'db>,
    pub end_of_change: PositionInfos<'db>,
    pub replacement: String,
}
