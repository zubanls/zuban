use std::sync::{Arc, Mutex};

use parsa_python_cst::{Name, NameParent};
use rayon::prelude::*;
use vfs::{Directory, DirectoryEntry, Entries, FileEntry};

use crate::{
    Document, InputPosition, PositionInfos,
    database::{Database, Specific},
    debug,
    file::{File as _, PythonFile},
    imports::ImportResult,
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

struct ImportFinder<'db> {
    db: &'db Database,
    name: &'db str,
    found: Mutex<Vec<PotentialImport<'db>>>,
}

struct PotentialImport<'db> {
    file: &'db PythonFile,
    needs_additional_name: bool,
}

impl PotentialImport<'_> {
    fn title(&self, db: &Database, name: &str) -> String {
        let (dot, rest) = if self.needs_additional_name {
            (".", name)
        } else {
            ("", "")
        };
        format!("Import `{}{dot}{rest}`", self.file.qualified_name(db))
    }
}

impl<'db> ImportFinder<'db> {
    fn find_importable_name(db: &'db Database, name: &'db str) -> Vec<PotentialImport<'db>> {
        let slf = ImportFinder {
            db,
            name,
            found: Default::default(),
        };
        for workspace in db.vfs.workspaces.iter() {
            if !workspace.is_type_checked() {
                // TODO support this
                continue;
            }
            slf.find_importable_name_in_entries(&workspace.entries)
        }
        slf.found.into_inner().unwrap()
    }

    fn find_importable_name_in_entries(&self, entries: &Entries) {
        if let Some(entry) = entries
            .search("__init__.pyi")
            .or_else(|| entries.search("__init__.py"))
        {
            if let DirectoryEntry::File(__init__) = &*entry
                && self.find_importable_name_in_file_entry(__init__)
            {
                // If we find a name in __init__.py, we should probably not be looking up the other
                // imports.
                return;
            }
        }
        entries.borrow().par_iter().for_each(|entry| match entry {
            DirectoryEntry::File(entry) => {
                self.find_importable_name_in_file_entry(entry);
            }
            DirectoryEntry::MissingEntry(_) => (),
            DirectoryEntry::Directory(dir) => {
                self.find_importable_name_in_entries(Directory::entries(&*self.db.vfs.handler, dir))
            }
        })
    }

    fn find_importable_name_in_file_entry(&self, entry: &Arc<FileEntry>) -> bool {
        let Some(file_index) = self.db.load_file_from_workspace(entry, false) else {
            return false;
        };
        let file = self.db.loaded_python_file(file_index);
        if file.name(self.db) == self.name {
            self.found.lock().unwrap().push(PotentialImport {
                file,
                needs_additional_name: false,
            })
        }
        let has_symbol = file.lookup_symbol(self.name).is_some();
        if has_symbol {
            self.found.lock().unwrap().push(PotentialImport {
                file,
                needs_additional_name: true,
            })
        }
        has_symbol
    }
}

fn create_import_code_action<'db>(
    db: &'db Database,
    from_file: &'db PythonFile,
    potential: PotentialImport,
    title: String,
    name: Name,
) -> CodeAction<'db> {
    if potential.needs_additional_name {
        // Try to find an import that matches
        for imp in &from_file.all_imports {
            if imp.in_global_scope && imp.node_index < name.index() {
                if let Some(imp) = NodeRef::new(from_file, imp.node_index).maybe_import_from() {
                    if matches!(
                        from_file.import_from_first_part_without_loading_file(db, imp),
                        Some(ImportResult::File(i)) if i == potential.file.file_index
                    ) {
                        let pos = from_file.byte_to_position_infos(db, imp.end());
                        return CodeAction {
                            title,
                            start_of_change: pos,
                            end_of_change: pos,
                            replacement: format!(", {}", name.as_code()),
                        };
                    }
                }
            }
        }
    }

    let pos = from_file.byte_to_position_infos(db, 0);
    CodeAction {
        title,
        start_of_change: pos,
        end_of_change: pos,
        replacement: if potential.needs_additional_name {
            format!(
                "from {} import {}\n",
                potential.file.qualified_name(db),
                name.as_code()
            )
        } else {
            format!("import {}\n", potential.file.qualified_name(db))
        },
    }
}
