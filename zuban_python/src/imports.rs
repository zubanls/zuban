use crate::database::{Database, FileIndex};
use crate::file_state::File;
use crate::workspaces::{DirContent, DirectoryOrFile};
use std::ops::Deref;

pub fn global_import(database: &Database, from_file: FileIndex, name: &str) -> Option<FileIndex> {
    if name == "typing" {
        return Some(database.python_state.typing().file_index());
    }
    if name == "typing_extensions" {
        // TODO this is completely wrong
        return Some(database.python_state.typing().file_index());
    }

    let result = python_import(database, database.workspaces.directories(), name);
    if result.is_none() {
        for (_, dir_children) in database.workspaces.directories() {
            dir_children.add_missing_entry(name, from_file);
        }
    }
    result
}

pub fn import_on_dir(database: &Database, name: &str) -> Option<FileIndex> {
    todo!()
}

fn python_import<'db>(
    database: &Database,
    directories: impl Iterator<Item = (&'db str, &'db DirContent)>,
    name: &str,
) -> Option<FileIndex> {
    let separator = "/"; // TODO different separator
    for (dir_path, dir_children) in directories {
        for directory in dir_children.iter() {
            match directory.deref() {
                DirectoryOrFile::Directory(dir_name, children) => {
                    if dir_name == name {
                        for child in children.iter() {
                            match child.deref() {
                                DirectoryOrFile::File(file_name, file_index) => {
                                    if file_name == "__init__.py" || file_name == "__init__.pyi" {
                                        if file_index.get().is_none() {
                                            database.load_file_from_workspace(
                                                format!(
                                                    "{}{}{}{}{}",
                                                    dir_path,
                                                    separator,
                                                    dir_name,
                                                    separator,
                                                    file_name
                                                ),
                                                file_index,
                                            );
                                        }
                                        return file_index.get();
                                    }
                                }
                                DirectoryOrFile::Directory(_, _) => {}
                                DirectoryOrFile::MissingEntry(dir_name, children) => {
                                    todo!()
                                }
                            }
                        }
                    }
                }
                DirectoryOrFile::File(file_name, file_index) => {
                    if file_name == &format!("{}.py", name) || file_name == &format!("{}.pyi", name)
                    {
                        if file_index.get().is_none() {
                            database.load_file_from_workspace(
                                format!("{}{}{}", dir_path, separator, file_name),
                                file_index,
                            );
                        }
                        return file_index.get();
                    }
                }
                DirectoryOrFile::MissingEntry(dir_name, children) => (),
            }
        }
    }
    None
}
