use crate::database::{Database, FileIndex};
use crate::file_state::File;
use crate::workspaces::DirectoryOrFile;

pub fn global_import(database: &Database, name: &str) -> Option<FileIndex> {
    if name == "typing" {
        return Some(database.python_state.typing().file_index());
    }
    if name == "typing_extensions" {
        // TODO this is completely wrong
        return Some(database.python_state.typing().file_index());
    }

    let result = python_import(database, database.workspaces.borrow().directories(), name);
    result
}

pub fn import_on_dir(database: &Database, name: &str) -> Option<FileIndex> {
    todo!()
}

fn python_import<'db>(
    database: &Database,
    directories: impl Iterator<Item = (&'db str, &'db [DirectoryOrFile])>,
    name: &str,
) -> Option<FileIndex> {
    let separator = "/"; // TODO different separator
    for (dir_path, dir_children) in directories {
        for directory in dir_children {
            match directory {
                DirectoryOrFile::Directory(dir_name, children) => {
                    if dir_name == name {
                        for child in children {
                            match child {
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
            }
        }
    }
    None
}
