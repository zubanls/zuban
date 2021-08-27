use crate::database::FileIndex;
use crate::database::{Database, DirectoryOrFile};
use crate::debug;
use DirectoryOrFile::{Directory, File};

pub fn global_import(database: &Database, name: &str) -> Option<FileIndex> {
    let result = python_import(
        database,
        database.workspaces.iter().map(|x| (x.get_root().get_name(), x.get_root().get_directory_entries().unwrap())),
        name,
    );
    debug!("Global import {}: {:?}", name, result);
    result
}

pub fn import_on_dir(database: &Database, name: &str) -> Option<FileIndex> {
    todo!()
}

fn python_import<'a>(
    database: &Database,
    directories: impl Iterator<Item = (&'a str, &'a [DirectoryOrFile])>,
    name: &str,
) -> Option<FileIndex> {
    let separator = "/"; // TODO different separator
    for (dir_path, dir_children) in directories {
        for directory in dir_children {
            match directory {
                Directory(dir_name, children) => {
                    if dir_name == name {
                        for child in children {
                            match child {
                                File(file_name, file_index) => {
                                    if file_name == "__init__.py" || file_name == "__init__.pyi" {
                                        if file_index.get().is_none() {
                                            database.load_file_from_workspace(
                                                format!("{}{}{}{}{}", dir_path, separator, dir_name, separator, file_name),
                                                file_index,
                                            );
                                        }
                                        return file_index.get();
                                    }
                                }
                                Directory(_, _) => {}
                            }
                        }
                    }
                }
                File(file_name, file_index) => {
                    if file_name == &format!("{}.py", name) || file_name == &format!("{}.pyi", name) {
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
