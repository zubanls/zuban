use crate::database::FileIndex;
use crate::database::{Database, DirectoryOrFile};
use crate::debug;
use DirectoryOrFile::{Directory, File};

pub fn global_import(database: &Database, name: &str) -> Option<FileIndex> {
    debug!("Global import {}", name);
    python_import(
        database,
        database.workspaces.iter().map(|x| x.get_root()),
        name,
    )
}

fn python_import<'a>(
    database: &Database,
    directories: impl Iterator<Item = &'a DirectoryOrFile>,
    name: &str,
) -> Option<FileIndex> {
    for directory in directories {
        match directory {
            Directory(dir_name, children) => {
                if dir_name == name {}
                for child in children {
                    match child {
                        File(file_name, file_index) => {
                            if file_name == "__init__.py" || file_name == "__init__.pyi" {
                                if file_index.get().is_none() {
                                    database.load_file_from_workspace(
                                        "".to_owned(),
                                        file_index.clone(),
                                    );
                                }
                                return file_index.get();
                            }
                        }
                        Directory(_, _) => {}
                    }
                }
            }
            File(file_name, file_index) => {
                if file_name == &format!("{}.py", name) || file_name == &format!("{}.pyi", name) {
                    return file_index.get();
                }
                unreachable!()
            }
        }
    }
    None
}
