use std::rc::Rc;

use crate::database::{Database, FileIndex};
use crate::file::PythonFile;
use crate::file_state::File;
use crate::workspaces::{DirContent, DirOrFile};

pub fn global_import(db: &Database, from_file: FileIndex, name: &str) -> Option<FileIndex> {
    if name == "typing" {
        return Some(db.python_state.typing().file_index());
    }
    if name == "typing_extensions" {
        // TODO this is completely wrong
        return Some(db.python_state.typing().file_index());
    }
    if name == "collections" {
        return Some(db.python_state.collections().file_index());
    }

    for (dir_path, dir) in db.workspaces.directories() {
        let result = python_import(db, dir_path, dir, name);
        if result.is_some() {
            return result;
        }
    }
    for (_, dir_children) in db.workspaces.directories() {
        dir_children.add_missing_entry(name.to_owned() + ".py", from_file);
    }
    None
}

pub fn import_on_dir(db: &Database, name: &str) -> Option<FileIndex> {
    todo!()
}

pub fn python_import(
    db: &Database,
    dir_path: &str,
    dir: &Rc<DirContent>,
    name: &str,
) -> Option<FileIndex> {
    let separator = "/"; // TODO different separator
    for directory in dir.iter() {
        match &directory.type_ {
            DirOrFile::Directory(content) => {
                if directory.name == name {
                    for child in content.iter() {
                        match &child.type_ {
                            DirOrFile::File(file_index) => {
                                if child.name == "__init__.py" || child.name == "__init__.pyi" {
                                    if file_index.get().is_none() {
                                        db.load_file_from_workspace(
                                            content.clone(),
                                            format!(
                                                "{dir_path}{separator}{}{separator}{}",
                                                directory.name, child.name
                                            ),
                                            file_index,
                                        );
                                    }
                                    return file_index.get();
                                }
                            }
                            DirOrFile::Directory(_) => {}
                            DirOrFile::MissingEntry(_) => {
                                todo!()
                            }
                        }
                    }
                }
            }
            DirOrFile::File(file_index) => {
                if directory.name == format!("{name}.py") || directory.name == format!("{name}.pyi")
                {
                    if file_index.get().is_none() {
                        db.load_file_from_workspace(
                            dir.clone(),
                            format!("{dir_path}{separator}{}", directory.name),
                            file_index,
                        );
                    }
                    return file_index.get();
                }
            }
            DirOrFile::MissingEntry(_) => (),
        }
    }
    None
}

pub fn find_ancestor(db: &Database, file: &PythonFile, level: usize) -> Option<FileIndex> {
    let path = file.file_path(db);
    let dir_content = db.workspaces.find_ancestor(db.vfs.as_ref(), path, level);
    //dir_content.search("__init__.py").or_else(|| dir_content.search("__init__.py"));
    //dir_content
    todo!()
}
