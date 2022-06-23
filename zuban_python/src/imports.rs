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
    if name == "types" {
        return Some(db.python_state.types().file_index());
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
    let mut python_file_index = None;
    let mut stub_file_index = None;
    for directory in dir.iter() {
        match &directory.type_ {
            DirOrFile::Directory(content) => {
                if directory.name == name {
                    let result = load_init_file(db, content, |child| {
                        format!(
                            "{dir_path}{separator}{dir_name}{separator}{child}",
                            dir_name = directory.name
                        )
                    });
                    if result.is_some() {
                        return result;
                    }
                }
            }
            DirOrFile::File(file_index) => {
                let is_py_file = directory.name == format!("{name}.py");
                if is_py_file || directory.name == format!("{name}.pyi") {
                    if file_index.get().is_none() {
                        db.load_file_from_workspace(
                            dir.clone(),
                            format!("{dir_path}{separator}{}", directory.name),
                            file_index,
                        );
                    }
                    debug_assert!(file_index.get().is_some());
                    if is_py_file {
                        python_file_index = file_index.get();
                    } else {
                        stub_file_index = file_index.get();
                    }
                }
            }
            DirOrFile::MissingEntry(_) => (),
        }
    }
    stub_file_index.or(python_file_index)
}

fn load_init_file(
    db: &Database,
    content: &Rc<DirContent>,
    on_new: impl Fn(&str) -> String,
) -> Option<FileIndex> {
    for child in content.iter() {
        if let DirOrFile::File(file_index) = &child.type_ {
            if child.name == "__init__.py" || child.name == "__init__.pyi" {
                if file_index.get().is_none() {
                    db.load_file_from_workspace(content.clone(), on_new(&child.name), file_index);
                }
                return file_index.get();
            }
        }
    }
    None
}

pub fn find_ancestor(db: &Database, file: &PythonFile, level: usize) -> Option<FileIndex> {
    debug_assert!(level > 0);
    let mut path = file.file_path(db);
    for _ in 0..level {
        if let (Some(dir), _) = db.vfs.dir_and_name(path) {
            path = dir;
        } else {
            todo!()
        }
    }
    db.workspaces
        .find_dir_content(db.vfs.as_ref(), path)
        .and_then(|dir_content| load_init_file(db, &dir_content, |_| todo!()))
}
