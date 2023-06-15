use std::rc::Rc;

use crate::database::{Database, FileIndex};
use crate::file::File;
use crate::file::PythonFile;
use crate::workspaces::{DirContent, DirOrFile};

pub enum ImportResult {
    File(FileIndex),
}

impl ImportResult {
    pub fn path<'db>(&self, db: &'db Database) -> &'db str {
        match self {
            Self::File(f) => db.loaded_python_file(*f).file_path(db),
        }
    }
}

pub fn global_import(db: &Database, from_file: FileIndex, name: &str) -> Option<ImportResult> {
    if name == "typing" {
        return Some(ImportResult::File(db.python_state.typing().file_index()));
    }
    if name == "typing_extensions" {
        return Some(ImportResult::File(
            db.python_state.typing_extensions().file_index(),
        ));
    }
    if name == "collections" {
        return Some(ImportResult::File(
            db.python_state.collections().file_index(),
        ));
    }
    if name == "types" {
        return Some(ImportResult::File(db.python_state.types().file_index()));
    }
    if name == "mypy_extensions" {
        // TODO this is completely wrong
        return Some(ImportResult::File(
            db.python_state.mypy_extensions().file_index(),
        ));
    }

    for (dir_path, dir) in db.workspaces.directories() {
        let result = python_import(db, from_file, dir_path, dir, name);
        if result.is_some() {
            return result;
        }
    }
    None
}

pub fn python_import(
    db: &Database,
    from_file: FileIndex,
    dir_path: &str,
    dir: &Rc<DirContent>,
    name: &str,
) -> Option<ImportResult> {
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
                        return result.map(ImportResult::File);
                    }
                    content.add_missing_entry("__init__.py".to_string(), from_file);
                    content.add_missing_entry("__init__.pyi".to_string(), from_file);
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
    let result = stub_file_index
        .or(python_file_index)
        .map(ImportResult::File);
    if result.is_none() {
        dir.add_missing_entry(name.to_string() + ".py", from_file);
        dir.add_missing_entry(name.to_string() + ".pyi", from_file);
    }
    result
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

pub fn find_ancestor(db: &Database, file: &PythonFile, level: usize) -> Option<ImportResult> {
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
        .map(ImportResult::File)
}
