use std::rc::Rc;

use crate::{
    database::{Database, FileIndex},
    debug,
    file::{File, PythonFile},
    type_::Namespace,
    workspaces::{Directory, DirectoryEntry},
};

#[derive(Debug)]
pub enum ImportResult {
    File(FileIndex),
    Namespace(Rc<Namespace>), // A Python Namespace package, i.e. a directory
}

impl ImportResult {
    pub fn qualified_name(&self, db: &Database) -> String {
        match self {
            Self::File(file_index) => db.loaded_python_file(*file_index).qualified_name(db),
            Self::Namespace(ns) => ns.qualified_name(),
        }
    }

    pub fn path<'x>(&'x self, db: &'x Database) -> &'x str {
        match self {
            Self::File(f) => db.loaded_python_file(*f).file_path(db),
            Self::Namespace(namespace) => &namespace.path,
        }
    }
}

pub fn global_import<'a>(
    db: &'a Database,
    from_file: FileIndex,
    name: &'a str,
) -> Option<ImportResult> {
    if name == "typing_extensions" {
        return Some(ImportResult::File(
            db.python_state.typing_extensions().file_index(),
        ));
    }
    if name == "functools" {
        return Some(ImportResult::File(db.python_state.functools().file_index()));
    }

    for (dir_path, dir) in db.workspaces.directories() {
        let result = python_import(db, from_file, dir, name);
        if result.is_some() {
            return result;
        }
    }
    None
}

pub fn python_import<'a>(
    db: &Database,
    from_file: FileIndex,
    dir: &Directory,
    name: &'a str,
) -> Option<ImportResult> {
    let mut python_file_index = None;
    let mut stub_file_index = None;
    let mut namespace_content = None;
    for entry in &dir.iter() {
        match entry {
            DirectoryEntry::Directory(dir2) => {
                if dir2.name.as_ref() == name {
                    let result = load_init_file(db, dir2);
                    if let Some(file_index) = &result {
                        db.add_invalidates(*file_index, from_file);
                        return result.map(ImportResult::File);
                    }
                    dir2.add_missing_entry(Box::from("__init__.py"), from_file);
                    dir2.add_missing_entry(Box::from("__init__.pyi"), from_file);
                    namespace_content = Some(dir2.clone());
                }
            }
            DirectoryEntry::File(file) => {
                let is_py_file = file.name.as_ref() == format!("{name}.py");
                if is_py_file || file.name.as_ref() == format!("{name}.pyi") {
                    if file.file_index.get().is_none() {
                        db.load_file_from_workspace(file.clone());
                    }
                    debug_assert!(file.file_index.get().is_some());
                    if is_py_file {
                        python_file_index = file.file_index.get();
                    } else {
                        stub_file_index = file.file_index.get();
                    }
                }
            }
            DirectoryEntry::MissingEntry { .. } => (),
        }
    }
    if let Some(file_index) = stub_file_index.or(python_file_index) {
        db.add_invalidates(file_index, from_file);
        return Some(ImportResult::File(file_index));
    }
    dir.add_missing_entry((name.to_string() + ".py").into(), from_file);
    dir.add_missing_entry((name.to_string() + ".pyi").into(), from_file);
    // The folder should not exist for folder/__init__.py or a namespace.
    if let Some(content) = namespace_content {
        debug!("// TODO invalidate!");
        return Some(ImportResult::Namespace(Rc::new(Namespace {
            path: content.path(&*db.vfs),
            content,
        })));
    }
    dir.add_missing_entry(name.into(), from_file);
    None
}

fn load_init_file(db: &Database, content: &Directory) -> Option<FileIndex> {
    for child in &content.iter() {
        if let DirectoryEntry::File(file) = child {
            if file.name.as_ref() == "__init__.py" || file.name.as_ref() == "__init__.pyi" {
                if file.file_index.get().is_none() {
                    db.load_file_from_workspace(file.clone());
                }
                return file.file_index.get();
            }
        }
    }
    None
}

pub fn find_ancestor(db: &Database, file: &PythonFile, level: usize) -> Option<ImportResult> {
    debug_assert!(level > 0);
    let mut parent = file.file_entry(db).parent.maybe_dir().ok()?;
    for _ in 1..level {
        parent = parent.parent.maybe_dir().ok()?;
    }
    Some(ImportResult::File(
        load_init_file(db, &parent).unwrap_or_else(|| todo!()),
    ))
}
