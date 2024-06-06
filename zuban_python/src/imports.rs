use std::{
    borrow::{Borrow, Cow},
    rc::Rc,
};

use crate::{
    database::{Database, FileIndex},
    debug,
    file::{File, PythonFile},
    type_::Namespace,
    type_helpers::Module,
    workspaces::{Directory, DirectoryEntry},
    TypeCheckerFlags,
};

pub const STUBS_SUFFIX: &str = "-stubs";
const INIT_PY: &str = "__init__.py";
const INIT_PYI: &str = "__init__.pyi";

#[derive(Debug)]
pub enum ImportResult {
    File(FileIndex),
    Namespace(Rc<Namespace>), // A Python Namespace package, i.e. a directory
}

impl ImportResult {
    pub fn import(
        &self,
        db: &Database,
        original_file_index: FileIndex,
        name: &str,
    ) -> Option<ImportResult> {
        match self {
            Self::File(file_index) => {
                let module = Module::from_file_index(db, *file_index);
                module.sub_module(db, name)
            }
            Self::Namespace(ns) => python_import(
                db,
                original_file_index,
                ns.directories.iter().cloned(),
                name,
            ),
        }
    }

    pub fn qualified_name(&self, db: &Database) -> String {
        match self {
            Self::File(file_index) => db.loaded_python_file(*file_index).qualified_name(db),
            Self::Namespace(ns) => ns.qualified_name(),
        }
    }

    pub fn debug_path<'x>(&'x self, db: &'x Database) -> Cow<'x, str> {
        match self {
            Self::File(f) => Cow::Borrowed(db.loaded_python_file(*f).file_path(db)),
            Self::Namespace(namespace) => Cow::Owned(namespace.debug_path(db)),
        }
    }
}

pub fn global_import<'a>(
    db: &'a Database,
    from_file: FileIndex,
    name: &'a str,
) -> Option<ImportResult> {
    if match_case(&db.project.flags, name, "typing_extensions") {
        return Some(ImportResult::File(
            db.python_state.typing_extensions().file_index(),
        ));
    }
    if match_case(&db.project.flags, name, "functools") {
        return Some(ImportResult::File(db.python_state.functools().file_index()));
    }
    global_import_without_stubs_first(db, from_file, &format!("{name}{STUBS_SUFFIX}"))
        .or_else(|| global_import_without_stubs_first(db, from_file, name))
}

pub fn global_import_without_stubs_first<'a>(
    db: &'a Database,
    from_file: FileIndex,
    name: &'a str,
) -> Option<ImportResult> {
    python_import(
        db,
        from_file,
        db.workspaces.directories().map(|(_, d)| d),
        name,
    )
}

pub fn python_import<'a, 'x>(
    db: &Database,
    from_file: FileIndex,
    dirs: impl Iterator<Item = impl Borrow<Directory>>,
    name: &'a str,
) -> Option<ImportResult> {
    python_import_with_needs_exact_case(db, from_file, dirs, name, false)
}

pub fn python_import_with_needs_exact_case<'a, 'x>(
    db: &Database,
    from_file: FileIndex,
    dirs: impl Iterator<Item = impl Borrow<Directory>>,
    name: &'a str,
    needs_exact_case: bool,
) -> Option<ImportResult> {
    let mut python_file_index = None;
    let mut stub_file_index = None;
    let mut namespace_directories = vec![];
    'outer: for dir in dirs {
        let dir = dir.borrow();
        for entry in &dir.iter() {
            match entry {
                DirectoryEntry::Directory(dir2) => {
                    if match_c(db, dir2.name.as_ref(), name, needs_exact_case) {
                        let result = load_init_file(db, dir2);
                        if let Some(file_index) = &result {
                            db.add_invalidates(*file_index, from_file);
                            return result.map(ImportResult::File);
                        }
                        dir2.add_missing_entry(Box::from(INIT_PY), from_file);
                        dir2.add_missing_entry(Box::from(INIT_PYI), from_file);
                        namespace_directories.push(dir2.clone());
                        continue 'outer;
                    }
                }
                DirectoryEntry::File(file) => {
                    // TODO these format!() always allocate a lot and don't seem to be necessary
                    let is_py_file =
                        match_c(db, &file.name, &format!("{name}.py"), needs_exact_case);
                    if is_py_file
                        || match_c(db, &file.name, &format!("{name}.pyi"), needs_exact_case)
                    {
                        if file.file_index.get().is_none() {
                            db.load_file_from_workspace(file.clone(), false);
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
        dir.add_missing_entry(name.into(), from_file);
    }
    if !namespace_directories.is_empty() {
        debug!("// TODO invalidate!");
        return Some(ImportResult::Namespace(Rc::new(Namespace {
            directories: namespace_directories.into(),
        })));
    }
    None
}

#[inline]
fn match_c(db: &Database, x: &str, y: &str, needs_exact_case: bool) -> bool {
    if needs_exact_case {
        x == y
    } else {
        match_case(&db.project.flags, x, y)
    }
}

pub fn match_case(flags: &TypeCheckerFlags, x: &str, y: &str) -> bool {
    if flags.case_sensitive {
        x == y
    } else {
        x.eq_ignore_ascii_case(y)
    }
}

fn load_init_file(db: &Database, content: &Directory) -> Option<FileIndex> {
    for child in &content.iter() {
        if let DirectoryEntry::File(file) = child {
            if match_c(db, &file.name, INIT_PY, false) || match_c(db, &file.name, INIT_PYI, false) {
                if file.file_index.get().is_none() {
                    db.load_file_from_workspace(file.clone(), false);
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
