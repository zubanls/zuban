use std::{array::IntoIter, borrow::Cow, sync::Arc};

use parsa_python_cst::{Decorated, FunctionDef, Name, NameDef};
use vfs::{Directory, DirectoryEntry, Parent};

use crate::{
    database::Database,
    debug,
    file::{File as _, PythonFile},
    imports::{ImportResult, python_import},
    inference_state::InferenceState,
    inferred::Inferred,
    type_::Type,
    type_helpers::{FuncLike as _, Function},
};

const _PYTEST_FIXTURE_MODULES: [&str; 5] =
    ["monkeypatch", "capture", "logging", "tmpdir", "pytester"];

pub(crate) fn maybe_infer_pytest_param(
    db: &Database,
    param: NameDef,
    func: Function,
    func_node: FunctionDef,
) -> Option<Inferred> {
    let func = find_pytest_fixture_for_param(
        db,
        func.file,
        param,
        func.node().name().as_code(),
        func_node.maybe_decorated(),
    )?;

    let i_s = &InferenceState::new(db, func.file);
    let mut t = func.inferred_return_type(i_s);
    debug!("Executed pytest fixture: {}", t.format_short(db));
    if let Type::Class(c) = t.as_ref()
        && c.link == db.python_state.generator_link()
    {
        t = Cow::Owned(c.class(db).nth_type_argument(db, 0));
    }
    Some(Inferred::from_type(t.into_owned()))
}

pub(crate) fn find_pytest_fixture_for_param<'db>(
    db: &'db Database,
    file: &PythonFile,
    param: NameDef,
    func_name: &str,
    decorated: Option<Decorated>,
) -> Option<Function<'db, 'static>> {
    let pytest_folder = db.pytest_folder()?;
    if !is_pytest_fixture_or_test(func_name, decorated) {
        return None;
    }
    let fixture_name = param.as_code();
    let skip_current_module = fixture_name == func_name;
    FixtureModuleIterator::new(db, pytest_folder, file, skip_current_module).find_map(|file| {
        let inf = file
            .lookup(db, |_| (), fixture_name)
            .into_maybe_inferred()?;
        let node_ref = inf.maybe_saved_node_ref(db)?;
        let func_node = node_ref.maybe_function()?;
        let func = Function::new(node_ref, None);
        if !is_fixture(func_node.maybe_decorated()) {
            return None;
        }
        debug!(
            "Found a pytest fixture for param {fixture_name:?} in {:?}",
            func.file.file_path(db),
        );
        Some(func)
    })
}

fn is_pytest_fixture_or_test(func_name: &str, decorated: Option<Decorated>) -> bool {
    // Pytest params are either in a `test*` function or have a pytest fixture
    // with the decorator @pytest.fixture.
    func_name.starts_with("test") || is_fixture(decorated)
}

fn is_fixture(decorated: Option<Decorated>) -> bool {
    decorated.is_some_and(|dec| {
        // TODO check that the fixture is from pytest, this is only a heuristic
        dec.decorators()
            .iter()
            .any(|dec| dec.as_code().contains("fixture"))
    })
}

pub(crate) fn find_all_possible_pytest_fixtures<'db>(
    db: &'db Database,
    file: &'db PythonFile,
    func_name: &str,
    decorated: Option<Decorated>,
) -> Option<impl Iterator<Item = (&'db PythonFile, Name<'db>)>> {
    let pytest_folder = db.pytest_folder()?;
    if !is_pytest_fixture_or_test(func_name, decorated) {
        return None;
    }
    Some(
        FixtureModuleIterator::new(db, pytest_folder, file, false)
            .map(|for_file| {
                for_file
                    .symbol_table
                    .iter()
                    .filter_map(move |(_, &node_index)| {
                        let name = Name::by_index(&for_file.tree, node_index);
                        let func = name.name_def()?.maybe_name_of_func()?;
                        /*
                        if for_file.file_index == file.file_index && func_name == name {
                            return None;
                        }
                        */
                        is_fixture(func.maybe_decorated()).then_some((for_file, name))
                    })
            })
            .flatten(),
    )
}

struct FixtureModuleIterator<'db> {
    db: &'db Database,
    pytest_folder: Arc<Directory>,
    current_module: &'db PythonFile,
    skip_current_module: bool,
    parent: Option<Parent>,
    pytest_fixture_modules: IntoIter<&'static str, 5>,
}

impl<'db> FixtureModuleIterator<'db> {
    fn new(
        db: &'db Database,
        pytest_folder: Arc<Directory>,
        current_module: &'db PythonFile,
        skip_current_module: bool,
    ) -> Self {
        Self {
            db,
            pytest_folder,
            current_module,
            skip_current_module,
            parent: Some(current_module.file_entry(db).parent.clone()),
            pytest_fixture_modules: _PYTEST_FIXTURE_MODULES.into_iter(),
        }
    }
}

impl<'db> Iterator for FixtureModuleIterator<'db> {
    type Item = &'db PythonFile;

    fn next(&mut self) -> Option<Self::Item> {
        // Yield the current module
        if !self.skip_current_module {
            self.skip_current_module = true;
            return Some(self.current_module);
        }
        // Search for conftest.py
        if let Some(mut parent) = self.parent.take() {
            loop {
                let result = parent.with_entries(&*self.db.vfs.handler, |entries| match &*entries
                    .search("conftest.py")?
                {
                    DirectoryEntry::File(entry) => {
                        let found = self.db.load_file_from_workspace(&entry)?;
                        (found.file_index != self.current_module.file_index).then_some(found)
                    }
                    _ => None,
                });
                /*
                * TODO
                   plugins_list = m.tree_node.get_used_names().get("pytest_plugins")
                   if plugins_list:
                       name = conftest_module.create_name(plugins_list[0])
                       yield from _load_pytest_plugins(module_context, name)
                */
                if let Ok(dir) = parent.maybe_dir() {
                    parent = dir.parent.clone();
                    if result.is_some() {
                        self.parent = Some(parent);
                        return result;
                    }
                } else {
                    // This is the case where we are in a workspace. There are no further parents
                    if result.is_some() {
                        return result;
                    } else {
                        break;
                    }
                }
            }
        }

        let pytest_folder_entries = Directory::entries(&*self.db.vfs.handler, &self.pytest_folder);
        self.pytest_fixture_modules
            .by_ref()
            .filter_map(|pytest_module_name| {
                match python_import(
                    self.db,
                    self.current_module,
                    std::iter::once(pytest_folder_entries),
                    pytest_module_name,
                ) {
                    Some(ImportResult::File(file_index)) => {
                        match self.db.ensure_file_for_file_index(file_index) {
                            Ok(file) => Some(file),
                            Err(err) => {
                                debug!(
                                    "Error while loading the pytest file {pytest_module_name}: {err}"
                                );
                                None
                            }
                        }
                    }
                    result => {
                        debug!("Missing the _pytest file {pytest_module_name}, got: {result:?}");
                        None
                    }
                }
            })
            .next()
    }
}

impl Database {
    fn pytest_folder(&self) -> Option<Arc<Directory>> {
        {
            if let Some(folder) = &*self.pytest_folder.read().unwrap()
                && let Some(dir) = folder.upgrade()
            {
                return Some(dir);
            }
        }

        let folder = self.vfs.workspaces.iter().find_map(|workspace| {
            let dir_entry = workspace.entries.search("_pytest")?;
            match &*dir_entry {
                DirectoryEntry::Directory(dir) => Some(dir.clone()),
                _ => None,
            }
        })?;
        *self.pytest_folder.write().unwrap() = Some(Arc::downgrade(&folder));
        Some(folder)
    }
}
