mod cases;

use std::{
    collections::HashMap,
    env,
    fs::{read_dir, read_to_string},
    path::{Path, PathBuf},
    process::ExitCode,
    rc::Rc,
    time::Instant,
};

use config::{ProjectOptions, Settings, TypeCheckerFlags};
use vfs::{LocalFS, NormalizedPath};
use zuban_python::{Mode, Project};

#[derive(Debug)]
pub struct Filter {
    name: String,
    lines: Vec<usize>,
    negative: bool,
}

const SKIPPED_FILES: [&str; 39] = [
    "async_.py",
    "basic.py",
    "completion.py",
    "complex.py",
    "conftest.py",
    "context.py",
    "decorators.py",
    "django.py",
    "docstring.py",
    "dynamic_arrays.py",
    "dynamic_params.py",
    "fixture_module.py",
    "flow_analysis.py",
    "fstring.py",
    "generators.py",
    "goto.py",
    "imports.py",
    "import_tree",
    "__init__.py",
    "invalid.py",
    "keywords.py",
    "lambdas.py",
    "named_param.py",
    "namespace1",
    "namespace2",
    "ns_path.py",
    "on_import.py",
    "ordering.py",
    "positional_only_params.py",
    "precedence.py",
    "pytest.py",
    "recursion.py",
    "stdlib.py",
    "stub_folder",
    "stubs.py",
    "sys_path.py",
    "types.py",
    "usages.py",
    // Our own
    "unreachable_no_crash.py",
];

lazy_static::lazy_static! {
    static ref EXPECTED_TEST_FAILURES: HashMap<&'static str, usize> = HashMap::from([
        ("arrays.py", 49),
        ("classes.py", 24),
        ("comprehensions.py", 36),
        ("descriptors.py", 2),
        ("functions.py", 57),
        ("inheritance.py", 3),
        ("isinstance.py", 3),
        ("parser.py", 2),
        ("pep0484_generic_passthroughs.py", 5),
        ("pep0484_typing.py", 3),
    ]);
}

impl Filter {
    fn new(name: &str, negative: bool) -> Self {
        Self {
            name: name.to_owned(),
            lines: vec![],
            negative,
        }
    }

    pub fn allowed(&self, file_name: &str, line: usize) -> bool {
        if self.negative || !file_name.contains(&self.name) {
            return false;
        }
        if self.lines.is_empty() {
            return true;
        }
        self.lines.contains(&line)
    }

    pub fn denied(&self, file_name: &str, line: usize) -> bool {
        if !self.negative || !file_name.contains(&self.name) {
            return false;
        }
        if self.lines.is_empty() {
            return true;
        }
        self.lines.contains(&line)
    }
}

fn calculate_filters(args: &[String]) -> Vec<Filter> {
    let mut filters: Vec<Filter> = vec![];
    for c in &args[1..] {
        if let Ok(line) = c.parse::<usize>() {
            filters.last_mut().unwrap().lines.push(line);
        } else if let Some(stripped) = c.strip_prefix('!') {
            filters.push(Filter::new(stripped, true));
        } else if c != "blackbox" {
            filters.push(Filter::new(c, false));
        }
    }
    filters
}

fn main() -> ExitCode {
    logging_config::setup_logging(None).unwrap();
    let cli_args: Vec<String> = env::args().collect();
    let filters = calculate_filters(&cli_args);
    if cli_args.iter().any(|s| s.as_str() == "mypy") {
        return ExitCode::from(0);
    }

    let po = ProjectOptions::new(
        Settings {
            typeshed_path: Some(test_utils::typeshed_path()),
            mypy_path: mypy_path(),
            ..Default::default()
        },
        TypeCheckerFlags {
            check_untyped_defs: true,
            allow_redefinition: true,
            ..Default::default()
        },
    );

    let files = python_files(&po.settings.mypy_path);

    let mut project = Project::without_watcher(po, Mode::LanguageServer);

    let start = Instant::now();
    let mut full_count = 0;
    let mut ran_count = 0;
    let mut error_count = 0;
    let mut unexpected_error_count = 0;
    let mut file_count = 0;
    let mut should_error_out = false;
    for python_file in files {
        let file_name = &python_file.file_name().unwrap().to_str().unwrap();
        if SKIPPED_FILES.contains(file_name) {
            continue;
        }
        let code = read_to_string(&python_file).unwrap().into();
        let f = cases::TestFile {
            path: &python_file,
            code,
            filters: &filters,
        };
        let (ran, full, errors) = f.test(&mut project);
        ran_count += ran;
        full_count += full;

        if let Some(&expected) = EXPECTED_TEST_FAILURES.get(file_name) {
            if expected != errors && ran > 0 {
                unexpected_error_count += errors.checked_sub(expected).unwrap_or(0);
                println!("Expected {expected} errors for {file_name}, but had {errors}");
                should_error_out = true;
            }
        } else {
            unexpected_error_count += errors;
            should_error_out |= errors > 0
        }
        error_count += errors;
        file_count += 1;
    }
    println!(
        "Ran {ran_count} of {full_count} ({unexpected_error_count} unexpected errors; \
         {error_count} expected) blackbox tests in {file_count} files; finished in {:.2}s",
        start.elapsed().as_secs_f32(),
    );
    ExitCode::from(should_error_out as u8)
}

fn mypy_path() -> Vec<Rc<NormalizedPath>> {
    let base = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("blackbox");

    ["python_files", "from_jedi_python_files"]
        .into_iter()
        .map(|part| {
            LocalFS::without_watcher()
                .normalized_path_from_current_dir(base.join(part).to_str().unwrap())
        })
        .collect()
}

fn python_files(mypy_path: &[Rc<NormalizedPath>]) -> Vec<PathBuf> {
    let mut entries = vec![];
    for path in mypy_path {
        entries.extend(
            read_dir(path.as_ref().as_ref())
                .unwrap()
                .map(|res| res.map(|e| e.path()).unwrap()),
        );
    }
    entries.sort();
    entries
}
