mod cases;

use std::{
    collections::HashMap,
    env,
    fs::{read_dir, read_to_string},
    path::{Path, PathBuf},
    process::ExitCode,
    sync::Arc,
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

lazy_static::lazy_static! {
    static ref EXPECTED_TEST_FAILURES: HashMap<&'static str, usize> = HashMap::from([
        ("arrays.py", 44),
        ("async_.py", 4),
        ("basic.py", 23),
        ("classes.py", 20),
        ("comprehensions.py", 31),
        ("django.py", 3),
        ("decorators.py", 31),
        ("descriptors.py", 2),
        ("dynamic_arrays.py", 18),
        ("flow_analysis.py", 16),
        ("fstring.py", 4),
        ("functions.py", 51),
        ("generators.py", 13),
        ("inheritance.py", 3),
        ("__init__.py", 1),
        ("isinstance.py", 3),
        ("lambdas.py", 18),
        ("named_param.py", 10),
        ("ordering.py", 5),
        ("pep0484_typing.py", 3),
        ("positional_only_params.py", 3),
        ("precedence.py", 7),
        ("stdlib.py", 43),

        // TODO work on these files
        ("completion.py", 6),
        ("context.py", 4),
        ("conftest.py", 1),
        ("docstring.py", 38),
        ("dynamic_params.py", 18),
        ("imports.py", 9),
        ("goto.py", 4),
        ("keywords.py", 9),
        ("ns_path.py", 4),
        ("pytest.py", 33),
        ("sys_path.py", 4),
        ("stubs.py", 5),
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
        } else {
            filters.push(Filter::new(c, false));
        }
    }
    filters
}

fn main() -> ExitCode {
    logging_config::setup_logging(None).unwrap();
    let cli_args: Vec<String> = env::args().collect();
    let filters = calculate_filters(&cli_args);

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
    let mut end_messages = vec![];
    for python_file in files {
        let file_name = &python_file.file_name().unwrap().to_str().unwrap();
        if !file_name.ends_with(".py") && !file_name.ends_with(".pyi") {
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
                unexpected_error_count += errors.saturating_sub(expected);
                end_messages.push(format!(
                    "Expected {expected} errors for {file_name}, but had {errors}"
                ));
                should_error_out = true;
            }
        } else {
            unexpected_error_count += errors;
            if errors > 0 {
                end_messages.push(format!(
                    "Expected 0 errors for {file_name}, but had {errors}"
                ));
            }
            should_error_out |= errors > 0
        }
        error_count += errors;
        file_count += 1;
    }
    for message in end_messages {
        println!("{message}");
    }
    if !filters.is_empty() && ran_count == 0 {
        println!("Did not find any file for filters {filters:?}");
        should_error_out = true
    }
    println!(
        "Ran {ran_count} of {full_count} ({unexpected_error_count} unexpected errors; \
         {expected} expected) blackbox tests in {file_count} files; finished in {:.2}s",
        start.elapsed().as_secs_f32(),
        expected = error_count - unexpected_error_count,
    );
    ExitCode::from(should_error_out as u8)
}

fn mypy_path() -> Vec<Arc<NormalizedPath>> {
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

fn python_files(mypy_path: &[Arc<NormalizedPath>]) -> Vec<PathBuf> {
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
