mod cases;

use std::env;
use std::fs::{read_dir, read_to_string};
use std::path::PathBuf;
use std::time::Instant;

use zuban_python::{Project, ProjectOptions};

#[derive(Debug)]
pub struct Filter {
    name: String,
    lines: Vec<usize>,
    negative: bool,
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

fn main() {
    let cli_args: Vec<String> = env::args().collect();
    let filters = calculate_filters(&cli_args);
    if cli_args.iter().any(|s| s.as_str() == "mypy") {
        return;
    }

    let mut project = Project::new(ProjectOptions {
        path: "tests/blackbox/".into(),
        strict_optional: true,
        implicit_optional: false,
        check_untyped_defs: true,
        disallow_untyped_defs: false,
        disallow_untyped_calls: false,
        mypy_compatible: false,
        extra_checks: false,
    });

    let files = python_files();
    let start = Instant::now();
    let mut full_count = 0;
    let mut ran_count = 0;
    let file_count = files.len();
    for python_file in files {
        let code = read_to_string(&python_file).unwrap().into();
        let f = cases::TestFile {
            path: python_file,
            code,
            filters: &filters,
        };
        let (ran, full) = f.test(&mut project);
        ran_count += ran;
        full_count += full;
    }
    println!(
        "Ran {} of {} integration tests in {} files; finished in {:.2}s",
        ran_count,
        full_count,
        file_count,
        start.elapsed().as_secs_f32(),
    );
}

fn python_files() -> Vec<PathBuf> {
    let mut base = PathBuf::from(file!().replace("zuban_python/", ""));
    assert!(base.pop());

    let mut entries = vec![];
    for p in ["python_files", "from_jedi_python_files"] {
        let mut path = base.clone();
        path.push(p);

        entries.extend(
            read_dir(path)
                .unwrap()
                .map(|res| res.map(|e| e.path()).unwrap()),
        );
    }
    entries.sort();
    entries
}
