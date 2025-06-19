mod cases;

use std::{
    env,
    fs::{read_dir, read_to_string},
    path::{Path, PathBuf},
    rc::Rc,
    time::Instant,
};

use config::{ProjectOptions, TypeCheckerFlags};
use vfs::{AbsPath, LocalFS};
use zuban_python::Project;

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
    logging_config::setup_logging(None).unwrap();
    let cli_args: Vec<String> = env::args().collect();
    let filters = calculate_filters(&cli_args);
    if cli_args.iter().any(|s| s.as_str() == "mypy") {
        return;
    }

    let mut po = ProjectOptions::new(
        Default::default(),
        //"tests/blackbox/".into(),
        TypeCheckerFlags {
            check_untyped_defs: true,
            ..Default::default()
        },
    );
    po.settings.typeshed_path = Some(test_utils::typeshed_path());
    po.settings.mypy_path = mypy_path();

    let files = python_files(&po.settings.mypy_path);

    let mut project = Project::without_watcher(po);

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

fn mypy_path() -> Vec<Rc<AbsPath>> {
    let base = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("blackbox");

    ["python_files", "from_jedi_python_files"]
        .into_iter()
        .map(|part| {
            LocalFS::without_watcher().abs_path_from_current_dir(base.join(part).to_str().unwrap())
        })
        .collect()
}

fn python_files(mypy_path: &[Rc<AbsPath>]) -> Vec<PathBuf> {
    let mut entries = vec![];
    for path in mypy_path {
        entries.extend(
            read_dir(path.as_ref())
                .unwrap()
                .map(|res| res.map(|e| e.path()).unwrap()),
        );
    }
    entries.sort();
    entries
}
