use std::collections::HashMap;
use std::fs::{read_dir, read_to_string};
use std::path::PathBuf;
use std::time::Instant;

use regex::{Captures, Regex, Replacer};

const USE_MYPY_TEST_FILES: [&str; 2] = ["fine-grained.test", "check-generic-alias.test"];

const BASE_PATH: &str = "/mypylike/";

lazy_static::lazy_static! {
    static ref CASE: Regex = Regex::new(r"(?m)^\[case ([a-zA-Z_0-9-]+)\][ \t]*\n").unwrap();
    // This is how I found out about possible "commands in mypy, executed in
    // mypy/test-data/unit:
    // find . | grep check | xargs cat | grep '^\[' | grep -Ev '\[(out|case|file)'
    static ref CASE_PART: Regex = Regex::new(concat!(
        r"(?m)^\[(file|out\d*|builtins|typing|stale|rechecked|targets\d?|delete|triggered)",
        r"(?: ([^\]]*))?\][ \t]*\n"
    )).unwrap();
    static ref REPLACE_COMMENTS: Regex = Regex::new(r"(?m)^--.*$\n").unwrap();
    static ref REPLACE_TUPLE: Regex = Regex::new(r"\bTuple\b").unwrap();
}

#[derive(Default, Clone, Debug)]
struct Step<'code> {
    deletions: Vec<&'code str>,
    files: HashMap<&'code str, &'code str>,
    out: &'code str,
}

#[derive(Debug)]
struct TestCase<'name, 'code> {
    file_name: &'name str,
    name: String,
    code: &'code str,
}

struct Steps<'code> {
    steps: Vec<Step<'code>>,
    flags: Vec<&'code str>,
}

impl<'name, 'code> TestCase<'name, 'code> {
    fn run(&self, project: &mut zuban_python::Project) {
        let steps = self.calculate_steps();
        let mut diagnostics_config = zuban_python::DiagnosticConfig::default();

        if steps.flags.contains(&"--ignore-missing-imports") {
            diagnostics_config.ignore_missing_imports = true;
        }

        if steps
            .flags
            .iter()
            .position(|&r| r == "--python-version")
            .map(|p| ["2.7", "3.5", "3.6", "3.7", "3.8"].contains(&steps.flags[p + 1]))
            .unwrap_or(false)
        {
            // For now skip Python tests < 3.9, because it looks like we won't support them.
            println!("Skipped: {}, because {:?}", self.file_name, steps.flags);
            return;
        }

        for (i, step) in steps.steps.iter().enumerate() {
            if cfg!(feature = "zuban_debug") {
                println!(
                    "\nTest: {} ({}): Step {}/{}",
                    self.name,
                    self.file_name,
                    i + 1,
                    steps.steps.len()
                );
            }
            let mut specified_lines = REPLACE_TUPLE
                .replace_all(step.out, TypeStuffReplacer())
                .trim()
                .split("\n")
                .map(|s| s.to_owned())
                .collect::<Vec<_>>();

            if specified_lines == [""] {
                specified_lines.pop();
            }

            for (&path, &code) in &step.files {
                specified_lines.extend(ErrorCommentsOnCode(path, code.split("\n").enumerate()));
                project.load_in_memory_file(BASE_PATH.to_owned() + path, code.to_owned());
            }
            specified_lines.sort();

            for path in &step.deletions {
                #[allow(unused_must_use)]
                {
                    project.unload_in_memory_file(&(BASE_PATH.to_owned() + path));
                }
            }
            let diagnostics: Vec<_> = project
                .diagnostics(&diagnostics_config)
                .iter()
                .map(|d| d.as_string())
                .collect();

            let actual = diagnostics.iter().fold(String::new(), |a, b| a + &b + "\n");
            let mut actual_lines = actual.trim().split("\n").collect::<Vec<_>>();
            if actual_lines == [""] {
                actual_lines.pop();
            }
            actual_lines.sort();

            assert_eq!(
                actual_lines,
                specified_lines,
                "\n\nError in {} ({}): Step {}/{}\n\nWanted:\n{}\n\nActual:\n{}\n",
                &self.name,
                self.file_name,
                i + 1,
                steps.steps.len(),
                specified_lines
                    .iter()
                    .fold(String::new(), |a, b| a + &b + "\n"),
                actual,
            );
        }
        for step in &steps.steps {
            for (path, _) in &step.files {
                #[allow(unused_must_use)]
                {
                    project.unload_in_memory_file(&(BASE_PATH.to_owned() + path));
                }
            }
        }
    }

    fn calculate_steps(&self) -> Steps {
        let mut steps = HashMap::<usize, Step>::new();
        steps.insert(1, Default::default());
        let mut current_step_index = 1;
        let mut current_type = "file";
        let mut current_rest = "main";
        let mut current_step_start = 0;
        let mut flags = vec![];

        let mut process_step_part2 = |step_index, type_, in_between, rest| {
            let step = if let Some(s) = steps.get_mut(&step_index) {
                s
            } else {
                steps.insert(step_index, Default::default());
                steps.get_mut(&step_index).unwrap()
            };
            if type_ == "file" {
                step.files.insert(rest, in_between);
            } else if type_ == "out" {
                step.out = in_between;
            } else if type_ == "delete" {
                step.deletions.push(rest)
            }
        };

        let mut process_step = |step_index, type_, step_start, step_end, rest| {
            let in_between = &self.code[step_start..step_end];

            if type_ == "out" && step_index == 1 {
                assert_eq!(rest, "");
                for (i, part) in in_between.split("==\n").enumerate() {
                    process_step_part2(i + 1, "out", part, rest)
                }
            } else {
                process_step_part2(step_index, type_, in_between, rest)
            }
            if rest == "main" {
                if in_between.starts_with("# flags: ") {
                    let all_flags = &in_between[9..in_between.find("\n").unwrap()];
                    flags = all_flags.split(' ').collect();
                }
            }
        };

        for capture in CASE_PART.captures_iter(&self.code) {
            process_step(
                current_step_index,
                current_type,
                current_step_start,
                capture.get(0).unwrap().start(),
                current_rest,
            );

            current_type = capture.get(1).unwrap().as_str();
            current_rest = capture.get(2).map(|x| x.as_str()).unwrap_or("");
            current_step_start = capture.get(0).unwrap().end();

            current_step_index = 1;
            if current_type == "file" || current_type == "delete" {
                let last = current_rest.chars().last().unwrap();
                if let Some(digit) = last.to_digit(10) {
                    current_step_index = digit as usize;
                    current_rest = &current_rest[..current_rest.len() - 2];
                }
            } else if current_type.starts_with("out") && current_type.len() > 3 {
                todo!()
            }
        }
        process_step(
            current_step_index,
            current_type,
            current_step_start,
            self.code.len(),
            current_rest,
        );

        let mut result_steps = vec![];
        for i in 1..steps.len() + 1 {
            result_steps.push(steps[&i].clone());
        }
        Steps {
            steps: result_steps,
            flags,
        }
    }
}

struct ErrorCommentsOnCode<'a>(&'a str, std::iter::Enumerate<std::str::Split<'a, &'a str>>);

impl Iterator for ErrorCommentsOnCode<'_> {
    type Item = String;
    fn next(&mut self) -> Option<Self::Item> {
        for (i, line) in &mut self.1 {
            if let Some(pos) = line.find("# E: ") {
                return Some(format!("{}:{}: error: {}", self.0, i + 1, &line[pos + 5..]));
            }
            if let Some(pos) = line.find("# N: ") {
                return Some(format!("{}:{}: note: {}", self.0, i + 1, &line[pos + 5..]));
            }
        }
        None
    }
}

struct TypeStuffReplacer();

impl Replacer for TypeStuffReplacer {
    fn replace_append(&mut self, _caps: &Captures<'_>, dst: &mut String) {
        if dst.ends_with("(got \"") || dst.ends_with(", expected \"") {
            dst.push_str("tuple")
        } else {
            dst.push_str("builtins.tuple")
        }
    }
}

fn main() {
    let mut project = zuban_python::Project::new(BASE_PATH.to_owned());

    let skipped = skipped();

    let files = find_mypy_style_files();
    let start = Instant::now();
    let mut full_count = 0;
    let mut ran_count = 0;
    let file_count = files.len();
    for file in files {
        let code = read_to_string(&file).unwrap();
        let code = REPLACE_COMMENTS.replace_all(&code, "");
        let stem = file.file_stem().unwrap().to_owned();
        let file_name = stem.to_str().unwrap();
        for case in mypy_style_cases(file_name, &code) {
            full_count += 1;
            if skipped.iter().any(|s| s.is_skip(&case.name)) {
                println!("Skipped: {}", case.name);
                continue;
            }
            case.run(&mut project);
            ran_count += 1;
        }
    }
    println!(
        "Ran {} of {} mypy-like tests in {} files; finished in {:.2}s",
        ran_count,
        full_count,
        file_count,
        start.elapsed().as_secs_f32(),
    );
}

fn mypy_style_cases<'a, 'b>(file_name: &'a str, code: &'b str) -> Vec<TestCase<'a, 'b>> {
    let mut cases = vec![];

    let mut add = |name, start, end| {
        cases.push(TestCase {
            file_name,
            name,
            code: &code[start..end],
        });
    };

    let mut start = None;
    let mut next_name = None;
    for capture in CASE.captures_iter(&code) {
        if let Some(start) = start {
            add(
                next_name.take().unwrap(),
                start,
                capture.get(0).unwrap().start(),
            );
        }
        next_name = Some(capture.get(1).unwrap().as_str().to_owned());
        start = Some(capture.get(0).unwrap().end())
    }

    add(
        next_name.unwrap_or_else(|| panic!("File without test cases: {:?}", file_name)),
        start.unwrap(),
        code.len(),
    );
    cases
}

fn get_base() -> PathBuf {
    // TODO windows, this slash probably makes problems...
    let mut base = PathBuf::from(file!().replace("zuban_python/", ""));
    assert!(base.pop());
    base
}

fn find_mypy_style_files() -> Vec<PathBuf> {
    let base = get_base();
    let mut entries = vec![];

    // Include local tests
    let mut path = base.clone();
    path.push("tests");

    entries.extend(
        read_dir(path)
            .unwrap()
            .map(|res| res.map(|e| e.path()).unwrap()),
    );

    // Include mypy tests
    for name in USE_MYPY_TEST_FILES {
        let mut path = base.clone();
        path.extend(["mypy", "test-data", "unit", name]);
        entries.push(path);
    }

    entries.sort();
    entries
}

#[derive(Debug)]
struct Skipped {
    name: String,
    start_star: bool,
    end_star: bool,
}

impl Skipped {
    fn is_skip(&self, name: &str) -> bool {
        if self.start_star && self.end_star {
            name.contains(&self.name)
        } else if self.start_star {
            name.ends_with(&self.name)
        } else if self.end_star {
            name.starts_with(&self.name)
        } else {
            self.name == name
        }
    }
}

fn skipped() -> Box<[Skipped]> {
    let mut skipped_path = get_base();
    skipped_path.push("skipped");
    let file = read_to_string(skipped_path).unwrap();

    file.trim()
        .split('\n')
        .map(|mut x| {
            let start_star = x.starts_with("*");
            let end_star = x.ends_with("*");
            if start_star {
                x = &x[1..];
            }
            if end_star {
                x = &x[..x.len() - 2]
            }
            Skipped {
                name: x.to_owned(),
                start_star,
                end_star,
            }
        })
        .collect()
}
