use std::collections::HashMap;
use std::fs::{read_dir, read_to_string};
use std::path::PathBuf;
use std::time::Instant;

use regex::Regex;

const BASE_PATH: &str = "/mypylike/";

lazy_static::lazy_static! {
    static ref CASE: Regex = Regex::new(r"(?m)^\[case ([a-zA-Z_0-9-]+)\][ \t]*\n").unwrap();
    // This is how I found out about possible "commands in mypy, executed in
    // mypy/test-data/unit:
    // find . | grep check | xargs cat | grep '^\[' | grep -Ev '\[(out|case|file)'
    static ref CASE_PART: Regex = Regex::new(concat!(
        r"(?m)^\[(file|out\d*|builtins|typing|stale|rechecked|targets|delete)",
        r"(?: ([^\]]*))?\][ \t]*\n"
    )).unwrap();
}

#[derive(Default, Clone, Debug)]
struct Step<'code> {
    files: HashMap<&'code str, &'code str>,
    out: &'code str,
}

#[derive(Debug)]
struct TestCase<'name, 'code> {
    file_name: &'name str,
    name: String,
    code: &'code str,
}

impl<'name, 'code> TestCase<'name, 'code> {
    fn run(&self, project: &mut zuban_python::Project) {
        if cfg!(feature = "zuban_debug") {
            println!("\nStart test {}: {}", self.file_name, self.name);
        }
        let steps = self.calculate_steps();
        for (i, step) in steps.iter().enumerate() {
            if i != 0 && cfg!(feature = "zuban_debug") {
                println!("\nStep {} of {}", i + 1, self.name);
            }
            for (&path, &code) in &step.files {
                project.load_in_memory_file(BASE_PATH.to_owned() + path, code.to_owned());
            }
            let script =
                zuban_python::Script::new(project, Some(BASE_PATH.to_owned() + "main"), None);
            let diagnostics = script.diagnostics();
            let actual = diagnostics
                .iter()
                .fold(String::new(), |a, b| a + &b.as_string() + "\n");
            assert_eq!(
                actual.trim(),
                step.out.trim(),
                "\n\nError {}: {}\n\nWanted:\n{}Actual:\n{}\n",
                self.file_name,
                &self.name,
                step.out,
                actual,
            );
        }
        for step in &steps {
            for (path, _) in &step.files {
                #[allow(unused_must_use)]
                {
                    project.unload_in_memory_file(&(BASE_PATH.to_owned() + path));
                }
            }
        }
    }

    fn calculate_steps(&self) -> Vec<Step<'code>> {
        let mut steps = HashMap::<usize, Step>::new();
        steps.insert(1, Default::default());
        let mut current_step_index = 1;
        let mut current_type = "file";
        let mut current_rest = "main";
        let mut current_step_start = 0;

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
            if current_type == "file" {
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
        result_steps
    }
}

fn main() {
    let mut project = zuban_python::Project::new(BASE_PATH.to_owned());

    let files = find_mypy_style_files();
    let start = Instant::now();
    let mut full_count = 0;
    let mut ran_count = 0;
    let file_count = files.len();
    for file in files {
        let code = read_to_string(&file).unwrap();
        let stem = file.file_stem().unwrap().to_owned();
        let file_name = stem.to_str().unwrap();
        for case in mypy_style_cases(file_name, &code) {
            case.run(&mut project);
            ran_count += 1;
            full_count += 1;
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

fn find_mypy_style_files() -> Vec<PathBuf> {
    let mut base = PathBuf::from(file!().replace("zuban_python/", ""));
    assert!(base.pop());

    let mut entries = vec![];
    for p in ["from_mypy", "tests"] {
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
