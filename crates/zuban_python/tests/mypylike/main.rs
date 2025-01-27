use std::{
    collections::HashMap,
    env,
    fs::{read_dir, read_to_string},
    path::{Path, PathBuf},
    process::ExitCode,
    time::Instant,
};

use clap::Parser;

use config::{DiagnosticConfig, ProjectOptions, PythonVersion, Settings, TypeCheckerFlags};
use regex::{Captures, Regex, Replacer};
use test_utils::{calculate_steps, Step};
use zuban_python::Project;

const SKIP_MYPY_TEST_FILES: [&str; 28] = [
    // Narrowing tests
    "check-redefine.test",
    // Python special features
    "check-formatting.test",
    "check-plugin-attrs.test",
    // Python syntax
    "check-python310.test",
    // Mypy flag checking
    "cmdline.test",
    "cmdline.pyproject.test",
    // Maybe some day
    "check-reports.test",
    "reports.test",
    // Unfortunately probably not possible
    "check-custom-plugin.test",
    // Probably not relevant, because additional almost unrelated mypy features
    "stubgen.test",
    "typexport-basic.test",
    // dmypy suggest feature,
    // see https://mypy.readthedocs.io/en/stable/mypy_daemon.html#static-inference-of-annotations
    "fine-grained-suggest.test",
    // Inspect feature, see https://mypy.readthedocs.io/en/stable/mypy_daemon.html#static-inference-of-annotations
    "fine-grained-inspect.test",
    // Won't do, because they test mypy internals
    "check-incomplete-fixture.test",
    "check-native-int.test",
    "semanal-symtable.test",
    "daemon.test",
    "deps-classes.test",
    "deps-expressions.test",
    "deps-generics.test",
    "deps-statements.test",
    "deps.test",
    "deps-types.test",
    "diff.test",
    "outputjson.test",
    "errorstream.test",
    "merge.test",
    "ref-info.test",
];

#[cfg(not(target_os = "windows"))]
const BASE_PATH: &str = "/mypylike/";
#[cfg(target_os = "windows")]
const BASE_PATH: &str = r"C:\\mypylike\";

const MYPY_TEST_DATA_PACKAGES_FOLDER: &str = "tests/mypylike/mypy/test-data/packages/";

lazy_static::lazy_static! {
    static ref CASE: Regex = Regex::new(r"(?m)^\[case ([a-zA-Z_0-9-]+)\][ \t]*\r?\n").unwrap();
    static ref REPLACE_COMMENTS: Regex = Regex::new(r"(?m)^--.*$\r?\n").unwrap();
    static ref REPLACE_TUPLE: Regex = Regex::new(r"\bTuple\b").unwrap();
    static ref REPLACE_MYPY: Regex = Regex::new(r"`-?\d+").unwrap();
    static ref REPLACE_MYPY_ELLIPSIS: Regex = Regex::new(r#""ellipsis""#).unwrap();
    static ref REPLACE_MYPY_NO_RETURN: Regex = Regex::new(r"\bNoReturn\b").unwrap();
    static ref REPLACE_MYPY_SUBTYPE_NUMBERS: Regex = Regex::new(r"(<subclass[^<]+>)\d+").unwrap();
    static ref REPLACE_MYPY_SUBTYPE: Regex = Regex::new(r"\w+\.(<subclass|<callable subtype)").unwrap();
    static ref REPLACE_ESCAPES: Regex = Regex::new(r"(?m)^\\\[").unwrap();
    static ref REPLACE_MAIN: Regex = Regex::new(r"^main:").unwrap();
}

/// Simple program to greet a person
#[derive(Parser, Debug)]
#[command(about, long_about = None)]
struct CliArgs {
    /// Will not reuse the database, which disables a hack, but is slower.
    #[arg(long)]
    no_reuse_db: bool,

    /// Filter files or test names like "check-classes" or "testFooBar"
    #[arg(num_args = 0..)]
    filters: Vec<String>,

    #[arg(short = 'x')]
    stop_after_first_error: bool,
}

#[derive(Debug)]
struct TestCase<'name, 'code> {
    file_name: &'name str,
    name: String,
    code: &'code str,
}

impl TestCase<'_, '_> {
    fn run(&self, projects: &mut ProjectsCache, mypy_compatible: bool) -> Result<bool, String> {
        let steps = calculate_steps(Some(self.file_name), self.code);
        let mut diagnostics_config = DiagnosticConfig::default();

        if steps.flags.contains(&"--mypy-compatible") && !mypy_compatible
            || steps.flags.contains(&"--no-mypy-compatible") && mypy_compatible
        {
            return Ok(false);
        }
        let arg_after = |after_name| {
            let mut flag_iterator = steps.flags.iter();
            (flag_iterator.any(|x| *x == after_name))
                .then(|| flag_iterator.next().unwrap().to_string())
        };

        let mut config = TypeCheckerFlags::default();
        let mut settings = Settings::default();
        let mut project_options = None;
        if let Some(mypy_ini_config) = steps.steps[0].files.get("mypy.ini") {
            println!("Loading mypy.ini for {} ({})", self.name, self.file_name);
            let ini = cleanup_mypy_issues(mypy_ini_config).unwrap();
            let mut new = ProjectOptions::from_mypy_ini(&ini, &mut diagnostics_config).unwrap();
            set_mypy_path(&mut new);
            config = std::mem::replace(&mut new.flags, config);
            settings = std::mem::replace(&mut new.settings, settings);
            project_options = Some(new);
        }
        if let Some(pyproject_toml) = steps.steps[0].files.get("pyproject.toml") {
            println!(
                "Loading pyproject.toml for {} ({})",
                self.name, self.file_name
            );
            let ini = cleanup_mypy_issues(pyproject_toml).unwrap();
            let mut new =
                ProjectOptions::from_pyproject_toml(&ini, &mut diagnostics_config).unwrap();
            set_mypy_path(&mut new);
            config = std::mem::replace(&mut new.flags, config);
            settings = std::mem::replace(&mut new.settings, settings);
            project_options = Some(new);
        }

        if matches!(self.file_name, "pep561" | "imports") {
            let first_line = self.code.split('\n').next().unwrap();
            if let Some(suffix) = first_line.strip_prefix("# pkgs:") {
                settings.prepended_site_packages.extend(
                    suffix
                        .split([';', ','])
                        .map(|s| MYPY_TEST_DATA_PACKAGES_FOLDER.to_string() + s.trim()),
                );
            };
        }

        if self.file_name == "check-errorcodes" || steps.flags.contains(&"--show-error-codes") {
            diagnostics_config.show_error_codes = true;
        }
        if self.file_name == "check-columns" || steps.flags.contains(&"--show-column-numbers") {
            diagnostics_config.show_column_numbers = true;
        }
        if steps.flags.contains(&"--show-error-end") {
            diagnostics_config.show_error_end = true;
        }

        if steps.flags.contains(&"--strict") {
            config.enable_all_strict_flags();
        }
        let set_bool_flag = |change: &mut _, flag| {
            if steps.flags.contains(&flag) {
                *change = true;
            }
        };
        let set_reverse_bool_flag = |change: &mut _, flag| {
            if steps.flags.contains(&flag) {
                *change = false;
            }
        };
        set_bool_flag(&mut config.implicit_optional, "--implicit-optional");
        set_bool_flag(&mut config.check_untyped_defs, "--check-untyped-defs");
        set_bool_flag(&mut config.disallow_untyped_defs, "--disallow-untyped-defs");
        set_bool_flag(
            &mut config.disallow_untyped_calls,
            "--disallow-untyped-calls",
        );
        set_bool_flag(
            &mut config.disallow_untyped_decorators,
            "--disallow-untyped-decorators",
        );
        set_bool_flag(&mut config.disallow_any_generics, "--disallow-any-generics");
        set_bool_flag(
            &mut config.disallow_any_decorated,
            "--disallow-any-decorated",
        );
        set_bool_flag(&mut config.disallow_any_explicit, "--disallow-any-explicit");
        set_bool_flag(&mut config.disallow_any_expr, "--disallow-any-expr");
        set_bool_flag(
            &mut config.disallow_any_unimported,
            "--disallow-any-unimported",
        );
        set_bool_flag(
            &mut config.disallow_subclassing_any,
            "--disallow-subclassing-any",
        );
        set_bool_flag(
            &mut config.disallow_incomplete_defs,
            "--disallow-incomplete-defs",
        );
        set_bool_flag(&mut config.allow_untyped_globals, "--allow-untyped-globals");
        set_bool_flag(&mut config.warn_unreachable, "--warn-unreachable");
        set_bool_flag(&mut config.warn_redundant_casts, "--warn-redundant-casts");
        set_bool_flag(&mut config.warn_return_any, "--warn-return-any");
        set_bool_flag(&mut config.warn_no_return, "");
        set_bool_flag(&mut config.local_partial_types, "--local-partial-types");
        set_bool_flag(&mut config.no_implicit_reexport, "--no-implicit-reexport");
        set_bool_flag(
            &mut config.disable_bytearray_promotion,
            "--disable-bytearray-promotion",
        );
        set_bool_flag(
            &mut config.disable_memoryview_promotion,
            "--disable-memoryview-promotion",
        );
        set_bool_flag(&mut config.strict_equality, "--strict-equality");
        set_bool_flag(&mut config.extra_checks, "--extra-checks");
        set_bool_flag(
            &mut config.ignore_missing_imports,
            "--ignore-missing-imports",
        );
        set_reverse_bool_flag(&mut config.warn_no_return, "--no-warn-no-return");
        set_reverse_bool_flag(&mut config.strict_optional, "--no-strict-optional");
        set_reverse_bool_flag(&mut config.disallow_any_generics, "--allow-any-generics");
        // This is simply for testing and mirrors how mypy does it.
        config.allow_empty_bodies =
            !self.name.ends_with("_no_empty") && self.file_name != "check-abstract";
        settings.platform = arg_after("--platform");
        settings.mypy_compatible = mypy_compatible;

        if let Some(version) = arg_after("--python-version") {
            let x = &version[..1];
            let y = &version[2..];
            let error = "Expected version X.Y like 3.10";
            settings.python_version =
                PythonVersion::new(x.parse().expect(error), y.parse().expect(error));
        } else {
            // TODO This appears to cause issues, because Mypy uses a custom typing.pyi that has
            // different argument types.
            //config.python_version = self.default_python_version();
        }

        {
            let mut flag_iterator = steps.flags.iter();
            if flag_iterator.any(|x| *x == "--platform") {
                settings.platform = Some(flag_iterator.next().unwrap().to_string());
            }
        }

        let gather_list = |push_to: &mut Vec<_>, wanted_flag: &str| {
            let mut flag_iterator = steps.flags.iter();
            while let Some(flag) = flag_iterator.next() {
                if flag == &wanted_flag {
                    push_to.push(flag_iterator.next().unwrap().to_string());
                } else if let Some(rest) = flag.strip_prefix(wanted_flag) {
                    if let Some(name) = rest.strip_prefix('=') {
                        push_to.push(name.to_string())
                    }
                }
            }
        };
        gather_list(&mut config.always_true_symbols, "--always-true");
        gather_list(&mut config.always_false_symbols, "--always-false");
        gather_list(&mut config.enabled_error_codes, "--enable-error-code");
        gather_list(&mut config.disabled_error_codes, "--disable-error-code");

        if self.file_name == "check-recursive-types" {
            // This feels very broken, but for now we disable these errors, because they don't feel
            // wrong, but Mypy does not have them.
            config.disabled_error_codes.push("used-before-def".into());
        } else if self.file_name == "check-modules-case" {
            // These tests are checking for case insensitive file systems like macOS, Windows
            config.case_sensitive = false;
        } else if self.file_name.starts_with("fine-grained") {
            config.local_partial_types = true;
        }

        let mut tmp;
        let project = if let Some(mut project_options) = project_options {
            project_options.settings = settings;
            project_options.flags = config;
            tmp = projects.try_to_reuse_project_parts(project_options);
            &mut tmp
        } else {
            projects.get_mut(settings, config)
        };

        let is_parse_test = self.file_name.starts_with("parse");
        let is_semanal_test = self.file_name.starts_with("semanal-");

        let mut result = Ok(true);
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
            let mut wanted = initialize_and_return_wanted_output(project, step);

            for path in &step.deletions {
                project
                    .unload_in_memory_file(&(BASE_PATH.to_owned() + path))
                    .unwrap_or_else(|_| {
                        project
                            .delete_directory_of_in_memory_files(&(BASE_PATH.to_owned() + path))
                            .unwrap()
                    });
            }
            let default_panic = std::panic::take_hook();
            let cloned_name = self.name.clone();
            let cloned_file_name = self.file_name.to_string();
            std::panic::set_hook(Box::new(move |info| {
                println!("Panic in {cloned_name} ({cloned_file_name})");
                default_panic(info);
            }));

            let diagnostics: Vec<_> = project
                .diagnostics()
                .issues
                .iter()
                .filter_map(|d| {
                    if is_semanal_test && !d.is_mypy_semanal_error() {
                        return None;
                    }
                    (!is_parse_test || d.mypy_error_code() == "syntax")
                        .then(|| d.as_string(&diagnostics_config))
                })
                .collect();

            let _ = std::panic::take_hook();

            let mut actual = replace_annoyances(diagnostics.join("\n"));
            if is_parse_test && self.file_name == "parse-errors" {
                // For whatever reason mypy uses a different file name for these tests
                actual = actual.replace("__main__:", "file:")
            }
            if self.file_name.starts_with("pythoneval") {
                // pythoneval tests use different file names, because in mypy these are actually
                // created as files.
                // It uses two different ways for convenience...
                let name = self.name.strip_suffix("-xfail").unwrap_or(&self.name);
                let file_name_dot_py = format!("_{}.py:", name);
                let file_name_qualified = format!("_{}.", name);
                for line in wanted.iter_mut() {
                    *line = line.replace("_program.py:", "__main__:");
                    *line = line.replace(&file_name_dot_py, "__main__:");
                    // Since the file name can be in a reveal_type like _fooTest.A, but it should
                    // actually be __main__.A to be closer to what we do.
                    *line = line.replace(&file_name_qualified, "__main__.");
                }
            } else if self.file_name == "pep561" {
                let file_name_dot_py = format!("{}.py:", self.name);
                for line in wanted.iter_mut() {
                    *line = line.replace(&file_name_dot_py, "__main__:");
                }
            }
            let mut actual_lines = actual
                .trim()
                .split('\n')
                .map(|s| s.to_lowercase())
                .filter_map(temporarily_skip)
                .collect::<Vec<_>>();
            if actual_lines == [""] {
                actual_lines.pop();
            }
            actual_lines.sort();

            // For now we want to compare lower cases, because mypy mixes up list[] and List[]
            let mut wanted_lower: Vec<_> = wanted
                .iter()
                .map(|s| s.to_lowercase())
                .filter_map(temporarily_skip)
                .collect();
            wanted_lower.sort();

            // To check output only sort by filenames, which should be enough.
            wanted.sort_by_key(|line| line.split(':').next().unwrap().to_owned());

            if wanted_lower != actual_lines {
                let wanted = wanted.iter().fold(String::new(), |a, b| a + b + "\n");
                result = Err(format!(
                    "\nMismatch:\n\
                     Wanted lines: {wanted_lower:?}\n\n\
                     Actual lines: {actual_lines:?}\n\n\
                     Wanted:\n\
                     {wanted}\n\
                     Actual:\n\
                     {actual}\n\
                     in {} ({}): Step {}/{}",
                    &self.name,
                    self.file_name,
                    i + 1,
                    steps.steps.len(),
                ));
                break;
            }
        }
        for step in &steps.steps {
            for path in step.files.keys() {
                // We need to unload the whole directory, otherwise we might leave up namespace
                // packages for other tests.

                // Somehow all tests use `/` paths, and I haven't seen backslashes (for Windows)
                if path.contains('/') {
                    let before_slash = path.split('/').next().unwrap();
                    let _ = project.delete_directory_of_in_memory_files(
                        &(BASE_PATH.to_owned() + before_slash),
                    );
                } else {
                    let _ = project.unload_in_memory_file(&(BASE_PATH.to_owned() + path));
                }
            }
        }
        result
    }

    #[allow(dead_code)]
    fn default_python_version(&self) -> PythonVersion {
        match self.file_name {
            "check-python312" => PythonVersion::new(3, 12),
            "check-python311" => PythonVersion::new(3, 11),
            "check-python310" => PythonVersion::new(3, 10),
            "check-python39" => PythonVersion::new(3, 9),
            "check-python38" => PythonVersion::new(3, 8),
            _ => PythonVersion::new(3, 8),
        }
    }
}

fn replace_annoyances(s: String) -> String {
    s.replace("builtins.", "")
}

fn temporarily_skip(s: String) -> Option<String> {
    if s.contains(" overlap with incompatible return types")
        && s.contains("overloaded function signatures")
    {
        return None;
    }
    // This callable note is very weird and I'm confused when it appears and when not.
    if s.contains(".__call__\" has type") {
        return None;
    }
    if s.contains("note: types from \"numbers\" aren't supported for static type checking")
        || s.contains("note: consider using a protocol instead, such as typing.supportsfloat")
        || s.contains("https://peps.python.org/pep-0484/#the-numeric-tower")
        // Full note: This is likely because "one" has named arguments: "x". Consider marking them positional-only
        || s.contains("consider marking them positional-only")
    {
        return None;
    }
    Some(s)
}

fn initialize_and_return_wanted_output(project: &mut Project, step: &Step) -> Vec<String> {
    let mut wanted = step
        .out
        .trim()
        .split('\n')
        .filter_map(cleanup_mypy_issues)
        .collect::<Vec<_>>();

    if wanted == [""] {
        wanted.pop();
    }

    let mut sorted_files: Vec<_> = step.files.iter().collect();
    sorted_files.sort();
    for (&path, &code) in &sorted_files {
        if ["mypy.ini", "pyproject.toml"].contains(&path) {
            continue;
        }
        add_inline_errors(&mut wanted, path, code);
        // testAbstractClassSubclasses
        let p = BASE_PATH.to_owned() + path;
        project.load_in_memory_file(p.into(), code.into());
    }
    for line in &mut wanted {
        replace_unions(line);
        replace_optional(line);
    }
    wanted
}

fn add_inline_errors(wanted: &mut Vec<String>, path: &str, code: &str) {
    let lines: Box<_> = code.split('\n').collect();
    for (line_nr, column, mut type_, comment) in
        ErrorCommentsOnCode(&lines, lines.iter().enumerate())
    {
        for comment in comment.split(" # E: ") {
            for (i, comment) in comment.split(" # N: ").enumerate() {
                if i != 0 {
                    type_ = "note";
                }
                if let Some(comment) = cleanup_mypy_issues(comment) {
                    if let Some(column) = column {
                        wanted.push(format!(
                            "{path}:{line_nr}:{column}: {type_}: {}",
                            comment.trim_end()
                        ))
                    } else {
                        wanted.push(format!("{path}:{line_nr}: {type_}: {}", comment.trim_end()))
                    }
                }
            }
        }
    }
}

fn replace_unions(line: &mut String) {
    // Replaces Union[int, str] with int | str
    while let Some(index) = line.rfind("Union[") {
        let (end, commas) = find_end_bracket(&line[index..]);
        line.replace_range(index + end..index + end + 1, "");
        for i in commas.iter().rev() {
            line.replace_range(index + i..index + i + 1, " |");
        }
        line.replace_range(index..index + "Union[".len(), "");
    }
}

fn replace_optional(line: &mut String) {
    // Replaces Optional[int] -> int | None
    while let Some(index) = line.rfind("Optional[") {
        let s = &line[index..];
        if s.starts_with("Optional[...] must have exactly one type argument") {
            return;
        }
        let end = find_end_bracket(s).0;
        line.replace_range(index + end..index + end + 1, " | None");
        line.replace_range(index..index + "Optional[".len(), "");
    }
}

fn find_end_bracket(s: &str) -> (usize, Vec<usize>) {
    let mut brackets = 0;
    let mut commas = vec![];
    let mut end = 0;
    for (i, chr) in s.char_indices() {
        match chr {
            '[' | '(' | '{' => brackets += 1,
            ']' | ')' | '}' => {
                brackets -= 1;
                if brackets == 0 {
                    end = i;
                    break;
                }
            }
            ',' => {
                if brackets == 1 {
                    commas.push(i);
                }
            }
            _ => (),
        }
    }
    assert_eq!(brackets, 0);
    assert_ne!(end, 0);
    (end, commas)
}

struct ErrorCommentsOnCode<'a>(
    &'a [&'a str],
    std::iter::Enumerate<std::slice::Iter<'a, &'a str>>,
);

impl Iterator for ErrorCommentsOnCode<'_> {
    type Item = (usize, Option<usize>, &'static str, String);
    fn next(&mut self) -> Option<Self::Item> {
        for (i, line) in &mut self.1 {
            let was_exception = line.find("# E:");
            if let Some(pos) = was_exception.or_else(|| line.find("# N:")) {
                let mut backslashes = 0;
                if line.trim_start().starts_with("#") {
                    for i in (0..i).rev() {
                        if !(self.0[i].trim_end_matches('\r').ends_with('\\')) {
                            break;
                        }
                        backslashes += 1;
                    }
                }
                // Get rid of # E:25: Foo
                let mut rest = &line[pos + 4..];
                let first = rest.split(':').next().unwrap();
                let column: Option<usize> = first.parse().ok();
                if column.is_some() {
                    rest = &rest[first.len() + 1..];
                }

                return Some((
                    i + 1 - backslashes,
                    column,
                    match was_exception {
                        Some(_) => "error",
                        None => "note",
                    },
                    rest[1..].to_string(),
                ));
            }
        }
        None
    }
}
fn cleanup_mypy_issues(mut s: &str) -> Option<String> {
    if s.contains("See https://mypy.readthedocs.io/en/stable/running_mypy.html#missing-imports") {
        return None;
    }
    if s.contains("\" defined here")
        || s.contains("Flipping the order of overloads will fix this error")
        || s.contains("Maybe you forgot to use \"await\"?")
    {
        // TODO we might not want to skip this note in the future.
        return None;
    }
    if cfg!(target_os = "windows") {
        s = s.trim_end_matches('\r')
    }

    if s.ends_with(" \\") {
        s = &s[..s.len() - 2];
    }
    let s = REPLACE_TUPLE.replace_all(s, TypeStuffReplacer());
    let s = REPLACE_MYPY.replace_all(&s, "");
    // Mypy has a bit of a different handling for ellipsis when reading it from typeshed.
    let s = REPLACE_MYPY_ELLIPSIS.replace_all(&s, "\"EllipsisType\"");
    let s = REPLACE_MYPY_NO_RETURN.replace_all(&s, "Never");
    let s = REPLACE_MYPY_SUBTYPE_NUMBERS.replace_all(&s, "$1");
    let s = REPLACE_MYPY_SUBTYPE.replace_all(&s, "$1");
    let s = REPLACE_ESCAPES.replace_all(&s, "[");
    let s = REPLACE_MAIN.replace(&s, "__main__:");
    Some(replace_annoyances(s.replace("tmp/", "")))
}

struct TypeStuffReplacer();

impl Replacer for TypeStuffReplacer {
    fn replace_append(&mut self, _caps: &Captures<'_>, dst: &mut String) {
        if dst.ends_with("(got \"")
            || dst.ends_with(", expected \"")
            || dst.ends_with("has type \"")
        {
            dst.push_str("tuple")
        } else {
            dst.push_str("builtins.tuple")
        }
    }
}

fn calculate_filters(args: Vec<String>) -> Vec<String> {
    let mut filters = vec![];
    for s in args.into_iter().skip(1) {
        if s != "mypy" {
            filters.push(s)
        }
    }
    filters
}

struct ProjectsCache {
    base_project: Option<Project>,
    map: HashMap<(Settings, TypeCheckerFlags), Project>,
}

fn set_mypy_path(options: &mut ProjectOptions) {
    for path in options.settings.mypy_path.iter_mut() {
        if !path.starts_with(MYPY_TEST_DATA_PACKAGES_FOLDER) {
            // Mypy has a kind of weird way how they deal with tmp/
            *path = BASE_PATH.to_owned() + path;
        }
    }
    options.settings.mypy_path.push(BASE_PATH.into());
}

impl ProjectsCache {
    fn new(reuse_db: bool) -> Self {
        let mut po = ProjectOptions::default();
        po.settings.typeshed_path = Some(test_utils::typeshed_path());
        set_mypy_path(&mut po);
        Self {
            base_project: reuse_db.then(|| Project::without_watcher(po)),
            map: Default::default(),
        }
    }

    fn get_mut(&mut self, mut settings: Settings, flags: TypeCheckerFlags) -> &mut Project {
        settings.typeshed_path = Some(test_utils::typeshed_path());
        let key = (settings, flags);
        if !self.map.contains_key(&key) {
            let mut options = ProjectOptions::new(key.0.clone(), key.1.clone());
            set_mypy_path(&mut options);
            let project = self.try_to_reuse_project_parts(options);
            self.map.insert(key.clone(), project);
        }
        self.map.get_mut(&key).unwrap()
    }

    fn try_to_reuse_project_parts(&mut self, options: ProjectOptions) -> Project {
        if let Some(base_project) = self.base_project.as_mut() {
            base_project.try_to_reuse_project_resources_for_tests(options)
        } else {
            Project::without_watcher(options)
        }
    }
}

fn main() -> ExitCode {
    // Avoid the --, because that's the only way how we can accept flags like --foo like
    // cargo test mypy -- -- --foo. Otherwise libtest? complains, if we just use -- once.
    let cli_args = CliArgs::parse_from(env::args().filter(|arg| arg != "--"));
    let filters = calculate_filters(cli_args.filters);

    let skipped = skipped();

    let files = find_mypy_style_files();
    let start = Instant::now();
    let mut projects = ProjectsCache::new(!cli_args.no_reuse_db);
    let mut full_count = 0;
    let mut passed_count = 0;
    let mut error_count = 0;
    let file_count = files.len();
    let mut error_summary = String::new();
    for (from_mypy_test_suite, file) in files {
        let code = read_to_string(&file).unwrap();
        let code = REPLACE_COMMENTS.replace_all(&code, "");
        let stem = file.file_stem().unwrap().to_owned();
        let file_name = stem.to_str().unwrap();
        for case in mypy_style_cases(file_name, &code) {
            if !filters.is_empty()
                && !filters.contains(&case.name)
                && !filters.iter().any(|s| s == file_name)
            {
                continue;
            }
            if skipped
                .iter()
                .any(|s| s.is_skip(case.file_name, &case.name) && !filters.contains(&case.name))
            {
                //println!("Skipped: {}", case.name);
                full_count += 1;
                continue;
            }
            let mut check = |result| match result {
                Ok(ran) => {
                    passed_count += ran as usize;
                    full_count += ran as usize;
                }
                Err(err) => {
                    full_count += 1;
                    if cli_args.stop_after_first_error {
                        panic!("{err}")
                    } else {
                        error_summary += &format!("{} ({})\n", case.name, case.file_name);
                        error_count += 1;
                        println!("{err}")
                    }
                }
            };
            if !from_mypy_test_suite {
                // Run our own tests both with mypy-compatible and without it.
                check(case.run(&mut projects, from_mypy_test_suite))
            }
            check(case.run(&mut projects, true));
        }
    }
    if error_count > 0 {
        println!("\nError summary:");
        println!("{error_summary}");
    }
    let error_s = match error_count {
        1 => "",
        _ => "s",
    };
    println!(
        "Passed {passed_count} of {full_count} ({error_count} error{error_s}) \
         mypy-like tests in {file_count} files; finished in {:.2}s",
        start.elapsed().as_secs_f32(),
    );
    ExitCode::from((error_count > 0) as u8)
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
    for capture in CASE.captures_iter(code) {
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
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("mypylike")
}

fn find_mypy_style_files() -> Vec<(bool, PathBuf)> {
    let base = get_base();

    // Include local tests
    let mut path = base.clone();
    path.push("tests");

    let mut our_own_tests: Vec<_> = read_dir(path)
        .unwrap()
        .map(|res| (false, res.unwrap().path()))
        .filter(|(_, p)| {
            p.extension()
                .is_some_and(|ext| ext.to_str().unwrap() == "test")
        })
        .collect();

    our_own_tests.sort();

    let mut mypy_test_path = base;
    mypy_test_path.extend(["mypy", "test-data", "unit"]);
    // Include mypy tests
    let mut entries: Vec<_> = read_dir(mypy_test_path)
        .unwrap()
        .filter_map(|res| {
            let entry = res.unwrap();
            let name = entry.file_name().into_string().unwrap();
            if !name.ends_with(".test") || SKIP_MYPY_TEST_FILES.contains(&name.as_str()) {
                None
            } else {
                Some((true, entry.path()))
            }
        })
        .collect();

    entries.sort();
    entries.extend(our_own_tests);
    entries
}

#[derive(Debug)]
struct Skipped {
    name: String,
    only_for_file: Option<String>,
    start_star: bool,
    end_star: bool,
}

impl Skipped {
    fn is_skip(&self, file_name: &str, name: &str) -> bool {
        if let Some(only_for_file) = self.only_for_file.as_ref() {
            if file_name != only_for_file {
                return false;
            }
        }
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
        .filter(|line| !line.starts_with('#'))
        .map(|mut x| {
            if cfg!(target_os = "windows") {
                x = x.trim_end_matches('\r')
            }
            let start_star = x.starts_with('*');
            let end_star = x.ends_with('*');
            if start_star {
                x = &x[1..];
            }
            if end_star {
                x = &x[..x.len() - 1]
            }
            let mut split_by_colon = x.split(':');
            let first = split_by_colon.next().unwrap();
            let mut only_for_file = None;
            if let Some(rest) = split_by_colon.next() {
                assert_eq!(split_by_colon.next(), None);
                only_for_file = Some(first.into());
                x = rest;
            }

            Skipped {
                name: x.to_owned(),
                only_for_file,
                start_star,
                end_star,
            }
        })
        .collect()
}
