mod ide;

use std::{
    collections::HashMap,
    env,
    fs::{read_dir, read_to_string},
    path::{Path, PathBuf},
    process::ExitCode,
    sync::Arc,
    time::Instant,
};

use clap::{Command, CommandFactory as _, FromArgMatches as _, Parser};

use config::{DiagnosticConfig, Mode, ProjectOptions, PythonVersion, Settings, TypeCheckerFlags};
use ide::find_and_check_ide_tests;
use regex::{Captures, Regex, Replacer};
use test_utils::{Step, calculate_steps};
use utils::FastHashSet;
use vfs::{NormalizedPath, PathWithScheme, SimpleLocalFS, VfsHandler};
use zuban_python::{Project, RunCause};

const SKIP_MYPY_TEST_FILES: [&str; 27] = [
    // --allow-redefinition tests
    "check-redefine.test",
    // Python special features
    "check-formatting.test",
    "check-plugin-attrs.test",
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
const BASE_PATH_STR: &str = "/mypylike/";
#[cfg(target_os = "windows")]
const BASE_PATH_STR: &str = r"C:\\mypylike\";

thread_local! {
    static BASE_PATH: Arc<NormalizedPath> = {
        let local_fs = SimpleLocalFS::without_watcher();
        local_fs.normalize_rc_path(local_fs.unchecked_abs_path(BASE_PATH_STR))
    };
}

const MYPY_TEST_DATA_PACKAGES_FOLDER: &str = "tests/mypylike/mypy/test-data/packages/";
const OUR_TEST_DATA_PACKAGES_FOLDER: &str = "tests/mypylike/packages/";

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

    #[arg(long)]
    start_at: Option<String>,

    /// Runs only the tests for typechecking and not language server
    #[arg(long)]
    only_typecheck: bool,
    #[arg(long)]
    only_language_server: bool,

    #[arg(short = 'x')]
    stop_after_first_error: bool,
}

#[derive(Parser, Default)]
struct PerTestFlags {
    #[command(flatten)]
    cli: cli_args::Cli,

    // Maybe implement?
    #[arg(long)]
    local_partial_types: bool,
    #[arg(long)]
    no_local_partial_types: bool,
    #[arg(long)]
    disable_memoryview_promotion: bool,
    #[arg(long)]
    disable_bytearray_promotion: bool,
    #[arg(long)]
    warn_unused_ignores: bool,
    #[arg(long)]
    namespace_packages: bool,
    #[arg(long)]
    no_namespace_packages: bool,
    #[arg(long)]
    no_strict_bytes: bool,
    #[arg(long)]
    follow_imports: Option<String>,

    // Won't implement, Mypy internals
    #[arg(long)]
    no_sqlite_cache: bool,
    #[arg(long)]
    soft_error_limit: Option<isize>,
    #[arg(long)]
    fast_module_lookup: bool,
    #[arg(long)]
    force_union_syntax: bool,
    #[arg(long)]
    no_force_union_syntax: bool,
    #[arg(long)]
    cache_fine_grained: bool,
    #[arg(long)]
    no_incremental: bool,
    #[arg(long)]
    bazel: bool,
    #[arg(long)]
    enable_incomplete_feature: Option<String>,
    #[arg(long)]
    verbose: bool,
    #[arg(short)]
    package: Option<String>,

    // Our own
    #[arg(long)]
    no_typecheck: bool,
    #[arg(long)]
    only_language_server: bool,
    #[arg(long)]
    no_windows: bool,
    #[arg(long)]
    use_joins: bool,
    #[arg(long)]
    no_use_joins: bool,
    #[arg(long)]
    disallow_empty_bodies: bool,
    #[arg(long)]
    auto_mode: bool,
}

#[derive(Debug)]
struct TestCase<'name, 'code> {
    file_name: &'name str,
    name: String,
    code: &'code str,
    from_mypy_test_suite: bool,
}

impl TestCase<'_, '_> {
    fn initialize_flags<'p>(
        &self,
        projects: &'p mut ProjectsCache,
        local_fs: &SimpleLocalFS,
        mode: Option<Mode>,
        flags: PerTestFlags,
        steps: &[Step],
    ) -> (OwnedOrMut<'p, Project>, DiagnosticConfig) {
        let mut diagnostic_config = DiagnosticConfig {
            show_error_codes: false,
            ..Default::default()
        };
        let po = ProjectOptions::default_for_mode(mode.unwrap_or_else(|| Mode::Default));
        let mut config = po.flags;
        // TODO This appears to cause issues, because Mypy uses a custom typing.pyi that has
        // different argument types.
        //config.python_version = self.default_python_version();
        let mut settings = po.settings;
        let mut project_options = None;

        if let Some(mypy_ini_config) = steps[0].files.get("mypy.ini") {
            println!("Loading mypy.ini for {} ({})", self.name, self.file_name);
            let ini = cleanup_mypy_issues(mypy_ini_config).unwrap();
            let mut new = BASE_PATH.with(|base_path| {
                ProjectOptions::from_mypy_ini(
                    local_fs,
                    base_path,
                    base_path,
                    &ini,
                    &mut diagnostic_config,
                )
                .expect("Expected there to be no errors in the mypy.ini")
                .unwrap_or_else(ProjectOptions::mypy_default)
            });
            set_mypy_path(&mut new);
            config = std::mem::replace(&mut new.flags, config);
            settings = std::mem::replace(&mut new.settings, settings);
            project_options = Some(new);
        } else if let Some(pyproject_toml) = steps[0].files.get("pyproject.toml") {
            println!(
                "Loading pyproject.toml for {} ({})",
                self.name, self.file_name
            );
            let ini = cleanup_mypy_issues(pyproject_toml).unwrap();
            let mut new = BASE_PATH.with(|base_path| {
                ProjectOptions::from_pyproject_toml_only(
                    local_fs,
                    base_path,
                    base_path,
                    &ini,
                    &mut diagnostic_config,
                    mode,
                )
                .expect("Expected there to be no errors in the pyproject.toml")
                .unwrap_or_else(|| ProjectOptions::default_for_mode(settings.mode))
            });
            set_mypy_path(&mut new);
            config = std::mem::replace(&mut new.flags, config);
            settings = std::mem::replace(&mut new.settings, settings);
            project_options = Some(new);
        }

        // Appears mostly in pep561.test
        let first_line = self.code.split('\n').next().unwrap();
        if let Some(suffix) = first_line.strip_prefix("# pkgs:") {
            let current_dir = local_fs.current_dir();
            let mypy_folder = local_fs.join(&current_dir, MYPY_TEST_DATA_PACKAGES_FOLDER);
            let our_folder = local_fs.join(&current_dir, OUR_TEST_DATA_PACKAGES_FOLDER);
            settings.prepended_site_packages.extend(
                suffix
                    .split([';', ','])
                    .map(|s| {
                        [
                            local_fs.normalize_rc_path(local_fs.join(&mypy_folder, s.trim())),
                            local_fs.normalize_rc_path(local_fs.join(&our_folder, s.trim())),
                        ]
                        .into_iter()
                    })
                    .flatten(),
            );
        };

        match self.file_name {
            "check-errorcodes" => diagnostic_config.show_error_codes = true,
            "check-columns" => diagnostic_config.show_column_numbers = true,
            "check-recursive-types" => {
                // This feels very broken, but for now we disable these errors, because they don't feel
                // wrong, but Mypy does not have them.
                config.disabled_error_codes.push("used-before-def".into())
            }
            "check-modules-case" => {
                // These tests are checking for case insensitive file systems like macOS, Windows
                config.case_sensitive = false;
            }
            _ => {
                if self.file_name.starts_with("fine-grained") {
                    config.local_partial_types = true;
                }
            }
        }
        // This is simply for testing and mirrors how mypy does it.
        config.allow_empty_bodies =
            !self.name.ends_with("_no_empty") && self.file_name != "check-abstract";

        BASE_PATH.with(|base_path| {
            let current_dir = NormalizedPath::arc_to_abs_path(base_path.clone());
            cli_args::apply_flags_detailed(
                local_fs,
                &mut settings,
                &mut config,
                &mut diagnostic_config,
                current_dir.clone(),
                flags.cli,
                current_dir,
                None,
            );
        });

        macro_rules! set_flag {
            ($name:ident) => {
                if flags.$name {
                    config.$name = true;
                }
            };
        }

        set_flag!(local_partial_types);
        set_flag!(disable_bytearray_promotion);
        set_flag!(disable_memoryview_promotion);
        set_flag!(use_joins);
        if flags.no_use_joins {
            config.use_joins = false;
        }
        if flags.no_local_partial_types {
            config.local_partial_types = false;
        }
        if flags.disallow_empty_bodies {
            config.allow_empty_bodies = false;
        }

        let project = if let Some(mut project_options) = project_options {
            project_options.settings = settings;
            project_options.flags = config;
            OwnedOrMut::Owned(projects.try_to_reuse_project_parts(project_options))
        } else {
            OwnedOrMut::Mut(projects.get_mut(settings, config))
        };
        (project, diagnostic_config)
    }

    fn run(&self, projects: &mut ProjectsCache, mode: Mode) -> anyhow::Result<bool> {
        let steps = calculate_steps(Some(self.file_name), self.code);
        // Avoid parsing, because it's pretty slow and let's not do it if not strictly necessary.
        let flags = if steps.flags.is_empty() {
            PerTestFlags::default()
        } else {
            // We could use PerTestFlags::try_parse_from, but that's much slower, because it recreates
            // the Command each time.
            let matches = projects
                .command
                .try_get_matches_from_mut(std::iter::once("").chain(steps.flags.into_iter()))?;
            PerTestFlags::from_arg_matches(&matches)?
        };
        let steps = steps.steps;
        if flags.cli.mode().is_some_and(|m| m != mode)
            || flags.only_language_server && !matches!(projects.run_cause, RunCause::LanguageServer)
            || flags.no_windows && cfg!(windows)
            || flags.auto_mode && mode == Mode::Mypy
        {
            return Ok(false);
        }
        let local_fs = SimpleLocalFS::without_watcher();
        let no_typecheck = flags.no_typecheck;
        let (mut project, diagnostic_config) = self.initialize_flags(
            projects,
            &local_fs,
            (!flags.auto_mode).then_some(mode),
            flags,
            &steps,
        );

        let is_parse_test = self.file_name.starts_with("parse");
        let is_semanal_test = self.file_name.starts_with("semanal-");

        let mut result = Ok(true);
        let project = project.as_mut();
        for (i, step) in steps.iter().enumerate() {
            if cfg!(feature = "zuban_debug") {
                println!(
                    "\nTest: {}: Step {}/{}",
                    self.format(mode),
                    i + 1,
                    steps.len()
                );
            }
            let mut wanted = initialize_and_return_wanted_output(
                &local_fs,
                project,
                step,
                self.from_mypy_test_suite,
            );
            let mut ide_test_results: Vec<String> = vec![];
            if !self.from_mypy_test_suite {
                BASE_PATH.with(|base_path| {
                    let mut previously_checked = FastHashSet::default();
                    for step in steps.iter().take(i + 1).rev() {
                        for (path, code) in &step.files {
                            if !previously_checked.insert(path) {
                                continue;
                            }
                            find_and_check_ide_tests(
                                project,
                                base_path,
                                path,
                                code,
                                &mut ide_test_results,
                            );
                        }
                    }
                });
            }

            for path in &step.deletions {
                project
                    .close_in_memory_file(&base_path_join(&local_fs, path))
                    .unwrap_or_else(|_| {
                        project
                            .delete_directory_of_in_memory_files(&base_path_join(&local_fs, path))
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

            let diagnostics: Vec<_> = if no_typecheck {
                vec![]
            } else {
                project
                    .diagnostics()
                    .unwrap()
                    .issues
                    .iter()
                    .filter_map(|d| {
                        if is_semanal_test && !d.is_mypy_semanal_error() {
                            return None;
                        }
                        (!is_parse_test || d.mypy_error_code() == "syntax").then(|| {
                            let mut s = d.as_string(&diagnostic_config, None);
                            if s.starts_with("__main__.py:") {
                                s = s.replace("__main__.py:", "__main__:");
                            }
                            if cfg!(target_os = "windows") {
                                // Safety: OK because we only modify ASCII
                                let bytes = unsafe { s.as_bytes_mut() };
                                for line in bytes.split_mut(|c| *c == b'\n') {
                                    if let Some(colon) = line.iter().position(|c| *c == b':') {
                                        let to_change = &mut line[..colon];
                                        for b in to_change {
                                            if *b == b'\\' {
                                                *b = b'/'
                                            }
                                        }
                                    }
                                }
                            }
                            s
                        })
                    })
                    .collect()
            };

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
                .map(|s| {
                    if self.from_mypy_test_suite {
                        s.to_lowercase()
                    } else {
                        s.to_string()
                    }
                })
                .filter_map(temporarily_skip)
                .collect::<Vec<_>>();
            if actual_lines == [""] {
                actual_lines.pop();
            }
            // Add ide_test_results
            for r in &ide_test_results {
                if !actual.is_empty() && !actual.ends_with('\n') {
                    actual.push('\n');
                }
                actual.push_str(r);
                actual.push('\n');
            }
            actual_lines.extend(ide_test_results);

            actual_lines.sort();

            let mut wanted_cleaned_up: Vec<_> = wanted
                .iter()
                .map(|s| {
                    if self.from_mypy_test_suite {
                        // For now we want to compare lower cases, because mypy mixes up list[] and
                        // List[]
                        s.to_lowercase()
                    } else {
                        s.to_string()
                    }
                })
                .filter_map(temporarily_skip)
                .collect();
            wanted_cleaned_up.sort();

            if wanted_cleaned_up != actual_lines {
                // To check output only sort by filenames, which should be enough.
                wanted.sort_by_key(|line| line.split(':').next().unwrap().to_owned());

                let wanted = wanted.iter().fold(String::new(), |a, b| a + b + "\n");
                result = Err(anyhow::anyhow!(
                    "\nMismatch:\n\
                     Wanted lines: {wanted_cleaned_up:?}\n\n\
                     Actual lines: {actual_lines:?}\n\n\
                     Wanted:\n\
                     {wanted}\n\
                     Actual:\n\
                     {actual}\n\
                     in {} ({}): Step {}/{}",
                    &self.name,
                    self.file_name,
                    i + 1,
                    steps.len(),
                ));
                break;
            }
        }
        for step in &steps {
            for path in step.files.keys() {
                // We need to unload the whole directory, otherwise we might leave up namespace
                // packages for other tests.

                // Somehow all tests use `/` paths, and I haven't seen backslashes (for Windows)
                if path.contains('/') {
                    let before_slash = path.split('/').next().unwrap();
                    let _ = project.delete_directory_of_in_memory_files(&base_path_join(
                        &local_fs,
                        before_slash,
                    ));
                } else {
                    let _ = project.close_in_memory_file(&base_path_join(&local_fs, path));
                }
            }
        }
        result
    }

    fn format(&self, mode: Mode) -> String {
        format!(
            "{} ({}, {})",
            self.name,
            self.file_name,
            match mode {
                Mode::Mypy => "mypy-compatible",
                Mode::Default => "default",
            }
        )
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

fn initialize_and_return_wanted_output(
    local_fs: &SimpleLocalFS,
    project: &mut Project,
    step: &Step,
    from_mypy_test_suite: bool,
) -> Vec<String> {
    let mut wanted = step
        .out
        .trim()
        .split('\n')
        .filter_map(|mut s| {
            if from_mypy_test_suite {
                cleanup_mypy_issues(s)
            } else {
                if cfg!(target_os = "windows") {
                    s = s.trim_end_matches('\r')
                }
                Some(s.to_string())
            }
        })
        .collect::<Vec<_>>();

    if wanted == [""] {
        wanted.pop();
    }

    let mut sorted_files: Vec<_> = step.files.iter().collect();
    sorted_files.sort();
    for &(&path, &code) in &sorted_files {
        // ../ files are usually Mypy internals
        if ["mypy.ini", "pyproject.toml"].contains(&path) || path.starts_with("../") {
            continue;
        }
        let p = if path == "__main__.py" {
            "__main__"
        } else {
            path
        };
        add_inline_errors(&mut wanted, p, code, from_mypy_test_suite);
        // testAbstractClassSubclasses
        let p = base_path_join(local_fs, path);
        if let Some(parent) = maybe_parent(local_fs, code) {
            project
                .store_in_memory_file_with_parent(p, code.into(), &parent)
                .unwrap();
        } else {
            project.store_in_memory_file(p, code.into());
        }
    }
    for line in &mut wanted {
        replace_unions(line);
        replace_optional(line);
    }
    wanted
}

fn maybe_parent(local_fs: &SimpleLocalFS, code: &str) -> Option<PathWithScheme> {
    let parent = code.strip_prefix("# parent: ")?;
    let path = &parent[0..parent.find(['\n', '\r'])?];
    Some(base_path_join(local_fs, path))
}

fn add_inline_errors(wanted: &mut Vec<String>, path: &str, code: &str, from_mypy_test_suite: bool) {
    let lines: Box<_> = code.split('\n').collect();
    for (line_nr, column, mut type_, comment) in
        ErrorCommentsOnCode(&lines, lines.iter().enumerate())
    {
        for comment in comment.split(" # E: ") {
            for (i, mut comment) in comment.split(" # N: ").enumerate() {
                if i != 0 {
                    type_ = "note";
                }
                if comment == "\\" || comment == "\\\r" {
                    // Stuff like:
                    // # E: \
                    continue;
                }
                let mut add_comment = |comment: &str| {
                    if let Some(column) = column {
                        wanted.push(format!(
                            "{path}:{line_nr}:{column}: {type_}: {}",
                            comment.trim_end()
                        ))
                    } else {
                        wanted.push(format!("{path}:{line_nr}: {type_}: {}", comment.trim_end()))
                    }
                };
                if from_mypy_test_suite {
                    if let Some(comment) = cleanup_mypy_issues(comment) {
                        add_comment(&comment)
                    }
                } else {
                    if cfg!(target_os = "windows") {
                        comment = comment.trim_end_matches('\r')
                    }
                    if comment.ends_with(" \\") {
                        comment = &comment[..comment.len() - 2];
                    }
                    add_comment(comment)
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

fn calculate_filters(args: &[String]) -> Vec<&str> {
    let mut filters = vec![];
    for s in args.iter() {
        filters.push(s.as_str())
    }
    filters
}

struct ProjectsCache {
    command: Command,
    base_project: Option<Project>,
    base_version: PythonVersion,
    map: HashMap<(Settings, TypeCheckerFlags), Project>,
    run_cause: RunCause,
}

fn set_mypy_path(options: &mut ProjectOptions) {
    options.settings.add_global_packages_default = false;
    BASE_PATH.with(|base_path| {
        options.settings.mypy_path.push(base_path.clone());
    })
}

fn base_path_join(local_fs: &dyn VfsHandler, other: &str) -> PathWithScheme {
    PathWithScheme::with_file_scheme(
        BASE_PATH.with(|base_path| local_fs.normalize_rc_path(local_fs.join(base_path, other))),
    )
}

impl ProjectsCache {
    fn new(reuse_db: bool, run_cause: RunCause) -> Self {
        let mut po = ProjectOptions::mypy_default();
        let base_version = po.settings.python_version_or_default();
        po.settings.typeshed_path = Some(test_utils::typeshed_path());
        set_mypy_path(&mut po);
        Self {
            command: PerTestFlags::command(),
            base_project: reuse_db.then(|| Project::without_watcher(po, run_cause)),
            base_version,
            run_cause,
            map: Default::default(),
        }
    }

    fn get_mut(&mut self, mut settings: Settings, flags: TypeCheckerFlags) -> &mut Project {
        settings.typeshed_path = Some(test_utils::typeshed_path());
        let key = (settings, flags);
        if !self.map.contains_key(&key) {
            let mut options = ProjectOptions::new(key.0.clone(), key.1.clone());
            set_mypy_path(&mut options);
            // We can only reuse the project if the python version matches.
            let project = if key.0.python_version_or_default() == self.base_version {
                self.try_to_reuse_project_parts(options)
            } else {
                Project::without_watcher(options, self.run_cause)
            };
            self.map.insert(key.clone(), project);
        }
        self.map.get_mut(&key).unwrap()
    }

    fn try_to_reuse_project_parts(&mut self, mut options: ProjectOptions) -> Project {
        if let Some(base_project) = self.base_project.as_mut() {
            base_project.try_to_reuse_project_resources_for_tests(options)
        } else {
            options.settings.typeshed_path = Some(test_utils::typeshed_path());
            Project::without_watcher(options, self.run_cause)
        }
    }
}

enum OwnedOrMut<'a, T> {
    Owned(T),
    Mut(&'a mut T),
}

impl<'a, T> OwnedOrMut<'a, T> {
    pub fn as_mut(&mut self) -> &mut T {
        match self {
            OwnedOrMut::Owned(t) => t,
            OwnedOrMut::Mut(t) => t,
        }
    }
}

fn main() -> ExitCode {
    logging_config::setup_logging(None).unwrap();

    // Avoid the --, because that's the only way how we can accept flags like --foo like
    // cargo test mypy -- -- --foo. Otherwise libtest? complains, if we just use -- once.
    let cli_args = CliArgs::parse_from(env::args().filter(|arg| arg != "--"));
    let filters = calculate_filters(&cli_args.filters);

    let skipped = skipped();

    let files = find_mypy_style_files();

    let mut error_count = 0;
    if !cli_args.only_language_server {
        error_count += run(
            &cli_args,
            RunCause::TypeChecking,
            &files,
            &skipped,
            &filters,
        );
    }
    if !cli_args.only_typecheck && error_count == 0 {
        error_count += run(
            &cli_args,
            RunCause::LanguageServer,
            &files,
            &skipped,
            &filters,
        )
    }

    ExitCode::from((error_count > 0) as u8)
}

fn run(
    cli_args: &CliArgs,
    run_cause: RunCause,
    files: &[(bool, PathBuf)],
    skipped: &[Skipped],
    filters: &[&str],
) -> usize {
    let start = Instant::now();
    let mut projects = ProjectsCache::new(!cli_args.no_reuse_db, run_cause);
    let mut full_count = 0;
    let mut passed_count = 0;
    let mut error_count = 0;
    let file_count = files.len();
    let mut error_summary = String::new();
    let mut allowed_to_run_when_start_at = false;
    for (from_mypy_test_suite, file) in files {
        let code = read_to_string(file).unwrap();
        let code = REPLACE_COMMENTS.replace_all(&code, "");
        let stem = file.file_stem().unwrap().to_owned();
        let file_name = stem.to_str().unwrap();
        for case in mypy_style_cases(file_name, &code, *from_mypy_test_suite) {
            if !filters.is_empty()
                && !filters.contains(&&*case.name)
                && !filters.contains(&file_name)
            {
                continue;
            }
            if let Some(name) = &cli_args.start_at {
                if case.name == *name || file_name == name {
                    allowed_to_run_when_start_at = true;
                } else if !allowed_to_run_when_start_at {
                    continue;
                }
            }
            if skipped
                .iter()
                .any(|s| s.is_skip(case.file_name, &case.name) && !filters.contains(&&*case.name))
            {
                //println!("Skipped: {}", case.name);
                full_count += 1;
                continue;
            }
            let mut check = |result, mode| match result {
                Ok(ran) => {
                    passed_count += ran as usize;
                    full_count += ran as usize;
                }
                Err(err) => {
                    full_count += 1;
                    if cli_args.stop_after_first_error {
                        panic!("{err}")
                    } else {
                        error_summary += &case.format(mode);
                        error_summary += "\n";
                        error_count += 1;
                        println!("{err}")
                    }
                }
            };
            if !from_mypy_test_suite {
                // Run our own tests both with mypy-compatible and without it.
                check(case.run(&mut projects, Mode::Default), Mode::Default)
            }
            check(case.run(&mut projects, Mode::Mypy), Mode::Mypy);
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
         mypy-like tests in {file_count} files; finished in {:.2}s (cause={})",
        start.elapsed().as_secs_f32(),
        match run_cause {
            RunCause::TypeChecking => "type-checking",
            RunCause::LanguageServer => "language-server",
        }
    );
    error_count
}

fn mypy_style_cases<'a, 'b>(
    file_name: &'a str,
    code: &'b str,
    from_mypy_test_suite: bool,
) -> Vec<TestCase<'a, 'b>> {
    let mut cases = vec![];

    let mut add = |name, start, end| {
        cases.push(TestCase {
            file_name,
            name,
            code: &code[start..end],
            from_mypy_test_suite,
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
        if let Some(only_for_file) = self.only_for_file.as_ref()
            && file_name != only_for_file
        {
            return false;
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
