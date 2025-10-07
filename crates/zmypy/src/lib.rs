use std::env::VarError;
use std::process::ExitCode;
use std::{path::PathBuf, sync::Arc};

use colored::Colorize as _;
pub use config::DiagnosticConfig;
pub use zuban_python::Diagnostics;

use config::{ExcludeRegex, ProjectOptions, PythonVersion, find_cli_config};
use vfs::{AbsPath, NormalizedPath, SimpleLocalFS, VfsHandler};
use zuban_python::{Mode, Project};

use clap::Parser;

#[derive(Parser)]
pub struct Cli {
    // Additional options
    /// Enable or disable mypy compatibility. By default disabled and enabled if a Mypy config is found (inverse: --no-mypy-compatible)
    #[arg(long)]
    pub mypy_compatible: bool,
    #[arg(long)]
    pub no_mypy_compatible: bool,
    #[command(flatten)]
    pub mypy_options: MypyCli,
}

#[derive(Parser, Clone)]
pub struct MypyCli {
    // Running code:
    /// Regular expression to match file names, directory names or paths which mypy should ignore
    /// while recursively discovering files to check, e.g. --exclude '/setup\.py$'. May be
    /// specified more than once, eg. --exclude a --exclude b
    #[arg(long)]
    exclude: Vec<String>,
    /// This is mostly for testing, to test all possible files (there shouldn't be any crashes)
    #[arg(long, hide = true)]
    ignore_excludes_from_config: bool,
    #[arg(num_args = 0..)]
    files: Vec<String>,
    /*
    /// Type-check module; can repeat for more modules
    #[arg(short, long, hide = true)]
    module_todo_unimplemented: Vec<String>,
    /// Type-check package recursively; can be repeated
    #[arg(short, long, hide = true)]
    package_todo_unimplemented: Vec<String>,
    */
    // Config file
    /// Configuration file, must have a [mypy] section (defaults to mypy.ini, .mypy.ini, pyproject.toml, setup.cfg, ~/.config/mypy/config, ~/.mypy.ini)
    #[arg(long)]
    config_file: Option<PathBuf>,

    // Import discovery
    /// Silently ignore imports of missing modules
    #[arg(long)]
    ignore_missing_imports: bool,
    /// Typecheck modules without stubs or py.typed marker
    #[arg(long)]
    follow_untyped_imports: bool,

    // Platform configuration
    /// Type check code assuming it will be running on Python x.y
    #[arg(long)]
    python_version: Option<PythonVersion>,
    /// Specifies the path for a python executable (for example a virtual env)
    #[arg(long)]
    python_executable: Option<String>,
    /// Type check special-cased code for the given OS platform (defaults to sys.platform)
    #[arg(long)]
    platform: Option<String>,
    /// Additional variable to be considered True (may be repeated)
    #[arg(long, value_name = "NAME")]
    always_true: Vec<String>,
    /// Additional variable to be considered False (may be repeated)
    #[arg(long, value_name = "NAME")]
    always_false: Vec<String>,

    // Disallow dynamic typing:
    // --disallow-any-unimported Disallow Any types resulting from unfollowed imports
    // --disallow-any-expr       Disallow all expressions that have type Any
    /// Disallow functions that have Any in their signature after decorator transformation
    #[arg(long)]
    disallow_any_decorated: bool,
    #[arg(long)]
    allow_any_decorated: bool,
    /// Disallow explicit Any in type positions
    #[arg(long)]
    disallow_any_explicit: bool,
    #[arg(long)]
    allow_any_explicit: bool,
    /// Disallow usage of generic types that do not specify explicit type parameters (inverse: --allow-any-generics)
    #[arg(long)]
    disallow_any_generics: bool,
    #[arg(long)]
    allow_any_generics: bool,
    /// Disallow subclassing values of type 'Any' when defining classes (inverse: --allow-subclassing-any)
    #[arg(long)]
    disallow_subclassing_any: bool,
    #[arg(long)]
    allow_subclassing_any: bool,

    // Untyped definitions and calls:
    /// Disallow calling functions without type annotations from functions with type annotations (inverse: --allow-untyped-calls)
    #[arg(long)]
    disallow_untyped_calls: bool,
    #[arg(long)]
    allow_untyped_calls: bool,
    // --untyped-calls-exclude MODULE Disable --disallow-untyped-calls for functions/methods coming from specific package, module, or class
    /// Disallow defining functions without type annotations or with incomplete type annotations (inverse: --allow-untyped-defs)
    #[arg(long)]
    disallow_untyped_defs: bool,
    #[arg(long)]
    allow_untyped_defs: bool,
    /// Disallow defining functions with incomplete type annotations (while still allowing entirely unannotated definitions) (inverse: --allow-incomplete-defs)
    #[arg(long)]
    disallow_incomplete_defs: bool,
    #[arg(long)]
    allow_incomplete_defs: bool,
    /// Type check the interior of functions without type annotations (inverse: --no-check-untyped-defs)
    #[arg(long)]
    check_untyped_defs: bool,
    #[arg(long)]
    no_check_untyped_defs: bool,
    /// Disallow decorating typed functions with untyped decorators (inverse: --allow-untyped-decorators)
    #[arg(long)]
    disallow_untyped_decorators: bool,
    #[arg(long)]
    allow_untyped_decorators: bool,

    // None and Optional handling:
    /// Assume arguments with default values of None are Optional (inverse: --no-implicit-optional)
    #[arg(long)]
    implicit_optional: bool,
    #[arg(long)]
    no_implicit_optional: bool,
    /// Disable strict Optional checks (inverse: --strict-optional)
    #[arg(long)]
    no_strict_optional: bool,
    #[arg(long)]
    strict_optional: bool,

    // Configuring warnings:
    // --warn-redundant-casts    Warn about casting an expression to its inferred type (inverse: --no-warn-redundant-casts)
    // --warn-unused-ignores     Warn about unneeded '# type: ignore' comments (inverse: --no-warn-unused-ignores)
    /// Warn about functions that end without returning (inverse: --no-warn-no-return)
    #[arg(long)]
    warn_no_return: bool,
    #[arg(long)]
    no_warn_no_return: bool,
    /// Warn about returning values of type Any from non-Any typed functions (inverse: --no-warn-return-any)
    #[arg(long)]
    warn_return_any: bool,
    #[arg(long)]
    no_warn_return_any: bool,
    /// Warn about statements or expressions inferred to be unreachable (inverse: --no-warn-unreachable)
    #[arg(long)]
    warn_unreachable: bool,
    #[arg(long)]
    no_warn_unreachable: bool,

    // Miscellaneous strictness flags:
    /// Suppress toplevel errors caused by missing annotations (inverse: --disallow-untyped-globals)
    #[arg(long)]
    allow_untyped_globals: bool,
    #[arg(long)]
    disallow_untyped_globals: bool,
    /// Allow unconditional variable redefinition with a new type (inverse: --disallow-redefinition)
    #[arg(long)]
    allow_redefinition: bool,
    #[arg(long)]
    disallow_redefinition: bool,
    /// For now --allow-redefinition and --allow-redefinition-new are the same (inverse: --disallow-redefinition-new)
    #[arg(long)]
    allow_redefinition_new: bool,
    #[arg(long)]
    disallow_redefinition_new: bool,
    /// Treat imports as private unless aliased (inverse: --implicit-reexport)
    #[arg(long)]
    no_implicit_reexport: bool,
    #[arg(long)]
    implicit_reexport: bool,
    /// Prohibit equality, identity, and container checks for non-overlapping types (inverse: --no-strict-equality)
    #[arg(long)]
    strict_equality: bool,
    #[arg(long)]
    no_strict_equality: bool,
    /// Disable treating bytearray and memoryview as subtypes of bytes
    #[arg(long)]
    strict_bytes: bool,
    /// Enable additional checks that are technically correct but may be impractical in real code.
    /// For example, this prohibits partial overlap in TypedDict updates, and makes arguments
    /// prepended via Concatenate positional-only (inverse: --no-extra-checks)
    #[arg(long)]
    extra_checks: bool,
    #[arg(long)]
    no_extra_checks: bool,
    /// Strict mode; enables the following flags: --warn-unused-configs, --disallow-any-generics,
    /// --disallow-subclassing-any, --disallow-untyped-calls, --disallow-untyped-defs,
    /// --disallow-incomplete-defs, --check-untyped-defs, --disallow-untyped-decorators,
    /// --warn-redundant-casts, --warn-unused-ignores, --warn-return-any, --no-implicit-reexport,
    /// --strict-equality, --extra-checks
    #[arg(long)]
    strict: bool,
    /// Disable a specific error code
    #[arg(long, value_name = "NAME")]
    disable_error_code: Vec<String>,
    /// Enable a specific error code
    #[arg(long, value_name = "NAME")]
    enable_error_code: Vec<String>,

    // Configuring error messages:
    /// Show column numbers in error messages (inverse: --hide-column-numbers)
    #[arg(long)]
    show_column_numbers: bool,
    #[arg(long)]
    hide_column_numbers: bool,
    /// Show end line/end column numbers in error messages. This implies --show-column-numbers (inverse: --hide-error-end)
    #[arg(long)]
    show_error_end: bool,
    #[arg(long)]
    hide_error_end: bool,
    /// Show error codes in error messages (inverse: --hide-error-codes)
    #[arg(long)]
    show_error_codes: bool,
    #[arg(long)]
    hide_error_codes: bool,
    // --show-absolute-path Show absolute paths to files (inverse: --hide-absolute-path)
    /// Use visually nicer output in error messages: Use soft word wrap, show source code snippets,
    /// and show error location markers (inverse: --no-pretty)
    #[arg(long)]
    pretty: bool,
    #[arg(long)]
    no_pretty: bool,
    /// Avoid showing the summary for errors
    #[arg(long, hide = true)]
    error_summary: bool,
    #[arg(long)]
    no_error_summary: bool,
}

pub fn run(cli: Cli) -> ExitCode {
    /*
     * TODO renenable this after alpha in some form
    if let Err(err) = licensing::verify_license_in_config_dir() {
        eprintln!("{err}");
        return ExitCode::from(10);
    }
    */

    let current_dir = std::env::current_dir().expect("Expected a valid working directory");
    const CWD_ERROR: &str = "Expected valid unicode in working directory";
    let current_dir = current_dir.into_os_string().into_string().expect(CWD_ERROR);
    with_exit_code(cli, current_dir, None)
}

fn with_exit_code(
    cli: Cli,
    current_dir: String,
    typeshed_path: Option<Arc<NormalizedPath>>,
) -> ExitCode {
    with_diagnostics_from_cli(cli, current_dir, typeshed_path, |diagnostics, config| {
        let stdout = std::io::stdout();
        for diagnostic in diagnostics.issues.iter() {
            diagnostic
                .write_colored(&mut stdout.lock(), config)
                .unwrap()
        }
        if config.error_summary {
            if diagnostics.error_count() > 0 {
                println!("{}", diagnostics.summary().red().bold());
            } else {
                println!("{}", diagnostics.summary().green().bold());
            }
        }
        ExitCode::from((diagnostics.error_count() > 0) as u8)
    })
    .unwrap_or_else(|err| {
        eprintln!("{err}");
        ExitCode::from(2)
    })
}

pub fn with_diagnostics_from_cli<T>(
    cli: Cli,
    current_dir: String,
    typeshed_path: Option<Arc<NormalizedPath>>,
    callback: impl FnOnce(Diagnostics, &DiagnosticConfig) -> T,
) -> anyhow::Result<T> {
    tracing::info!("Checking in {current_dir}");
    let (mut project, diagnostic_config) =
        project_from_cli(cli, &current_dir, typeshed_path, |name| std::env::var(name));
    let diagnostics = project.diagnostics();
    Ok(callback(diagnostics?, &diagnostic_config))
}

fn project_from_cli(
    cli: Cli,
    current_dir: &str,
    typeshed_path: Option<Arc<NormalizedPath>>,
    lookup_env_var: impl Fn(&str) -> Result<String, VarError>,
) -> (Project, DiagnosticConfig) {
    let local_fs = SimpleLocalFS::without_watcher();
    let current_dir = local_fs.unchecked_abs_path(current_dir);
    let mut found = find_cli_config(
        &local_fs,
        &current_dir,
        cli.mypy_options.config_file.as_deref(),
        // Set the default to not mypy compatible, at least for now
        cli.mypy_compatible && !cli.no_mypy_compatible,
    )
    .unwrap_or_else(|err| panic!("Problem parsing Mypy config: {err}"));
    let mut options = found.project_options;
    if let Some(typeshed_path) = typeshed_path {
        options.settings.typeshed_path = Some(typeshed_path);
    }
    options
        .settings
        .try_to_apply_environment_variables(&local_fs, &current_dir, lookup_env_var);

    apply_flags(
        &local_fs,
        &mut options,
        &mut found.diagnostic_config,
        cli,
        current_dir,
        found.config_path.as_deref(),
    );

    (
        Project::new(Box::new(local_fs), options, Mode::LanguageServer),
        found.diagnostic_config,
    )
}

fn apply_flags(
    vfs_handler: &SimpleLocalFS,
    project_options: &mut ProjectOptions,
    diagnostic_config: &mut DiagnosticConfig,
    cli: Cli,
    current_dir: Arc<AbsPath>,
    config_path: Option<&AbsPath>,
) {
    if cli.mypy_compatible {
        project_options.settings.mypy_compatible = true;
    }
    if cli.no_mypy_compatible {
        project_options.settings.mypy_compatible = false;
    }
    apply_mypy_flags(
        vfs_handler,
        project_options,
        diagnostic_config,
        cli.mypy_options,
        current_dir,
        config_path,
    )
}

fn apply_mypy_flags(
    vfs_handler: &SimpleLocalFS,
    project_options: &mut ProjectOptions,
    diagnostic_config: &mut DiagnosticConfig,
    cli: MypyCli,
    current_dir: Arc<AbsPath>,
    config_path: Option<&AbsPath>,
) {
    macro_rules! apply {
        ($to:ident, $attr:ident, $inverse:ident) => {
            if cli.$attr {
                $to.$attr = true;
            }
            if cli.$inverse {
                $to.$attr = false;
            }
        };
    }
    let flags = &mut project_options.flags;
    if cli.strict {
        flags.enable_all_strict_flags();
    }
    if cli.strict_bytes {
        flags.enable_strict_bytes();
    }
    apply!(flags, strict_optional, no_strict_optional);
    apply!(flags, strict_equality, no_strict_equality);
    apply!(flags, implicit_optional, no_implicit_optional);
    apply!(flags, check_untyped_defs, no_check_untyped_defs);
    if cli.ignore_missing_imports {
        flags.ignore_missing_imports = true;
    }
    if cli.follow_untyped_imports {
        flags.follow_untyped_imports = true;
    }
    apply!(flags, disallow_untyped_defs, allow_untyped_defs);
    apply!(flags, disallow_untyped_calls, allow_untyped_calls);
    apply!(flags, disallow_untyped_decorators, allow_untyped_decorators);
    apply!(flags, disallow_any_generics, allow_any_generics);
    apply!(flags, disallow_any_decorated, allow_any_decorated);
    apply!(flags, disallow_any_explicit, allow_any_explicit);
    //apply!(disallow_any_unimported, allow_any_unimported);
    //apply!(disallow_any_expr, allow_any_expr);
    apply!(flags, disallow_subclassing_any, allow_subclassing_any);
    apply!(flags, disallow_incomplete_defs, allow_incomplete_defs);
    apply!(flags, allow_untyped_globals, disallow_untyped_globals);
    apply!(flags, warn_unreachable, no_warn_unreachable);
    //apply!(warn_redundant_casts, no_warn_redundant_casts);
    apply!(flags, warn_return_any, no_warn_return_any);
    apply!(flags, warn_no_return, no_warn_no_return);
    apply!(flags, no_implicit_reexport, implicit_reexport);
    apply!(flags, extra_checks, no_extra_checks);

    apply!(diagnostic_config, show_column_numbers, hide_column_numbers);
    apply!(diagnostic_config, show_error_end, hide_error_end);
    apply!(diagnostic_config, show_error_codes, hide_error_codes);
    apply!(diagnostic_config, pretty, no_pretty);
    apply!(diagnostic_config, error_summary, no_error_summary);

    apply!(flags, allow_redefinition, disallow_redefinition);
    if cli.allow_redefinition_new {
        flags.allow_redefinition = true;
    }
    if cli.disallow_redefinition_new {
        flags.allow_redefinition = false;
    }

    if cli.platform.is_some() {
        project_options.settings.platform = cli.platform;
    }
    if let Some(python_version) = cli.python_version {
        project_options.settings.python_version = Some(python_version);
    }
    if let Some(p) = cli.python_executable {
        project_options
            .settings
            .apply_python_executable(vfs_handler, &current_dir, config_path, &p)
            .expect("Error when applying --python-executable")
    }
    if let Some(p) = &project_options.settings.environment {
        tracing::info!("Checking the following environment: {p}");
    }
    if !cli.files.is_empty() {
        project_options
            .settings
            .set_files_or_directories_to_check(vfs_handler, &current_dir, config_path, cli.files)
            .expect("Need a valid glob path as a files argument");
    }
    tracing::info!(
        "Checking the following files: {:?}",
        &project_options.settings.files_or_directories_to_check
    );
    project_options
        .flags
        .enabled_error_codes
        .extend(cli.enable_error_code);
    project_options
        .flags
        .disabled_error_codes
        .extend(cli.disable_error_code);
    project_options
        .flags
        .always_true_symbols
        .extend(cli.always_true);
    project_options
        .flags
        .always_false_symbols
        .extend(cli.always_false);

    if cli.ignore_excludes_from_config {
        // This is for testing, so we can test all files
        project_options.flags.excludes.clear();
    }
    for r in cli.exclude {
        project_options
            .flags
            .excludes
            .push(ExcludeRegex::new(r).expect("Invalid --exclude regex"));
    }
    tracing::info!(
        "Found the following excludes: {:?}",
        project_options
            .flags
            .excludes
            .iter()
            .map(|e| &e.regex_str)
            .collect::<Vec<_>>()
    );

    project_options
        .settings
        .mypy_path
        .push(vfs_handler.normalize_rc_path(current_dir));
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use super::*;

    fn diagnostics_with_env_lookup(
        cli: Cli,
        directory: &str,
        lookup_env_var: impl Fn(&str) -> Result<String, VarError>,
    ) -> anyhow::Result<Vec<String>> {
        let (mut project, diagnostic_config) = project_from_cli(
            cli,
            directory,
            Some(test_utils::typeshed_path()),
            lookup_env_var,
        );
        let diagnostics = project.diagnostics();
        let mut diagnostics = diagnostics?
            .issues
            .iter()
            .map(|d| d.as_string(&diagnostic_config))
            .collect::<Vec<_>>();
        diagnostics.sort();
        Ok(diagnostics)
    }

    fn diagnostics(cli: Cli, directory: &str) -> Vec<String> {
        diagnostics_with_env_lookup(cli, directory, |_| Err(VarError::NotPresent)).unwrap()
    }

    fn expect_diagnostics_error(cli: Cli, directory: &str) -> String {
        diagnostics_with_env_lookup(cli, directory, |_| Err(VarError::NotPresent))
            .unwrap_err()
            .to_string()
    }

    #[test]
    fn test_diagnostics() {
        logging_config::setup_logging_for_tests();
        let test_dir = test_utils::write_files_from_fixture(
            r#"
            [file pyproject.toml]
            [tool.mypy]
            strict = true

            [file foo.py]
            1()
            def foo(x) -> int: return 1

            [file README]
            Test that readme's are not type checked
            "#,
            false,
        );
        let d = || diagnostics(Cli::parse_from(vec![""]), test_dir.path());

        const NOT_CALLABLE: &str = "foo.py:1: error: \"int\" not callable  [operator]";
        assert_eq!(
            d(),
            vec![
                NOT_CALLABLE.to_string(),
                "foo.py:2: error: Function is missing a type annotation for one or more arguments  [no-untyped-def]"
                    .to_string()
            ]
        );

        test_dir.remove_file("pyproject.toml");

        assert_eq!(d(), vec![NOT_CALLABLE.to_string()]);
    }

    #[test]
    fn test_pyproject_should_be_ignored_if_no_relevant_entry() {
        logging_config::setup_logging_for_tests();
        let test_dir = test_utils::write_files_from_fixture(
            r#"
            [file pyproject.toml]

            [file setup.cfg]
            [mypy]
            exclude = "foo.py"

            [file foo.py]
            1()
            def foo(x: str) -> int: return 1
            [file bar.py]
            def bar(x) -> None: ...
            "#,
            false,
        );
        let d = || diagnostics(Cli::parse_from(vec![""]), test_dir.path());

        const NOT_CALLABLE: &str = "foo.py:1: error: \"int\" not callable  [operator]";

        let empty: [&str; _] = [];
        assert_eq!(d(), empty);

        test_dir.write_file("pyproject.toml", "[tool.mypy]");

        assert_eq!(d(), [NOT_CALLABLE]);

        test_dir.write_file("pyproject.toml", "[tool.zuban]");
        assert_eq!(d(), empty);

        // The Zuban config can overwrite mypy settings.
        test_dir.write_file(
            "pyproject.toml",
            "[tool.zuban]\ndisallow_untyped_defs = true",
        );
        const MISSING_ANNOTATION: &str = "bar.py:1: error: Function is missing a type \
                                          annotation for one or more arguments  [no-untyped-def]";
        assert_eq!(d(), [MISSING_ANNOTATION]);

        // Using --config-file should disable all other config files and only use the one
        // specified.
        assert_eq!(
            diagnostics(
                Cli::parse_from(vec!["", "--config-file", "pyproject.toml"]),
                test_dir.path()
            ),
            [MISSING_ANNOTATION, NOT_CALLABLE]
        );

        // If both the zuban config and the mypy section are available in pyproject.toml, that file
        // overwrites everything else.
        test_dir.write_file(
            "pyproject.toml",
            "[tool.zuban]\ndisallow_untyped_defs = true\n[tool.mypy]",
        );
        assert_eq!(d(), [MISSING_ANNOTATION, NOT_CALLABLE]);

        // mypy.ini doesn't change that.
        test_dir.write_file("mypy.ini", "[mypy]\nexclude = \"foo.py\"");
        assert_eq!(d(), [MISSING_ANNOTATION, NOT_CALLABLE]);
    }

    #[test]
    fn test_path_argument() {
        logging_config::setup_logging_for_tests();
        let test_dir = test_utils::write_files_from_fixture(
            r#"

            [file foo.py]
            1()

            [file bar.py]
            1()

            "#,
            false,
        );
        let d = |cli_args: &[&str]| diagnostics(Cli::parse_from(cli_args), test_dir.path());

        const NOT_CALLABLE_FOO: &str = "foo.py:1: error: \"int\" not callable  [operator]";
        const NOT_CALLABLE_BAR: &str = "bar.py:1: error: \"int\" not callable  [operator]";
        // Relative paths
        assert_eq!(
            d(&["", "foo.py", "bar.py"]),
            vec![NOT_CALLABLE_BAR.to_string(), NOT_CALLABLE_FOO.to_string()]
        );
        assert_eq!(d(&["", "foo.py"]), vec![NOT_CALLABLE_FOO.to_string(),]);
        // Absolute path
        let foo_path = Path::new(test_dir.path()).join("foo.py");
        assert_eq!(
            d(&["", foo_path.to_str().unwrap()]),
            vec![NOT_CALLABLE_FOO.to_string(),]
        );

        // Now set a default path
        test_dir.write_file("mypy.ini", "[mypy]\nfiles = foo.py");
        assert_eq!(d(&[""]), vec![NOT_CALLABLE_FOO.to_string(),]);
        assert_eq!(d(&["", "bar.py"]), vec![NOT_CALLABLE_BAR.to_string(),]);
    }

    #[test]
    fn test_environment() {
        logging_config::setup_logging_for_tests();
        // We intentionally also test that dirs with dashes are also checked.
        let fixture = if cfg!(target_os = "windows") {
            r#"
            [file venv/Scripts/python.exe]

            [file venv/site-packages/foo.py]

            [file venv/site-packages/bar.py]
            1()

            [file m.py]
            import foo

            [file test-dir/n.py]
            import foo
            "#
        } else {
            r#"
            [file venv/bin/python]

            [file venv/lib/python3.12/site-packages/foo.py]

            [file venv/lib/python3.12/site-packages/bar.py]
            1()

            [file venv/src/baz/baz/__init__.py]
            # Installing with pip install -e works similar to this
            my_baz = 1

            [file m.py]
            import foo

            [file test-dir/n.py]
            import foo
            "#
        };
        let test_dir = test_utils::write_files_from_fixture(fixture, false);
        let d = |cli_args: &[&str]| diagnostics(Cli::parse_from(cli_args), test_dir.path());

        let err = "error: Cannot find implementation or library stub for module named \"foo\"  [import-not-found]";
        // No venv information should fail to import
        assert_eq!(
            d(&[""]),
            [
                format!("m.py:1: {err}"),
                format!("test-dir{}n.py:1: {err}", std::path::MAIN_SEPARATOR),
            ]
        );
        // venv information via --python-executable should work
        let empty: [&str; _] = [];
        assert_eq!(d(&["", "--python-executable", "venv/bin/python"]), empty);

        // venv information via $VIRTUAL_ENV
        let ds = diagnostics_with_env_lookup(Cli::parse_from([""]), test_dir.path(), |name| {
            match name == "VIRTUAL_ENV" {
                true => Ok("venv".to_string()),
                false => Err(VarError::NotPresent),
            }
        });
        assert_eq!(ds.unwrap(), empty);
    }

    #[test]
    fn test_files_glob() {
        logging_config::setup_logging_for_tests();
        let test_dir = test_utils::write_files_from_fixture(
            r#"
            [file foo/bar/mod1.py]
            1()

            [file foo/mod2.py]
            1()

            [file mod3.py]
            1()

            [file mypy.ini]
            [mypy]
            files = foo/*.py
            "#,
            false,
        );
        let d = |cli_args: &[&str]| diagnostics(Cli::parse_from(cli_args), test_dir.path());
        let expect_not_found = |cli_args: &[&str]| {
            expect_diagnostics_error(Cli::parse_from(cli_args), test_dir.path().into())
        };

        let err1 = format!(
            "foo{sep}bar{sep}mod1.py:1: error: \"int\" not callable  [operator]",
            sep = std::path::MAIN_SEPARATOR
        );
        let err2 = format!(
            "foo{}mod2.py:1: error: \"int\" not callable  [operator]",
            std::path::MAIN_SEPARATOR
        );
        let err3 = "mod3.py:1: error: \"int\" not callable  [operator]";

        assert_eq!(d(&[""]), [&*err2]);

        assert_eq!(d(&["", "foo/**/mod[1-9].py"]), [&*err1, &*err2]);
        assert_eq!(d(&["", "**/*.py"]), [&*err1, &*err2, err3]);
        assert_eq!(d(&["", "**/mod2.py"]), [&*err2]);
        assert_eq!(d(&["", "**/"]), [&*err1, &*err2, err3]);
        assert_eq!(d(&["", "**/mod?.py"]), [&*err1, &*err2, err3]);
        assert_eq!(d(&["", "*.py"]), [err3]);
        assert_eq!(d(&["", "foo"]), [&*err1, &*err2]);
        assert_eq!(d(&["", "./foo"]), [&*err1, &*err2]);
        assert_eq!(d(&["", "does-not-exist/../foo"]), [&*err1, &*err2]);
        // Same file twice
        assert_eq!(d(&["", "foo", "foo/mod2.py"]), [&*err1, &*err2]);

        expect_not_found(&["", "foo", "undefined-path"]);
        if cfg!(windows) {
            assert_eq!(
                expect_not_found(&["", "/foo/zuban/undefined-path"]),
                r"No Python files found to check for C:\foo\zuban\undefined-path"
            );
            assert_eq!(
                expect_not_found(&["", "/foo/zuban/undefined-path/*/baz/*"]),
                r"No Python files found to check in C:\foo\zuban\undefined-path\*\baz\*"
            );
        } else {
            assert_eq!(
                expect_not_found(&["", "/foo/zuban/undefined-path"]),
                "No Python files found to check for /foo/zuban/undefined-path"
            );
            assert_eq!(
                expect_not_found(&["", "/foo/zuban/undefined-path/*/baz/*"]),
                "No Python files found to check in /foo/zuban/undefined-path/*/baz/*"
            );
        }
    }

    #[test]
    fn test_files_relative_paths() {
        logging_config::setup_logging_for_tests();
        let mut project_options = ProjectOptions::mypy_default();
        let local_fs = SimpleLocalFS::without_watcher();
        let current_dir = local_fs.unchecked_abs_path("/a/b");
        let mut cli = Cli::parse_from([""]);
        cli.mypy_options.files = vec![
            "/a/b/baz.py".to_string(),
            "bla.py".to_string(),
            "/other/".to_string(),
            "/another".to_string(),
            "blub/bla/".to_string(),
            "blub/baz".to_string(),
            "blub/../not_in_blub".to_string(),
        ];
        apply_flags(
            &local_fs,
            &mut project_options,
            &mut DiagnosticConfig::default(),
            cli,
            current_dir.clone(),
            Some(current_dir.as_ref()),
        );
        let files: Vec<&str> = project_options
            .settings
            .files_or_directories_to_check
            .iter()
            .map(|p| p.as_str())
            .collect();
        if cfg!(target_os = "windows") {
            assert_eq!(
                files,
                vec![
                    r"\a\b\baz.py",
                    r"\a\b\bla.py",
                    r"\other",
                    r"\another",
                    r"\a\b\blub\bla",
                    r"\a\b\blub\baz",
                    r"\a\b\not_in_blub",
                ]
            )
        } else {
            assert_eq!(
                files,
                vec![
                    "/a/b/baz.py",
                    "/a/b/bla.py",
                    "/other",
                    "/another",
                    "/a/b/blub/bla",
                    "/a/b/blub/baz",
                    "/a/b/not_in_blub",
                ]
            )
        }
    }

    #[test]
    fn correct_exit_code() {
        logging_config::setup_logging_for_tests();
        let test_dir = test_utils::write_files_from_fixture(
            r#"
            [file with_note.py]
            reveal_type(1)

            [file empty.py]

            [file with_error.py]
            1()
            "#,
            false,
        );
        let c = |cli| {
            with_exit_code(
                cli,
                test_dir.path().into(),
                Some(test_utils::typeshed_path()),
            )
        };
        assert_eq!(c(Cli::parse_from(["", "with_note.py"])), ExitCode::SUCCESS);
        assert_eq!(c(Cli::parse_from(["", "empty.py"])), ExitCode::SUCCESS);
        assert_eq!(c(Cli::parse_from(["", "with_error.py"])), ExitCode::FAILURE);
    }

    #[test]
    fn no_python_files() {
        logging_config::setup_logging_for_tests();
        let test_dir = test_utils::write_files_from_fixture(
            r#"
            [file foo/no_py_ending]
            1()
            "#,
            false,
        );
        let d = |cli_args: &[&str]| diagnostics(Cli::parse_from(cli_args), test_dir.path());
        let err = |cli_args: &[&str]| {
            expect_diagnostics_error(Cli::parse_from(cli_args), test_dir.path())
        };

        assert_eq!(
            d(&["", "foo/no_py_ending"]),
            [format!(
                "foo{}no_py_ending:1: error: \"int\" not callable  [operator]",
                std::path::MAIN_SEPARATOR
            )]
        );
        assert!(err(&["", "foo/"]).starts_with("No Python files found to check for"));
        assert_eq!(err(&[""]), "No Python files found to check");
    }

    #[test]
    fn test_pyproject_with_mypy_config_dir_env_var() {
        // From https://github.com/zubanls/zubanls/issues/3
        logging_config::setup_logging_for_tests();
        let test_dir = test_utils::write_files_from_fixture(
            r#"
            [file pyproject.toml]
            [project]
            name = "hello_zuban"
            version = "0.1.0"

            requires-python = ">= 3.12"
            dependencies = []

            [project.scripts]
            hello-zuban = "hello_zuban:entry_point"

            [tool.mypy]
            mypy_path = "$MYPY_CONFIG_FILE_DIR/src"
            files = ["$MYPY_CONFIG_FILE_DIR/src"]
            strict = true

            [file src/hello_zuban/__init__.py]
            from hello_zuban.hello import X
            from src.hello_zuban.hello import Z

            x = X()

            [file src/hello_zuban/hello.py]
            Z = 1
            class X: pass
            1()

            "#,
            false,
        );
        let d = || diagnostics(Cli::parse_from(vec![""]), test_dir.path());

        if cfg!(target_os = "windows") {
            assert_eq!(
                d(),
                ["src\\hello_zuban\\hello.py:3: error: \"int\" not callable  [operator]"]
            );
        } else {
            assert_eq!(
                d(),
                ["src/hello_zuban/hello.py:3: error: \"int\" not callable  [operator]"]
            );
        }
    }

    #[test]
    fn test_editable_source() {
        logging_config::setup_logging_for_tests();
        // We intentionally also test that dirs with dashes are also checked.
        let test_dir = test_utils::write_files_from_fixture(
            if cfg!(windows) {
                r#"
                [file venv/bin/python]

                [file venv/pyvenv.cfg]
                include-system-site-packages = false
                version = 3.12.3

                [file venv/Lib/site-packages/frompth.pth]
                ../../frompth

                [file venv/frompth/my_frompth/__init__.py]
                x = 1
                [file venv/frompth/my_frompth/py.typed]

                [file venv/Lib/site-packages/foo.py]

                [file venv/src/baz/baz/__init__.py]
                # Installing with pip install -e works similar to this
                my_baz = 1

                [file venv/src/baz/baz/py.typed]

                [file m.py]
                from typing import assert_type
                import foo
                from baz import my_baz
                reveal_type(my_baz)

                from my_frompth import x
                assert_type(x, int)
                "#
            } else {
                r#"
                [file venv/bin/python]

                [file venv/pyvenv.cfg]
                include-system-site-packages = false
                version = 3.12.3

                [file venv/lib/python3.12/site-packages/frompth.pth]
                ../../../frompth

                [file venv/frompth/my_frompth/__init__.py]
                x = 1
                [file venv/frompth/my_frompth/py.typed]

                [file venv/lib/python3.12/site-packages/foo.py]

                [file venv/src/baz/baz/__init__.py]
                # Installing with pip install -e works similar to this
                my_baz = 1

                [file venv/src/baz/baz/py.typed]

                [file m.py]
                from typing import assert_type
                import foo
                from baz import my_baz
                reveal_type(my_baz)

                from my_frompth import x
                assert_type(x, int)

                "#
            },
            false,
        );
        let d = |cli_args: &[&str]| diagnostics(Cli::parse_from(cli_args), test_dir.path());

        assert_eq!(
            d(&["", "--python-executable", "venv/bin/python"]),
            ["m.py:4: note: Revealed type is \"builtins.int\""]
        );

        assert_eq!(
            d(&[""]),
            ["m.py:4: note: Revealed type is \"builtins.int\""]
        );
    }

    #[test]
    fn test_pythonpath() {
        logging_config::setup_logging_for_tests();

        let test_dir = test_utils::write_files_from_fixture(
            r#"
                [file pkg1/bar.py]
                import bar
                import pkg1
                import base
                import doesnotexist
                import baz

                [file pkg2/baz.py]

                [file base.py]

                [file main.py]
                import bar
                import pkg1
                import base
                import doesnotexist
                import baz
                "#,
            false,
        );

        let pth = |dir: &str| {
            Path::new(test_dir.path())
                .join(dir)
                .into_os_string()
                .into_string()
                .unwrap()
        };

        for (var, value) in [
            ("PYTHONPATH", format!("{}:{}", pth("pkg1"), pth("pkg2"))),
            ("MYPYPATH", format!("{}:{}", pth("pkg1"), pth("pkg2"))),
        ] {
            let d = |file: &str| {
                diagnostics_with_env_lookup(Cli::parse_from(&["", file]), test_dir.path(), |s| {
                    match s {
                        _ if s == var => Ok(value.clone()),
                        _ => Err(VarError::NotPresent),
                    }
                })
                .unwrap()
            };
            assert_eq!(
                d("main.py"),
                ["main.py:4: error: Cannot find implementation or library \
                     stub for module named \"doesnotexist\"  [import-not-found]"]
            );
            assert_eq!(
                d("pkg1/bar.py"),
                ["bar.py:4: error: Cannot find implementation or library \
                     stub for module named \"doesnotexist\"  [import-not-found]"]
            );
        }
    }
}
