use std::path::PathBuf;
use std::process::ExitCode;

use config::{find_cli_config, DiagnosticConfig, ExcludeRegex, ProjectOptions, PythonVersion};
use vfs::{AbsPath, GlobAbsPath, LocalFS, VfsHandler};
use zuban_python::Project;

use clap::Parser;

#[derive(Parser)]
#[command(version, about)]
pub struct Cli {
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
    /// Type-check module; can repeat for more modules
    #[arg(short, long, hide = true)]
    module_todo_unimplemented: Vec<String>,
    /// Type-check package recursively; can be repeated
    #[arg(short, long, hide = true)]
    package_todo_unimplemented: Vec<String>,

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
    disallow_allow_untyped_globals: bool,
    //allow_redefinition:      Allow unconditional variable redefinition with a new type (inverse: --disallow-redefinition)
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

    // Additional options
    #[arg(long, hide = true)]
    no_mypy_compatible: bool,
}

pub fn run(cli: Cli) -> ExitCode {
    if let Err(err) = licensing::verify_license_in_config_dir() {
        eprintln!("{err}");
        return ExitCode::from(10);
    }

    let current_dir = std::env::current_dir().expect("Expected a valid working directory");
    const CWD_ERROR: &str = "Expected valid unicode in working directory";
    let current_dir = current_dir.into_os_string().into_string().expect(CWD_ERROR);

    run_with_cli(cli, current_dir, None)
}

pub fn run_with_cli(
    cli: Cli,
    current_dir: String,
    typeshed_path: Option<Box<AbsPath>>,
) -> ExitCode {
    tracing::info!("Checking in {current_dir}");
    let (mut project, diagnostic_config) =
        project_from_cli(cli, current_dir, typeshed_path, |name| {
            std::env::var(name).ok()
        });
    let diagnostics = project.diagnostics();
    for diagnostic in diagnostics.issues.iter() {
        println!("{}", diagnostic.as_string(&diagnostic_config))
    }
    let had_diagnostics = !diagnostics.issues.is_empty();
    let s_if_plural = |n| match n {
        1 => "",
        _ => "s",
    };
    if had_diagnostics {
        println!(
            "Found {e} error{e_s} in {fwe} file{fwe_s} (checked {checked} source file{checked_s})",
            e = diagnostics.issues.len(),
            e_s = s_if_plural(diagnostics.issues.len()),
            fwe = diagnostics.files_with_errors,
            fwe_s = s_if_plural(diagnostics.files_with_errors),
            checked = diagnostics.checked_files,
            checked_s = s_if_plural(diagnostics.checked_files),
        )
    } else {
        println!(
            "Success: no issues found in {checked} source file{checked_s}",
            checked = diagnostics.checked_files,
            checked_s = s_if_plural(diagnostics.checked_files),
        )
    }
    ExitCode::from(had_diagnostics as u8)
}

fn project_from_cli(
    cli: Cli,
    current_dir: String,
    typeshed_path: Option<Box<AbsPath>>,
    lookup_env_var: impl Fn(&str) -> Option<String>,
) -> (Project, DiagnosticConfig) {
    let local_fs = LocalFS::without_watcher();
    let current_dir = local_fs.unchecked_abs_path(current_dir);
    let (mut options, mut diagnostic_config) =
        find_cli_config(&local_fs, &current_dir, cli.config_file.as_deref())
            .unwrap_or_else(|err| panic!("Problem parsing Mypy config: {err}"));
    options.settings.mypy_compatible = true;
    if let Some(typeshed_path) = typeshed_path {
        options.settings.typeshed_path = Some(typeshed_path);
    }
    if options.settings.environment.is_none() {
        options.settings.environment =
            lookup_env_var("VIRTUAL_ENV").map(|v| local_fs.absolute_path(&current_dir, v))
    }

    apply_flags(
        &local_fs,
        &mut options,
        &mut diagnostic_config,
        cli,
        current_dir,
    );

    (Project::new(Box::new(local_fs), options), diagnostic_config)
}

fn apply_flags(
    vfs_handler: &LocalFS,
    project_options: &mut ProjectOptions,
    diagnostic_config: &mut DiagnosticConfig,
    cli: Cli,
    current_dir: Box<AbsPath>,
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
    apply!(flags, allow_untyped_globals, disallow_allow_untyped_globals);
    apply!(flags, warn_unreachable, no_warn_unreachable);
    //apply!(warn_redundant_casts, no_warn_redundant_casts);
    apply!(flags, warn_return_any, no_warn_return_any);
    apply!(flags, warn_no_return, no_warn_no_return);
    apply!(flags, no_implicit_reexport, implicit_reexport);
    apply!(flags, extra_checks, no_extra_checks);

    apply!(diagnostic_config, show_column_numbers, hide_column_numbers);
    apply!(diagnostic_config, show_error_end, hide_error_end);
    apply!(diagnostic_config, show_error_codes, hide_error_codes);

    if cli.no_mypy_compatible {
        project_options.settings.mypy_compatible = false;
    }

    if cli.platform.is_some() {
        project_options.settings.platform = cli.platform;
    }
    if let Some(python_version) = cli.python_version {
        project_options.settings.python_version = python_version;
    }
    if let Some(p) = cli.python_executable {
        let p = vfs_handler.absolute_path(&current_dir, p);
        project_options
            .settings
            .apply_python_executable(vfs_handler, &p)
            .expect("Error when applying --python-executable")
    }
    if let Some(p) = &project_options.settings.environment {
        tracing::info!("Checking the following environment: {p}");
    }
    if !cli.files.is_empty() {
        project_options.settings.files_or_directories_to_check = cli
            .files
            .into_iter()
            .map(|p| {
                GlobAbsPath::new(vfs_handler, &current_dir, p)
                    .expect("Need a valid glob path as a files argument")
            })
            .collect();
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

    // TODO MYPYPATH=$MYPYPATH:mypy-stubs
    project_options.settings.mypy_path.push(current_dir);
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use super::*;

    fn diagnostics_with_env_lookup(
        cli: Cli,
        directory: &str,
        lookup_env_var: impl Fn(&str) -> Option<String>,
    ) -> Vec<String> {
        let (mut project, diagnostic_config) = project_from_cli(
            cli,
            directory.to_string(),
            Some(test_utils::typeshed_path()),
            lookup_env_var,
        );
        let diagnostics = project.diagnostics();
        let mut diagnostics = diagnostics
            .issues
            .iter()
            .map(|d| d.as_string(&diagnostic_config))
            .collect::<Vec<_>>();
        diagnostics.sort();
        diagnostics
    }

    fn diagnostics(cli: Cli, directory: &str) -> Vec<String> {
        diagnostics_with_env_lookup(cli, directory, |_| None)
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

        const NOT_CALLABLE: &str = "foo.py:1: error: \"int\" not callable";
        assert_eq!(
            d(),
            vec![
                NOT_CALLABLE.to_string(),
                "foo.py:2: error: Function is missing a type annotation for one or more arguments"
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
            def foo(x) -> int: return 1
            "#,
            false,
        );
        let d = || diagnostics(Cli::parse_from(vec![""]), test_dir.path());

        const NOT_CALLABLE: &str = "foo.py:1: error: \"int\" not callable";

        assert!(d().is_empty());

        test_dir.write_file("pyproject.toml", "[tool.mypy]");

        assert_eq!(d(), vec![NOT_CALLABLE.to_string()]);
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

        const NOT_CALLABLE_FOO: &str = "foo.py:1: error: \"int\" not callable";
        const NOT_CALLABLE_BAR: &str = "bar.py:1: error: \"int\" not callable";
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
        let test_dir = test_utils::write_files_from_fixture(
            r#"
            [file venv/bin/python]

            [file venv/lib/python3.12/site-packages/foo.py]

            [file venv/lib/python3.12/site-packages/bar.py]
            1()

            [file m.py]
            import foo

            [file test-dir/n.py]
            import foo
            "#,
            false,
        );
        let d = |cli_args: &[&str]| diagnostics(Cli::parse_from(cli_args), test_dir.path());

        let err = "error: Cannot find implementation or library stub for module named \"foo\"";
        // No venv information should fail to import
        assert_eq!(
            d(&[""]),
            [
                format!("m.py:1: {err}"),
                format!("test-dir{}n.py:1: {err}", std::path::MAIN_SEPARATOR),
            ]
        );
        // venv information via --python-executable should work
        let empty: [&str; 0] = [];
        assert_eq!(d(&["", "--python-executable", "venv/bin/python"]), empty);

        // venv information via $VIRTUAL_ENV
        let ds = diagnostics_with_env_lookup(Cli::parse_from(&[""]), test_dir.path(), |name| {
            (name == "VIRTUAL_ENV").then(|| "venv".to_string())
        });
        assert_eq!(ds, empty);
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

        let err1 = format!(
            "foo{sep}bar{sep}mod1.py:1: error: \"int\" not callable",
            sep = std::path::MAIN_SEPARATOR
        );
        let err2 = format!(
            "foo{}mod2.py:1: error: \"int\" not callable",
            std::path::MAIN_SEPARATOR
        );
        let err3 = "mod3.py:1: error: \"int\" not callable";

        assert_eq!(d(&[""]), [&*err2]);

        assert_eq!(d(&["", "foo/**/mod[1-9].py"]), [&*err1, &*err2]);
        assert_eq!(d(&["", "**/*.py"]), [&*err1, &*err2, err3]);
        assert_eq!(d(&["", "**/mod2.py"]), [&*err2]);
        assert_eq!(d(&["", "**/"]), [&*err1, &*err2, err3]);
        assert_eq!(d(&["", "**/mod?.py"]), [&*err1, &*err2, err3]);
        assert_eq!(d(&["", "*.py"]), [err3]);
        assert_eq!(d(&["", "foo"]), [&*err1, &*err2]);
    }

    #[test]
    fn test_files_relative_paths() {
        logging_config::setup_logging_for_tests();
        let mut project_options = ProjectOptions::default();
        let local_fs = LocalFS::without_watcher();
        let current_dir = local_fs.unchecked_abs_path("/a/b".into());
        let mut cli = Cli::parse_from([""]);
        cli.files = vec![
            "/a/b/baz.py".to_string(),
            "bla.py".to_string(),
            "/other/".to_string(),
            "/another".to_string(),
            "blub/bla/".to_string(),
            "blub/baz".to_string(),
            //"blub/../not_in_blub".to_string(),
        ];
        apply_flags(
            &local_fs,
            &mut project_options,
            &mut DiagnosticConfig::default(),
            cli,
            current_dir,
        );
        let files: Vec<&str> = project_options
            .settings
            .files_or_directories_to_check
            .iter()
            .map(|p| p.as_str())
            .collect();
        if cfg!(target_os = "windows") {
            // TODO it might be questionable that this replaces some slashes, but not others on
            // Windows
            assert_eq!(
                files,
                vec![
                    "/a/b/baz.py",
                    "/a/b\\bla.py",
                    "/other\\**",
                    "/another\\**",
                    "/a/b\\blub/bla\\**",
                    "/a/b\\blub/baz\\**",
                    //"/foo/bar/not_in_blub",
                ]
            )
        } else {
            assert_eq!(
                files,
                vec![
                    "/a/b/baz.py",
                    "/a/b/bla.py",
                    "/other/**",
                    "/another/**",
                    "/a/b/blub/bla/**",
                    "/a/b/blub/baz/**",
                    //"/foo/bar/not_in_blub",
                ]
            )
        }
    }
}
