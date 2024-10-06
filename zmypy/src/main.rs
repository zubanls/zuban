use std::io::Read;
use std::path::PathBuf;
use std::process::ExitCode;
use zuban_python::{DiagnosticConfig, ExcludeRegex, Project, ProjectOptions, PythonVersion};

use clap::Parser;

const CONFIG_PATHS: [&str; 6] = [
    "mypy.ini",
    ".mypy.ini",
    "pyproject.toml",
    "setup.cfg",
    "~/.config/mypy/config",
    "~/.mypy.ini",
];

#[derive(Parser)]
#[command(version, about)]
struct Cli {
    // Running code:
    /// Regular expression to match file names, directory names or paths which mypy should ignore
    /// while recursively discovering files to check, e.g. --exclude '/setup\.py$'. May be
    /// specified more than once, eg. --exclude a --exclude b
    #[arg(long)]
    exclude: Vec<String>,
    #[arg(num_args = 0..)]
    files: Vec<String>,
    /// Type-check module; can repeat for more modules
    #[arg(short, long)]
    module: Vec<String>,
    /// Type-check package recursively; can be repeated
    #[arg(short, long)]
    package: Vec<String>,

    // Config file
    /// Configuration file, must have a [mypy] section (defaults to mypy.ini, .mypy.ini, pyproject.toml, setup.cfg, ~/.config/mypy/config, ~/.mypy.ini)
    #[arg(long)]
    config_file: Option<PathBuf>,

    // Import discovery
    /// Silently ignore imports of missing modules
    #[arg(long)]
    ignore_missing_imports: bool,

    // Platform configuration
    /// Type check code assuming it will be running on Python x.y
    #[arg(long)]
    python_version: Option<PythonVersion>,
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
    #[arg(long)]
    no_mypy_compatible: bool,
}

fn main() -> ExitCode {
    let cli = Cli::parse();

    let in_dir = "TODO ";
    let mut diagnostic_config = DiagnosticConfig::default();
    let mut options = if let Some((name, content)) = find_mypy_config_file(&cli) {
        if name.ends_with(".toml") {
            ProjectOptions::from_pyproject_toml(in_dir, &content, &mut diagnostic_config)
        } else {
            ProjectOptions::from_mypy_ini(in_dir, &content, &mut diagnostic_config)
        }
        .unwrap_or_else(|err| panic!("Problem parsing Mypy config {name}: {err}"))
    } else {
        ProjectOptions::default()
    };

    options.settings.mypy_compatible = true;
    apply_flags(&mut options, cli);

    let mut project = Project::new(options);
    let diagnostic_config = DiagnosticConfig {
        show_error_codes: true,
        ..Default::default()
    };
    let diagnostics = project.diagnostics(&diagnostic_config);
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

fn find_mypy_config_file(cli: &Cli) -> Option<(&str, String)> {
    const CONFIG_FILE_READ_ISSUE: &'static str = "Issue while reading the config file";
    if let Some(config_file) = cli.config_file.as_ref() {
        let config_path = config_file
            .as_os_str()
            .to_str()
            .expect("Expected a valid UTF-8 encoded config path");
        let s = std::fs::read_to_string(config_path).expect(CONFIG_FILE_READ_ISSUE);
        return Some((config_path, s));
    }
    for config_path in CONFIG_PATHS {
        if let Ok(mut file) = std::fs::File::open(config_path) {
            let mut content = String::new();
            file.read_to_string(&mut content)
                .expect(CONFIG_FILE_READ_ISSUE);
            return Some((config_path, content));
        }
    }
    None
}

fn apply_flags(project_options: &mut ProjectOptions, cli: Cli) {
    macro_rules! apply {
        ($attr:ident, $inverse:ident) => {
            if cli.$attr {
                project_options.flags.$attr = true;
            }
            if cli.$inverse {
                project_options.flags.$attr = false;
            }
        };
    }
    apply!(strict_optional, no_strict_optional);
    apply!(strict_equality, no_strict_equality);
    apply!(implicit_optional, no_implicit_optional);
    apply!(check_untyped_defs, no_check_untyped_defs);
    if cli.ignore_missing_imports {
        project_options.flags.ignore_missing_imports = true;
    }
    apply!(disallow_untyped_defs, allow_untyped_defs);
    apply!(disallow_untyped_calls, allow_untyped_calls);
    apply!(disallow_untyped_decorators, allow_untyped_decorators);
    apply!(disallow_any_generics, allow_any_generics);
    apply!(disallow_any_decorated, disallow_any_decorated);
    apply!(disallow_any_explicit, disallow_any_explicit);
    //apply!(disallow_any_unimported, allow_any_unimported);
    //apply!(disallow_any_expr, allow_any_expr);
    apply!(disallow_subclassing_any, allow_subclassing_any);
    apply!(disallow_incomplete_defs, allow_incomplete_defs);
    if cli.allow_untyped_globals {
        project_options.flags.allow_untyped_globals = true;
    }
    apply!(warn_unreachable, no_warn_unreachable);
    //apply!(warn_redundant_casts, no_warn_redundant_casts);
    apply!(warn_return_any, no_warn_return_any);
    apply!(warn_no_return, no_warn_no_return);
    apply!(no_implicit_reexport, implicit_reexport);
    apply!(extra_checks, no_extra_checks);

    if cli.no_mypy_compatible {
        project_options.settings.mypy_compatible = false;
    }

    if cli.platform.is_some() {
        project_options.settings.platform = cli.platform;
    }
    if let Some(python_version) = cli.python_version {
        project_options.settings.python_version = python_version;
    }
    let cwd = std::env::current_dir().expect("Expected a valid working directory");
    const CWD_ERROR: &'static str = "Expected valid unicode in working directory";
    if !cli.files.is_empty() {
        project_options.settings.files_or_directories_to_check = cli
            .files
            .into_iter()
            .map(|f| {
                cwd.as_path()
                    .join(f)
                    .into_os_string()
                    .into_string()
                    .expect(CWD_ERROR)
            })
            .collect();
    }
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

    for r in cli.exclude {
        project_options
            .flags
            .excludes
            .push(ExcludeRegex::new(r).expect("Invalid --exclude regex"));
    }

    // TODO MYPYPATH=$MYPYPATH:mypy-stubs
    project_options
        .settings
        .mypy_path
        .push(cwd.into_os_string().into_string().expect(CWD_ERROR));
}
