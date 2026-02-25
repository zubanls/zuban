use std::{path::PathBuf, sync::Arc};

pub use config::DiagnosticConfig;

use config::{
    ExcludeRegex, Mode, ProjectOptions, PythonVersion, Settings, TypeCheckerFlags,
    UntypedFunctionReturnMode,
};
use vfs::{AbsPath, SimpleLocalFS, VfsHandler};

use clap::Parser;

#[derive(Parser, Default, Debug)]
pub struct Cli {
    // Additional options that are not present in zmypy
    /// Choosing a mode sets the basic preset of flags. The default mode is typed, which is not
    /// mypy-compatible.
    #[arg(long)]
    mode: Option<Mode>,

    /// Can be either "any" to infer untyped function returns like Mypy, "inferred" to infer return
    /// types or "advanced" to infer return types in a more sophisticated way that includes
    /// inferring params.
    #[arg(long)]
    pub untyped_function_return_mode: Option<UntypedFunctionReturnMode>,

    #[command(flatten)]
    pub mypy_options: MypyCli,
}

impl Cli {
    pub fn new_mypy_compatible(mypy_options: MypyCli) -> Self {
        Self {
            mode: Some(Mode::Mypy),
            untyped_function_return_mode: None,
            mypy_options,
        }
    }

    pub fn mypy_compatible(&self) -> Option<bool> {
        Some(matches!(self.mode?, Mode::Mypy))
    }

    pub fn mode(&self) -> Option<Mode> {
        Some(self.mode?.into())
    }
}

#[derive(Parser, Clone, Default, Debug)]
pub struct MypyCli {
    // Running code:
    /// Regular expression to match file names, directory names or paths which mypy should ignore
    /// while recursively discovering files to check, e.g. --exclude '/setup\.py$'. May be
    /// specified more than once, eg. --exclude a --exclude b
    #[arg(long)]
    pub exclude: Vec<String>,
    /// This is mostly for testing, to test all possible files (there shouldn't be any crashes)
    #[arg(long, hide = true)]
    pub ignore_excludes_from_config: bool,
    #[arg(num_args = 0..)]
    pub files: Vec<String>,
    #[arg(long, hide = true)]
    pub exclude_gitignore: bool,
    #[arg(long, hide = true)]
    pub no_exclude_gitignore: bool,
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
    pub config_file: Option<PathBuf>,

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
    // any_unimported and any_expr are currently hidden, because they are not fully implemented.
    //-/ Disallow Any types resulting from unfollowed imports
    #[arg(long, hide = true)]
    allow_any_unimported: bool,
    #[arg(long, hide = true)]
    disallow_any_unimported: bool,
    //-/ Disallow all expressions that have type Any
    #[arg(long, hide = true)]
    disallow_any_expr: bool,
    #[arg(long, hide = true)]
    allow_any_expr: bool,
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
    /// Disable strict Optional checks in untyped contexts (inverse: --untyped-strict-optional)
    #[arg(long)]
    no_untyped_strict_optional: bool,
    #[arg(long)]
    untyped_strict_optional: bool,

    // Configuring warnings:
    /// Warn about casting an expression to its inferred type (inverse: --no-warn-redundant-casts)
    #[arg(long)]
    warn_redundant_casts: bool,
    #[arg(long)]
    no_warn_redundant_casts: bool,
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
    #[arg(long, hide = true)]
    allow_incomplete_generics: bool,
    #[arg(long, hide = true)]
    disallow_incomplete_generics: bool,
    #[arg(long, hide = true)]
    check_untyped_overrides: bool,
    #[arg(long, hide = true)]
    no_check_untyped_overrides: bool,
}

pub fn apply_flags(
    vfs_handler: &SimpleLocalFS,
    project_options: &mut ProjectOptions,
    diagnostic_config: &mut DiagnosticConfig,
    current_dir: Arc<AbsPath>,
    cli: Cli,
    project_dir: Arc<AbsPath>,
    config_path: Option<&AbsPath>,
) {
    apply_flags_detailed(
        vfs_handler,
        &mut project_options.settings,
        &mut project_options.flags,
        diagnostic_config,
        current_dir,
        cli,
        project_dir,
        config_path,
    )
}

pub fn apply_flags_detailed(
    vfs_handler: &SimpleLocalFS,
    settings: &mut Settings,
    flags: &mut TypeCheckerFlags,
    diagnostic_config: &mut DiagnosticConfig,
    current_dir: Arc<AbsPath>,
    cli: Cli,
    project_dir: Arc<AbsPath>,
    config_path: Option<&AbsPath>,
) {
    if let Some(mode) = cli.mode {
        settings.mode = mode.into();
    }
    if let Some(untyped_function_return_mode) = cli.untyped_function_return_mode {
        settings.untyped_function_return_mode = untyped_function_return_mode
    }

    apply_mypy_flags(
        vfs_handler,
        settings,
        flags,
        diagnostic_config,
        current_dir,
        cli.mypy_options,
        config_path,
    );

    settings
        .mypy_path
        .push(vfs_handler.normalize_rc_path(project_dir));
}

fn apply_mypy_flags(
    vfs_handler: &SimpleLocalFS,
    settings: &mut Settings,
    flags: &mut TypeCheckerFlags,
    diagnostic_config: &mut DiagnosticConfig,
    current_dir: Arc<AbsPath>,
    cli: MypyCli,
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
    if cli.strict {
        flags.enable_all_strict_flags();
    }
    if cli.strict_bytes {
        flags.enable_strict_bytes();
    }
    apply!(flags, strict_optional, no_strict_optional);
    apply!(flags, untyped_strict_optional, no_untyped_strict_optional);
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
    apply!(flags, disallow_any_unimported, allow_any_unimported);
    apply!(flags, disallow_any_expr, allow_any_expr);
    apply!(flags, disallow_subclassing_any, allow_subclassing_any);
    apply!(flags, disallow_incomplete_defs, allow_incomplete_defs);
    apply!(flags, allow_untyped_globals, disallow_untyped_globals);
    apply!(flags, warn_unreachable, no_warn_unreachable);
    apply!(flags, warn_redundant_casts, no_warn_redundant_casts);
    apply!(flags, warn_return_any, no_warn_return_any);
    apply!(flags, warn_no_return, no_warn_no_return);
    apply!(flags, no_implicit_reexport, implicit_reexport);
    apply!(flags, extra_checks, no_extra_checks);
    apply!(
        flags,
        allow_incomplete_generics,
        disallow_incomplete_generics
    );
    apply!(flags, check_untyped_overrides, no_check_untyped_overrides);

    apply!(diagnostic_config, show_column_numbers, hide_column_numbers);
    apply!(diagnostic_config, show_error_end, hide_error_end);
    apply!(diagnostic_config, show_error_codes, hide_error_codes);
    apply!(diagnostic_config, pretty, no_pretty);
    apply!(diagnostic_config, error_summary, no_error_summary);
    apply!(settings, exclude_gitignore, no_exclude_gitignore);

    apply!(flags, allow_redefinition, disallow_redefinition);
    if cli.allow_redefinition_new {
        flags.allow_redefinition = true;
    }
    if cli.disallow_redefinition_new {
        flags.allow_redefinition = false;
    }

    if cli.platform.is_some() {
        settings.platform = cli.platform;
    }
    if let Some(python_version) = cli.python_version {
        settings.python_version = Some(python_version);
    }
    if let Some(p) = cli.python_executable {
        settings
            .apply_python_executable(vfs_handler, &current_dir, config_path, &p)
            .expect("Error when applying --python-executable")
    }
    if let Some(p) = &settings.environment {
        tracing::info!("Checking the following environment: {p}");
    }
    if !cli.files.is_empty() {
        settings
            .set_files_or_directories_to_check(vfs_handler, &current_dir, config_path, cli.files)
            .expect("Need a valid glob path as a files argument");
    }
    tracing::info!(
        "Checking the following files: {:?}",
        &settings.files_or_directories_to_check
    );
    flags.enabled_error_codes.extend(cli.enable_error_code);
    flags.disabled_error_codes.extend(cli.disable_error_code);
    flags.always_true_symbols.extend(cli.always_true);
    flags.always_false_symbols.extend(cli.always_false);

    if cli.ignore_excludes_from_config {
        // This is for testing, so we can test all files
        flags.excludes.clear();
    }
    for r in cli.exclude {
        flags
            .excludes
            .push(ExcludeRegex::new(r).expect("Invalid --exclude regex"));
    }
    tracing::info!(
        "Found the following excludes: {:?}",
        flags
            .excludes
            .iter()
            .map(|e| &e.regex_str)
            .collect::<Vec<_>>()
    );
}
