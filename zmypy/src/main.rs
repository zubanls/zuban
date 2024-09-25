use std::path::PathBuf;
use zuban_python::{DiagnosticConfig, Project, ProjectOptions, PythonVersion, TypeCheckerFlags};

use clap::Parser;

#[derive(Parser)]
#[command(version, about)]
struct Cli {
    // Running code:
    #[arg(num_args = 0..)]
    path_filters: Vec<String>,
    #[arg(short, long)]
    module: Vec<String>,
    #[arg(short, long)]
    package: Vec<String>,
    #[arg(long)]
    exclude: Vec<String>,

    // Config file
    /// Configuration file, must have a [mypy] section
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
    #[arg(long, num_args = 0.., value_name="NAME")]
    always_true: Vec<String>,
    /// Additional variable to be considered False (may be repeated)
    #[arg(long, num_args = 0.., value_name="NAME")]
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
    #[arg(long, num_args = 0.., value_name="NAME")]
    disable_error_code: Vec<String>,
    /// Enable a specific error code
    #[arg(long, num_args = 0.., value_name="NAME")]
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

    // --warn-unreachable --disallow-untyped-calls --disallow-incomplete-defs
}

fn main() -> std::io::Result<()> {
    // TODO MYPYPATH=$MYPYPATH:mypy-stubs
    let cli = Cli::parse();

    let options = ProjectOptions::new(TypeCheckerFlags {
        strict_optional: todo!(),
        strict_equality: todo!(),
        implicit_optional: todo!(),
        check_untyped_defs: todo!(),
        ignore_missing_imports: todo!(),
        disallow_untyped_defs: todo!(),
        disallow_untyped_calls: todo!(),
        disallow_untyped_decorators: todo!(),
        disallow_any_generics: todo!(),
        disallow_any_decorated: todo!(),
        disallow_any_explicit: todo!(),
        disallow_any_unimported: todo!(),
        disallow_any_expr: false,
        disallow_subclassing_any: todo!(),
        disallow_incomplete_defs: todo!(),
        allow_untyped_globals: todo!(),
        allow_empty_bodies: todo!(),
        warn_unreachable: todo!(),
        warn_redundant_casts: todo!(),
        warn_return_any: todo!(),
        warn_no_return: todo!(),
        local_partial_types: todo!(),
        no_implicit_reexport: todo!(),
        disable_bytearray_promotion: todo!(),
        disable_memoryview_promotion: todo!(),
        platform: todo!(),
        enabled_error_codes: todo!(),
        disabled_error_codes: todo!(),
        python_version: todo!(),
        always_true_symbols: todo!(),
        always_false_symbols: todo!(),
        mypy_path: todo!(),
        extra_checks: todo!(),
        mypy_compatible: todo!(),
        case_sensitive: todo!(),
    });
    let mut project = zuban_python::Project::new(options);
    let diagnostic_config = DiagnosticConfig {
        show_error_codes: true,
        ..Default::default()
    };
    let diagnostics = project.diagnostics(&diagnostic_config);
    for diagnostic in diagnostics.iter() {
        println!("{}", diagnostic.as_string(&diagnostic_config))
    }
    return Ok(());
}
