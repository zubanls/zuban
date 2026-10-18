# Zuban

This is a normal Rust repository. You have to make sure `cargo fmt --check`,
`cargo test` and `cargo check --all-targets` pass.

Never cheat when solving a problem. I always want a perfect solution.

You have to use `git clone --recurse-submodules`. If you are not able to or
allowed to checkout the submodules let the user know and abort immediately.

## Quickstart

- If you have to fix an issue, you most likely have to fix files within `crates/zuban_python/src/`.
- If you have to fix language server issues, the crate is `crates/zubanls/src/`

## Testing & Security
- Most tests belong in `zuban_python/tests/mypylike/tests/`.
- If a test needs actual file system access and cannot be reproduced in a
  virtual environment you should probably create a test in `crates/zubanls/tests/slow-tests/`

