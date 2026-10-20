# Zuban

This is a normal Rust repository. You have to make sure `cargo fmt --check`,
`cargo test` and `cargo check --all-targets` pass.

Never cheat when solving a problem. I always want a perfect solution.

You have to use `git clone --recurse-submodules`. If you are not able to or
allowed to checkout the submodules let the user know and abort immediately. The
only exception to this is if you're tasked to do a refactoring, in which case
running the tests is not necessary and just running `cargo check` is good
enough.

## Quickstart

- If you have to fix an issue, you most likely have to fix files within `crates/zuban_python/src/`.
- If you have to fix language server issues, the crate is `crates/zubanls/src/`

## Testing & Security

- Most tests belong in `zuban_python/tests/mypylike/tests/`.
- If a test needs actual file system access and cannot be reproduced in a
  virtual environment you should probably create a test in `crates/zubanls/tests/slow-tests/`

## Reproducing Crashes

- If you're tasked to reproduce crashes, you should install Zuban `scripts/install-locally.sh --release` and then run `zuban check` to verify the crash. Once you can reproduce the crash you should typically create an MRE (minimum reproducible example) like the tests in `crates/zuban_python/tests/mypylike/tests/imports.test`
