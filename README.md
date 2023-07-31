
# Zuban

Copyright (c) 2020-2021 Dave Halter. All rights reserved.

## Development

I usually use this to test:

    CARGO_TARGET_DIR=/tmp/cargo_target RUSTFLAGS="-Z macro-backtrace" cargo test -- --nocapture

or:

    CARGO_TARGET_DIR=/tmp/cargo_target RUSTFLAGS="-Z macro-backtrace" cargo test -- --nocapture

with debug enabled:

    RUST_BACKTRACE=1 CARGO_TARGET_DIR=/tmp/cargo_target RUSTFLAGS="-Z macro-backtrace" cargo test --features zuban_debug
    CARGO_TARGET_DIR=/tmp/cargo_target  cargo test --features zuban_debug


### Profiling

    sudo apt-get install linux-tools-generic
    cargo install flamegraph
    sudo sysctl -w kernel.perf_event_paranoid=1  # Might be needed
    flamegraph cargo test blackbox --release
    firefox flamegraph.svg

### Progress History

- 2022-09-27: 1170 / 2547 (0.08s -> 14625 tests/s 44b39e90299909bb1672a0a64699c42145efda35)
- 2023-01-20: 1622 / 2989 (0.13s -> 12476 tests/s 914aede21d716bd80b9a790c213b6d54024b8b79)
- 2023-02-23: 1750 / 3104 (0.27s ->  6481 tests/s a8d9592a77286caa42501c69ea8b7b89c430c4a8)
- 2023-03-22: 2106 / 3866 (0.30s ->  7262 tests/s d5b94d4a3dcb75fbdb2abb7c6feb41dd7bd287ec)
- 2023-04-23: 2328 / 4006 (0.31s ->  7510 tests/s 515d90a4a5c12af68cd885db0bf2b79afe88f54d)
- 2023-07-23: 3411 / 5752 (0.39s ->  8746 tests/s 52f55a6477c9ecb71a76323cb9f8937e8f0c2433)

### Unsound?

- Chosing `__new__` or `__init__` via heuristic
- Initializing casting `Type[Class]` to `Type[object]` and then `Type[object]()` is ok?
- Ignoring positional arg names when assigning functions in:
  - Override checks (including multiple inheritance checks)
  - Checks where one side of callables is implicitly typed (i.e. `def foo...`)
  - Checks of inplace operators (However this does not matter, probably).
  - overlapping checks
