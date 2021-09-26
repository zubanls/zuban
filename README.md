
# Zuban

Copyright (c) 2020-2021 Dave Halter. All rights reserved.

## Development

I usually use this to test:

    CARGO_TARGET_DIR=/tmp/cargo_target RUSTFLAGS="-Z macro-backtrace" cargo test -- --nocapture

or:

    CARGO_TARGET_DIR=/tmp/cargo_target RUSTFLAGS="-Z macro-backtrace" cargo test -- --nocapture

with debug enabled:

    RUST_BACKTRACE=1 CARGO_TARGET_DIR=/tmp/cargo_target RUSTFLAGS="-Z macro-backtrace" cargo     test --features zuban_debug


### Profiling

    sudo sysctl -w kernel.perf_event_paranoid=1  # Might be needed
    flamegraph cargo test blackbox --release
    firefox flamegraph.svg
