#!/usr/bin/env bash
set -eu -o pipefail -x

# Simply show the current rust version
rustup show

RUST_BACKTRACE=1 cargo test --locked

# Check that the server ends, because no license was found
(cargo run --bin zubanls 2>&1 || true) | grep -q 'license.json": No such file or directory'
