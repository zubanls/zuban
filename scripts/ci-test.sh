#!/usr/bin/env bash
set -eu -o pipefail

# Simply show the current rust version
rustup show

cargo test --locked

# Check that the server ends, because no license was found
cargo run --bin zubanls 2>&1 | grep -q 'license.json": No such file or directory'
