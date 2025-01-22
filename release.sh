#!/usr/bin/env bash
set -eu -o pipefail

cd "$(dirname "$0")"

# path is the default level
LEVEL="${1:-patch}"

cargo install cargo-release
cargo release --manifest-path crates/zuban/Cargo.toml --no-tag --no-push "$LEVEL"
