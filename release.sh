#!/usr/bin/env bash
set -eu -o pipefail

cd "$(dirname "$0")"

# path is the default level
LEVEL="${1:-patch}"

cargo install cargo-release
cargo release --workspace --no-tag --no-push --execute "$LEVEL"
