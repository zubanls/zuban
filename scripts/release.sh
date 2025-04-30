#!/usr/bin/env bash
set -eu -o pipefail

cd "$(dirname "$0")"

# path is the default level
LEVEL="${1:-patch}"

cargo install cargo-release --version 0.25.17
cargo release --workspace --tag-prefix '' --no-publish --execute "$LEVEL"
