#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

RUSTFLAGS="-C target-feature=+atomics,+bulk-memory" \
  wasm-pack build \
  --target web \
  --out-dir ../../target/wasm \
  crates/zubanls
