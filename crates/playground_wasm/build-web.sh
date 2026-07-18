#!/usr/bin/env bash
set -euo pipefail

crate_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
output_dir="$crate_dir/dist"

cd "$crate_dir"
wasm-pack build . \
    --target web \
    --release \
    --out-dir dist \
    --out-name playground_wasm \
    --no-typescript \
    --no-pack \
    --no-default-features \
    --features playground-single

cp web/index.html "$output_dir/index.html"
rm -f "$output_dir/.gitignore"

echo "Cloudflare Pages bundle: $output_dir"
