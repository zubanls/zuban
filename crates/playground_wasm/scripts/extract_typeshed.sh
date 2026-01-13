#!/bin/bash
set -e
dir="$(dirname "$0")"
ts="$dir/../../../third_party/typeshed"
sf="$dir/stubs.txt"
out="$dir/../src/stubs.rs"

{
  echo "pub const BUNDLED_STUBS: &[(&str, &str)] = &["
  n=0
  while read -r s; do
    for d in stdlib stubs; do
      [[ -f "$ts/$d/$s" ]] && {
        echo "    ("
        echo "        \"typeshed/$d/$s\"",
        echo "        include_str!(\"../../../third_party/typeshed/$d/$s\"),"
        echo "    ),"
        ((++n)); break
      }
    done
  done < "$sf"
  echo "];"
} > "$out"
echo "$n stubs -> $out"
