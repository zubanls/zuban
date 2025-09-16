#!/usr/bin/env bash 
set -eu -o pipefail 
                    
cd "$(dirname "$0")"
rm -f ../target/wheels/*
cd ../deploy/pypi/zuban

if [ $# -eq 0 ]; then
    echo "Creating a dev build (for release builds pass --release)"
else
    echo "Creating a build with maturin build ${@:1}"
fi

if [ ! -f licenses.html ]; then
    bash pre-maturin-build.sh
fi

maturin build "${@:1}"


pip install ../../../target/wheels/zuban-*.whl --force-reinstall --break-system-packages
