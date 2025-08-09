#!/usr/bin/env bash 
set -eu -o pipefail 
                    
cd "$(dirname "$0")"
rm -f ../target/wheels/*
cd ../deploy/pypi/zuban

if [ "$1" == "dev" ]; then
    echo "Creating a dev build"
    maturin build
else
    echo "Creating a release build"
    maturin build --release
fi


pip install ../../../target/wheels/zuban-*.whl --force-reinstall --break-system-packages
