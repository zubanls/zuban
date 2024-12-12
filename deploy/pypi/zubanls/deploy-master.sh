#!/usr/bin/env bash

set -eu -o pipefail

BASE_DIR=$(dirname $(readlink -f "$0"))
cd $BASE_DIR

# Package and upload to PyPI
rm -rf dist/
echo `pwd`
python3 setup.py bdist_wheel
# Maybe do a pip install twine before.
twine upload dist/*
