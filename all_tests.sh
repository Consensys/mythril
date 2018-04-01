#!/bin/sh

rm -rf ./tests/testdata/outputs_current/
mkdir -p ./tests/testdata/outputs_current/
python3 -m unittest discover -p "*_test.py"
