#!/bin/sh

python3 --version
echo "Please make sure you are using python 3.6.x"

solc --version
echo "Please make sure you are using solc 0.4.21"

rm -rf ./tests/testdata/outputs_current/
mkdir -p ./tests/testdata/outputs_current/
python3 -m unittest discover -p "*_test.py"
