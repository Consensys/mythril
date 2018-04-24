#!/bin/sh

python3 --version
echo "Please make sure you are using python 3.6.x"

solc --version
echo "Please make sure you are using solc 0.4.21"

rm -rf ./tests/testdata/outputs_current/
mkdir -p ./tests/testdata/outputs_current/
mkdir -p /tmp/test-reports
pytest --junitxml=/tmp/test-reports/junit.xml
