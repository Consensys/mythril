#!/bin/sh

python --version
echo "Please make sure you are using python 3.6.x"

rm -rf ./tests/testdata/outputs_current/
mkdir -p ./tests/testdata/outputs_current/
rm -rf coverage_html_report

coverage run -m unittest discover -p "*_test.py"
coverage html
open coverage_html_report/index.html
