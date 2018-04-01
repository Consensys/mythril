#!/bin/sh

rm -rf ./tests/testdata/outputs_current/
mkdir -p ./tests/testdata/outputs_current/
rm -rf coverage_html_report

coverage run -m unittest discover -p "*_test.py"
coverage html
open coverage_html_report/index.html
