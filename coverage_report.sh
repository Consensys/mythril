#!/bin/sh

python --version
echo "Please make sure you are using python 3.6.x"

rm -rf ./tests/testdata/outputs_current/
mkdir -p ./tests/testdata/outputs_current/
rm -rf ./tests/testdata/outputs_current_laser_result/
mkdir -p ./tests/testdata/outputs_current_laser_result/
rm -rf coverage_html_report

py.test \
    --cov=mythril \
    --cov-config=tox.ini \
    --cov-report=html:coverage_html_report \
