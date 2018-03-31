#!/bin/sh

rm -rf coverage_html_report
coverage run -m unittest discover -p "*_test.py"
coverage html
open coverage_html_report/index.html
