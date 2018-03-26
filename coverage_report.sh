#!/bin/sh

rm -rf htmlcov
coverage run -m unittest discover -p "*_test.py"
coverage html
open coverage_html_report/index.html
