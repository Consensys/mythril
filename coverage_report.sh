#!/bin/sh

coverage run --source=mythril -m unittest discover -p "*_test.py"
coverage html
open htmlcov/index.html
