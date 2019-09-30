#!/bin/sh

echo -n "Checking Python version... "
python -c 'import sys
print(sys.version)
assert sys.version_info[0:2] >= (3,5), \
"""Please make sure you are using Python 3.5 or later.
You ran with {}""".format(sys.version)' || exit $?

echo "Checking that truffle is installed..."
if ! which truffle ; then
    echo "Please make sure you have etherum truffle installed (npm install -g truffle)"
    exit 2
fi

rm -rf ./tests/testdata/outputs_current/
mkdir -p ./tests/testdata/outputs_current/
rm -rf ./tests/testdata/outputs_current_laser_result/
mkdir -p ./tests/testdata/outputs_current_laser_result/
mkdir -p /tmp/test-reports
pytest --junitxml=/tmp/test-reports/junit.xml
