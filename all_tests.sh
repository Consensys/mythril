#!/bin/sh

echo -n "Checking Python version... "
python -c 'import sys
print(sys.version)
assert sys.version_info[0:2] >= (3,6), \
"""Please make sure you are using Python 3.6.x.
You ran with {}""".format(sys.version)' || exit $?

echo "Checking solc version..."
out=$(solc --version) || {
    echo 2>&1 "Please make sure you have solc installed, version 0.4.21 or greater"

    }
case $out in
    *Version:\ 0.4.2[1-9]* )
	echo $out
	break ;;
    * )
	echo $out
	echo "Please make sure your solc version is at least 0.4.21"
	exit 1
	;;
esac

echo "Checking that truffle is installed..."
if ! which truffle ; then
    echo "Please make sure you have etherum truffle installed (npm install -g truffle)"
    exit 2
fi

rm -rf ./tests/testdata/outputs_current/
mkdir -p ./tests/testdata/outputs_current/
mkdir -p /tmp/test-reports
pytest --junitxml=/tmp/test-reports/junit.xml
