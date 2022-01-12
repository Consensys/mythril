import pytest
import json
import sys
import os
import subprocess

from subprocess import check_output
from tests import PROJECT_DIR, TESTDATA
from mythril.analysis.swc_data import UNPROTECTED_SELFDESTRUCT


def test_docker():
    os.chdir(PROJECT_DIR)
    result = subprocess.run("docker build -t mythril .", shell=True)
    assert result.returncode == 0
    command = "docker run -v $(pwd):/tmp --rm mythril a /tmp/tests/testdata/input_contracts/symbolic_exec_bytecode.sol --solv 0.8.11"
    output = check_output(command, shell=True).decode("UTF-8")

    assert UNPROTECTED_SELFDESTRUCT in output
