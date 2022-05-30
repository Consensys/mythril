import pytest
import json
import sys

from subprocess import check_output, STDOUT
from tests import PROJECT_DIR, TESTDATA

MYTH = str(PROJECT_DIR / "myth")


def test_positive_solc_settings():
    file_path = str(TESTDATA / "input_contracts" / "destruct_crlf.sol")

    command = f"python3 {MYTH} analyze {file_path} --solv 0.5.0"
    output = check_output(command, shell=True, stderr=STDOUT).decode("UTF-8")
    assert "selfdestruct(addr)" in output
