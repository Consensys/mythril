import pytest
import json
import sys

from subprocess import STDOUT
from tests import PROJECT_DIR, TESTDATA
from utils import output_of

MYTH = str(PROJECT_DIR / "myth")


def test_positive_solc_settings():
    file_path = str(TESTDATA / "input_contracts" / "destruct_crlf.sol")

    command = f"python3 {MYTH} analyze {file_path} --solv 0.5.0"
    output = output_of(command, stderr=STDOUT)
    assert "selfdestruct(addr)" in output
