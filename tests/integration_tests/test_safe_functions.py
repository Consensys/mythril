import pytest
import json
import sys

from subprocess import check_output
from tests import PROJECT_DIR, TESTDATA

MYTH = str(PROJECT_DIR / "myth")
test_data = (
    ("safe_funcs.sol.o", ["change_val()", "assert1()", "safe_indexing(uint256)"],),
)


@pytest.mark.parametrize("file_name, safe_funcs", test_data)
def test_analysis(file_name, safe_funcs):
    bytecode_file = str(TESTDATA / "inputs" / file_name)
    command = f"""python3 {MYTH} safe-functions -f {bytecode_file}"""
    output = check_output(command, shell=True).decode("UTF-8")
    assert f"{len(safe_funcs)} functions are deemed safe in this contract" in output
    for func in safe_funcs:
        assert func in output
