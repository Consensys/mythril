import pytest
import json
import sys

from subprocess import check_output
from tests import PROJECT_DIR, TESTDATA

MYTH = str(PROJECT_DIR / "myth")
test_data = (
    ("version_contract.sol", "v0.7.0", True),
    ("version_contract.sol", "v0.8.0", False),
    ("version_contract_0.8.0.sol", None, False),
    ("version_contract_0.7.0.sol", None, True),
)


@pytest.mark.parametrize("file_name, version, has_overflow", test_data)
def test_analysis(file_name, version, has_overflow):
    file = str(TESTDATA / "input_contracts" / file_name)
    if version:
        command = f"python3 {MYTH} analyze {file} --solv {version}"
    else:
        command = f"python3 {MYTH} analyze {file}"
    output = check_output(command, shell=True).decode("UTF-8")
    if has_overflow:
        assert f"SWC ID: 101" in output
    else:
        assert (
            "The analysis was completed successfully. No issues were detected."
            in output
        )
