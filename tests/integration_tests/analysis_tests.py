import pytest
import json
import sys

from subprocess import check_output
from tests import PROJECT_DIR, TESTDATA

MYTH = str(PROJECT_DIR / "myth")
test_data = (
    (
        "flag_array.sol.o",
        {
            "TX_COUNT": 1,
            "TX_OUTPUT": 1,
            "MODULE": "EtherThief",
            "ISSUE_COUNT": 1,
            "ISSUE_NUMBER": 0,
        },
        "0xab12585800000000000000000000000000000000000000000000000000000000000004d2",
    ),
)


@pytest.mark.parametrize("file_name, tx_data, calldata", test_data)
def test_analysis(file_name, tx_data, calldata):
    bytecode_file = str(TESTDATA / "inputs" / file_name)
    command = f"""python3 {MYTH} analyze -f {bytecode_file} -t {tx_data["TX_COUNT"]} -o jsonv2 -m {tx_data["MODULE"]} --solver-timeout 60000"""
    output = json.loads(check_output(command, shell=True).decode("UTF-8"))

    assert len(output[0]["issues"]) == tx_data["ISSUE_COUNT"]
    test_case = output[0]["issues"][tx_data["ISSUE_NUMBER"]]["extra"]["testCases"][0]
    assert test_case["steps"][tx_data["TX_OUTPUT"]]["input"] == calldata
