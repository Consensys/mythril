import pytest
import json
import sys

from utils import output_of
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
    (
        "exceptions_0.8.0.sol.o",
        {
            "TX_COUNT": 1,
            "TX_OUTPUT": 1,
            "MODULE": "Exceptions",
            "ISSUE_COUNT": 2,
            "ISSUE_NUMBER": 0,
        },
        None,
    ),
    (
        "symbolic_exec_bytecode.sol.o",
        {
            "TX_COUNT": 1,
            "TX_OUTPUT": 0,
            "MODULE": "AccidentallyKillable",
            "ISSUE_COUNT": 1,
            "ISSUE_NUMBER": 0,
        },
        None,
    ),
    (
        "extcall.sol.o",
        {
            "TX_COUNT": 1,
            "TX_OUTPUT": 0,
            "MODULE": "Exceptions",
            "ISSUE_COUNT": 1,
            "ISSUE_NUMBER": 0,
        },
        None,
    ),
)


@pytest.mark.parametrize("file_name, tx_data, calldata", test_data)
def test_analysis(file_name, tx_data, calldata):
    bytecode_file = str(TESTDATA / "inputs" / file_name)
    command = f"""python3 {MYTH} analyze -f {bytecode_file} -t {tx_data["TX_COUNT"]} -o jsonv2 -m {tx_data["MODULE"]} --solver-timeout 60000  --no-onchain-data"""
    output = json.loads(output_of(command))

    assert len(output[0]["issues"]) == tx_data["ISSUE_COUNT"]
    if calldata:
        test_case = output[0]["issues"][tx_data["ISSUE_NUMBER"]]["extra"]["testCases"][
            0
        ]
        assert test_case["steps"][tx_data["TX_OUTPUT"]]["input"] == calldata


@pytest.mark.parametrize("file_name, tx_data, calldata", test_data)
def test_analysis_pending(file_name, tx_data, calldata):
    bytecode_file = str(TESTDATA / "inputs" / file_name)
    command = f"""python3 {MYTH} analyze -f {bytecode_file} -t {tx_data["TX_COUNT"]} -o jsonv2 -m {tx_data["MODULE"]} --solver-timeout 60000 --strategy pending --no-onchain-data"""
    output = json.loads(output_of(command))

    assert len(output[0]["issues"]) == tx_data["ISSUE_COUNT"]
    if calldata:
        test_case = output[0]["issues"][tx_data["ISSUE_NUMBER"]]["extra"]["testCases"][
            0
        ]
        assert test_case["steps"][tx_data["TX_OUTPUT"]]["input"] == calldata


test_data_code = [
    ("114", f"{TESTDATA}/input_contracts/tx.sol", True),
    ("123", f"{TESTDATA}/input_contracts/requirements_violation_pos.sol", True),
    ("123", f"{TESTDATA}/input_contracts/requirements_violation_neg.sol", False),
    ("132", f"{TESTDATA}/input_contracts/unexpected_ether_pos.sol", True),
    ("132", f"{TESTDATA}/input_contracts/unexpected_ether_neg.sol", False),
]


@pytest.mark.parametrize("swc, file_path, exists", test_data_code)
def test_analysis_code(swc, file_path, exists):
    assert (
        "SWC ID: {}".format(swc)
        in output_of(f"python3 {MYTH} a {file_path} --solver-timeout 5000")
    ) == exists
