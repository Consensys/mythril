import pytest
import json
import sys
import os

from tests import PROJECT_DIR, TESTDATA
from utils import output_of

MYTH = str(PROJECT_DIR / "myth")


test_data = (
    # TODO: The commented tests should be sped up!
    # (
    #    "destruct.sol",
    #    {
    #        "TX_COUNT": 5,
    #        "MODULE": "AccidentallyKillable",
    #        "ISSUE_COUNT": 1,
    #        "VERSION": "v0.5.0",
    #    },
    # ),
    # (
    #    "destruct.sol",
    #    {
    #        "TX_COUNT": 4,
    #        "MODULE": "AccidentallyKillable",
    #        "ISSUE_COUNT": 0,
    #        "VERSION": "v0.5.0",
    #    },
    # ),
    (
        "theft.sol",
        {"TX_COUNT": 4, "MODULE": "EtherThief", "ISSUE_COUNT": 1, "VERSION": "v0.5.0"},
    ),
    (
        "theft.sol",
        {"TX_COUNT": 3, "MODULE": "EtherThief", "ISSUE_COUNT": 0, "VERSION": "v0.5.0"},
    ),
    (
        "large.sol",
        {
            "TX_COUNT": 11,
            "MODULE": "AccidentallyKillable",
            "ISSUE_COUNT": 1,
            "VERSION": "v0.5.0",
        },
    ),
    (
        "large.sol",
        {
            "TX_COUNT": 10,
            "MODULE": "AccidentallyKillable",
            "ISSUE_COUNT": 0,
            "VERSION": "v0.5.0",
        },
    ),
    (
        "hash_test.sol",
        {
            "TX_COUNT": 2,
            "MODULE": "AccidentallyKillable",
            "ISSUE_COUNT": 1,
            "VERSION": "v0.4.24",
        },
    ),
    (
        "complex.sol",
        {
            "TX_COUNT": 2,
            "MODULE": "AccidentallyKillable",
            "ISSUE_COUNT": 1,
            "VERSION": "v0.5.0",
        },
    ),
    (
        "base_case.sol",
        {
            "TX_COUNT": 1,
            "MODULE": "AccidentallyKillable",
            "ISSUE_COUNT": 1,
            "VERSION": "v0.5.0",
        },
    ),
    (
        "simple_theft.sol",
        {
            "TX_COUNT": 1,
            "MODULE": "EtherThief",
            "ISSUE_COUNT": 0,
            "VERSION": "v0.5.0",
        },
    ),
)


@pytest.mark.parametrize("file_name, tx_data", test_data)
def test_analysis(file_name, tx_data):
    file_path = str(TESTDATA / "input_contracts" / file_name)
    command = f"""python3 {MYTH} analyze {file_path} -t {tx_data["TX_COUNT"]} -o jsonv2 -m {tx_data["MODULE"]} --solver-timeout 60000 --solv {tx_data["VERSION"]} --execution-timeout 300 --enable-summaries"""
    output = json.loads(output_of(command))
    assert len(output[0]["issues"]) == tx_data["ISSUE_COUNT"]
