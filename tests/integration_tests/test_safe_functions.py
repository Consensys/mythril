import pytest
import json
import sys

from subprocess import check_output
from tests import PROJECT_DIR, TESTDATA

MYTH = str(PROJECT_DIR / "myth")
test_data = (
    ("suicide.sol", [], "0.5.0"),
    ("overflow.sol", ["balanceOf(address)", "totalSupply()"], "0.5.0"),
    (
        "ether_send.sol",
        [
            "crowdfunding()",
            "withdrawfunds()",
            "owner()",
            "balances(address)",
            "getBalance()",
        ],
        "0.5.0",
    ),
)

bytes_test_data = (
    ("suicide.sol.o", []),
    ("overflow.sol.o", ["balanceOf(address)", "totalSupply()"]),
    (
        "ether_send.sol.o",
        ["crowdfunding()", "withdrawfunds()", "owner()", "balances(address)"],
    ),
)


@pytest.mark.parametrize("file_name, safe_funcs, version", test_data)
def test_analysis(file_name, safe_funcs, version):
    file = str(TESTDATA / "input_contracts" / file_name)
    command = f"python3 {MYTH} safe-functions {file} --solv {version}"
    output = check_output(command, shell=True).decode("UTF-8")
    assert f"{len(safe_funcs)} functions are deemed safe in this contract" in output
    for func in safe_funcs:
        assert func in output


@pytest.mark.parametrize("file_name, safe_funcs", bytes_test_data)
def test_bytecode_analysis(file_name, safe_funcs):
    file = str(TESTDATA / "inputs" / file_name)
    command = f"python3 {MYTH} safe-functions --bin-runtime -f {file}"
    output = check_output(command, shell=True).decode("UTF-8")
    assert f"{len(safe_funcs)} functions are deemed safe in this contract" in output
