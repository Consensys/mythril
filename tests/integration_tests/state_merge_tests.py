import pytest
import os
import subprocess

from tests import PROJECT_DIR, TESTDATA


MYTH = str(PROJECT_DIR / "myth")


def output_with_stderr(command):
    return subprocess.run(
        command.split(" "), stdout=subprocess.PIPE, stderr=subprocess.PIPE
    )


testfile_path = os.path.split(__file__)[0]

"""
calls.bin is the bytecode of 
https://github.com/ConsenSys/mythril/blob/develop/solidity_examples/calls.sol
"""
swc_test_data = [
    ("114", f"{TESTDATA}/inputs/calls.sol.o", (9, 5)),
]


@pytest.mark.parametrize("swc, code, states_reduction", swc_test_data)
def test_merge(swc, code, states_reduction):
    output = output_with_stderr(
        f"{MYTH} -v4 a -f {code} -t 1 --solver-timeout 500 -mUncheckedRetval --enable-state-merging"
    )
    output_str = f"States reduced from {states_reduction[0]} to {states_reduction[1]}"
    assert output_str in output.stderr.decode("utf-8")
