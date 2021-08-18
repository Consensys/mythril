import pytest
import json
import subprocess

from tests import BaseTestCase, TESTDATA, PROJECT_DIR, TESTS_DIR
from mock import patch

MYTH = str(PROJECT_DIR / "myth")


def output_of(command):
    return json.loads(subprocess.check_output(command, shell=True).decode("UTF-8"))


# TODO: Try using some python EVM for these tests


def validate_simple_example(output, branches):
    for branch_output, branch in zip(output, branches):
        if branch == "153":
            # Validation for initialState

            # Validation for tx steps
            tx_step = branch["steps"][1]
            assert tx_step["input"] == tx_step["calldata"]
            assert int(tx_step["input"][10:], 16) == 3


def validate_multiple_example(output, branches):
    for branch_output, branch in zip(output, branches):
        if branch == "153":
            # Validation for initialState

            # Validation for tx steps
            tx_step = branch["steps"][1]
            assert tx_step["input"] == tx_step["calldata"]
            assert int(tx_step["input"][10:], 16) == 3
        elif branch == "192":
            # Validation for initialState

            # Validation for tx steps
            tx_step = branch["steps"][1]
            assert tx_step["input"] == tx_step["calldata"]
            assert int(tx_step["input"][10:], 16) == 5
        elif branch == "243":
            # Validation for initialState

            # Validation for tx steps
            tx_step = branch["steps"][1]
            assert tx_step["input"] == tx_step["calldata"]
            assert int(tx_step["input"][10:], 16) == 7


def validate_two_contract(output, branches):
    for branch_output, branch in zip(output, branches):
        if branch == "311":
            # Validation for initialState

            # Validation for tx steps
            assert (
                int(branch["steps"][1][10:], 16) + int(branch["steps"][3][10:], 16)
                == 11
            )

        if branch == "341":
            # Validation for initialState

            # Validation for tx steps
            assert (
                int(branch["steps"][1][10:], 16) + int(branch["steps"][3][10:], 16)
                == 30
            )

        if branch == "371":
            # Validation for initialState

            # Validation for tx steps
            assert (
                int(branch["steps"][1][10:], 16) + int(branch["steps"][3][10:], 16)
                == 20
            )


def validate_multi_contract(output, branches):
    for branch_output, branch in zip(output, branches):
        if branch == "453":
            # Validation for initialState

            # Validation for tx steps
            assert (
                int(branch["steps"][1][10:], 16)
                + int(branch["steps"][3][10:], 16)
                + int(branch["steps"][5][10:], 16)
                == 10
            )

        if branch == "483":
            # Validation for initialState

            # Validation for tx steps
            assert (
                int(branch["steps"][1][10:], 16)
                + int(branch["steps"][3][10:], 16)
                + int(branch["steps"][5][10:], 16)
                == 25
            )


test_data = (
    ("simple_example_input.json", validate_simple_example, "153"),
    ("multiple_example_input.json", validate_multiple_example, "153,192,243"),
    ("two_contract_input.json", validate_two_contract, "311,341,371"),
    ("multi_contract_example_input.json", validate_multi_contract, "453,483"),
)

test_data_error = (("simple_example_input.json", "508"),)


@pytest.mark.parametrize("input_file,validate_function,branches", test_data)
def test_concolic(input_file, validate_function, branches):
    input_path = str(TESTS_DIR / "concolic" / "concolic_io" / input_file)

    command = f"{MYTH} concolic {input_path} --branches {branches}"
    received_output = output_of(command)

    validate_function(received_output, branches)


@pytest.mark.parametrize("input_file,branch", test_data_error)
def test_concolic_error(input_file, branch):
    input_path = str(TESTS_DIR / "concolic" / "concolic_io" / input_file)
    command = f"{MYTH} concolic {input_path} --branches {branch}"
    received_output = subprocess.run(
        command.split(), stdout=subprocess.PIPE, stderr=subprocess.PIPE
    )

    assert (
        f"The branch {branch} does not lead to a jump address, skipping this branch"
        in received_output.stderr.decode("UTF-8")
    )
