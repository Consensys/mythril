import pytest
import json
import subprocess

from tests import BaseTestCase, TESTDATA, PROJECT_DIR, TESTS_DIR
from mock import patch

MYTH = str(PROJECT_DIR / "myth")


def output_of(command):
    return json.loads(subprocess.check_output(command, shell=True).decode("UTF-8"))


test_data = (
    ("simple_example_input.json", "simple_example_output.json", "153"),
    ("multiple_example_input.json", "multiple_example_output.json", "153,192,243"),
    ("two_contract_input.json", "two_contract_output.json", "311,341,371"),
    (
        "multi_contract_example_input.json",
        "multi_contract_example_output.json",
        "453,483",
    ),
)

test_data_error = (("simple_example_input.json", "508"),)


@pytest.mark.parametrize("input_file,output_file,branches", test_data)
def test_concolic(input_file, output_file, branches):
    input_path = str(TESTS_DIR / "concolic" / "concolic_io" / input_file)
    output_path = str(TESTS_DIR / "concolic" / "concolic_io" / output_file)

    command = f"{MYTH} concolic {input_path} --branches {branches}"
    with open(output_path) as f:
        expected_output = json.load(f)
    received_output = output_of(command)

    assert received_output == expected_output


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
