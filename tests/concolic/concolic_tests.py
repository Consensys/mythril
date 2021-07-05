import pytest
import json

from subprocess import check_output
from tests import BaseTestCase, TESTDATA, PROJECT_DIR, TESTS_DIR
from mock import patch

MYTH = str(PROJECT_DIR / "myth")


def output_of(command):
    return json.loads(check_output(command, shell=True).decode("UTF-8"))


test_data = (
    ("simple_example_input.json", "simple_example_output.json", "153"),
    ("multiple_example_input.json", "multiple_example_output.json", "153,192,243"),
    ("two_contract_input.json", "two_contract_output.json", "311,341,371"),
)


@pytest.mark.parametrize("input_file,output_file,branches", test_data)
def test_concolic(input_file, output_file, branches):
    input_path = str(TESTS_DIR / "concolic" / "concolic_io" / input_file)
    output_path = str(TESTS_DIR / "concolic" / "concolic_io" / output_file)

    command = f"{MYTH} concolic {input_path} --branches {branches}"
    with open(output_path) as f:
        expected_output = json.load(f)
    received_output = output_of(command)

    assert received_output == expected_output
