import pytest
import json
import sys

from subprocess import check_output, STDOUT
from tests import PROJECT_DIR, TESTDATA

MYTH = str(PROJECT_DIR / "myth")


def test_positive_solc_settings():
    file_dir = str(TESTDATA / "json_test_dir" / "dir_a")
    json_file_path = str(TESTDATA / "json_test_dir" / "test_file.json")
    file_path = file_dir + "/input_file.sol"

    command = f"cd {file_dir} && python3 {MYTH} analyze {file_path} --solc-json {json_file_path} --solv 0.8.0"
    output = check_output(command, shell=True, stderr=STDOUT).decode("UTF-8")
    assert "The analysis was completed successfully" in output


def test_positive_solc_args():
    base_path = str(TESTDATA)
    file_dir = str(TESTDATA / "json_test_dir" / "dir_a")
    json_file_path = str(TESTDATA / "json_test_dir" / "test_file.json")
    file_path = file_dir + "/input_file_args.sol"

    command = f"""cd {file_dir} && python3 {MYTH} analyze {file_path} --solc-args "--allow-paths {base_path}" --solv 0.8.0"""
    output = check_output(command, shell=True, stderr=STDOUT).decode("UTF-8")
    assert "The analysis was completed successfully" in output


def test_neg_optimizer_solc_settings():
    file_dir = str(TESTDATA / "json_test_dir" / "dir_a")
    json_file_path = str(TESTDATA / "json_test_dir" / "test_file_disable.json")
    file_path = file_dir + "/input_file.sol"

    command = f"cd {file_dir} && python3 {MYTH} analyze {file_path} --solc-json {json_file_path} --solv 0.8.0"
    output = check_output(command, shell=True, stderr=STDOUT).decode("UTF-8")
    assert "Stack too deep when compiling inline assembly" in output


def test_negative_solc_settings():
    file_path = str(TESTDATA / "json_test_dir" / "dir_a" / "input_file.sol")

    command = f"python3 {MYTH} analyze {file_path} --solv 0.8.0"
    output = check_output(command, shell=True, stderr=STDOUT).decode("UTF-8")
    assert (
        """ParserError: Source "@openzeppelin/contracts/token/PRC20/PRC20.sol"""
        in output
    )
