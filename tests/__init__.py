from pathlib import Path
from unittest import TestCase
import os
import shutil

TESTS_DIR = Path(__file__).parent
PROJECT_DIR = TESTS_DIR.parent
TESTDATA = TESTS_DIR / "testdata"
TESTDATA_INPUTS = TESTDATA / "inputs"
TESTDATA_INPUTS_CONTRACTS = TESTDATA / "input_contracts"
TESTDATA_OUTPUTS_EXPECTED = TESTDATA / "outputs_expected"
TESTDATA_OUTPUTS_CURRENT = TESTDATA / "outputs_current"
TESTDATA_OUTPUTS_CURRENT_LASER_RESULT = TESTDATA / "outputs_current_laser_result"
TESTDATA_OUTPUTS_EXPECTED_LASER_RESULT = TESTDATA / "outputs_expected_laser_result"
MYTHRIL_DIR = TESTS_DIR / "mythril_dir"


class BaseTestCase(TestCase):
    def setUp(self):
        self.changed_files = []
        self.ori_mythril_dir = getattr(os.environ, "MYTHRIL_DIR", "")
        os.environ["MYTHRIL_DIR"] = str(MYTHRIL_DIR)
        shutil.copyfile(
            str(MYTHRIL_DIR / "signatures.json.example"),
            str(MYTHRIL_DIR / "signatures.json"),
        )

    def tearDown(self):
        os.environ["MYTHRIL_DIR"] = self.ori_mythril_dir
        os.remove(str(MYTHRIL_DIR / "signatures.json"))

    def compare_files_error_message(self):
        message = "Following output files are changed, compare them manually to see differences: \n"

        for (input_file, expected, current) in self.changed_files:
            message += "{}:\n".format(input_file.name)
            message += "- {}\n".format(str(expected))
            message += "- {}\n".format(str(current))

        return message

    def found_changed_files(self, input_file, output_expected, output_current):
        self.changed_files.append((input_file, output_expected, output_current))

    def assert_and_show_changed_files(self):
        self.assertEqual(
            0, len(self.changed_files), msg=self.compare_files_error_message()
        )
