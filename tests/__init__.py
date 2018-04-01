from pathlib import Path
import os

TESTS_DIR = Path(__file__).parent
PROJECT_DIR = TESTS_DIR.parent
TESTDATA = TESTS_DIR / "testdata"
TESTDATA_INPUTS = TESTDATA / "inputs"
TESTDATA_OUTPUTS_EXPECTED = TESTDATA / "outputs_expected"
TESTDATA_OUTPUTS_CURRENT = TESTDATA / "outputs_current"

os.environ['MYTHRIL_DIR'] = str(TESTS_DIR / "mythril_dir")

def compare_files_error_message(expected, current):
    return "Expected output changes, compare the following files to see differences: \n- {}\n- {}\n".format(str(expected), str(current))
