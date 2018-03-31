from pathlib import Path
import os

TESTS_DIR = Path(__file__).parent
PROJECT_DIR = TESTS_DIR.parent
TESTDATA = TESTS_DIR / "testdata"
TESTDATA_INPUTS = TESTDATA / "inputs"
TESTDATA_OUTPUTS = TESTDATA / "outputs"

os.environ['MYTHRIL_DIR'] = str(TESTS_DIR / "mythril_dir")
