import pytest

from tests import PROJECT_DIR, TESTDATA
from utils import output_of

MYTH = str(PROJECT_DIR / "myth")


test_data = [
    (open(f"{TESTDATA}/inputs/coverage.sol.o").read(), True),
]


@pytest.mark.parametrize("code, exists", test_data)
def test_basic_coverage(code, exists):
    assert (
        "instruction_discovery_time"
        in output_of(f"{MYTH} a -c 0x{code} --solver-timeout 1000 -o jsonv2")
    ) == exists
