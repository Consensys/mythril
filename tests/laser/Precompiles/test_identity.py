import pytest

from mock import patch
from eth_utils import decode_hex
from mythril.laser.ethereum.natives import identity, NativeContractException
from mythril.laser.smt import symbol_factory


@pytest.mark.parametrize(
    "input_list, expected_result", (([], []), ([10, 20], [10, 20]))
)
def test_identity(input_list, expected_result):
    assert identity(input_list) == expected_result
