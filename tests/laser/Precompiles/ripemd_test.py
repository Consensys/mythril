import pytest

from mock import patch
from eth_utils import decode_hex
from mythril.laser.ethereum.natives import ripemd160, NativeContractException
from mythril.laser.smt import symbol_factory


@pytest.mark.parametrize(
    "input_list, expected_result",
    (
        (
            [],
            [
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                156,
                17,
                133,
                165,
                197,
                233,
                252,
                84,
                97,
                40,
                8,
                151,
                126,
                232,
                245,
                72,
                178,
                37,
                141,
                49,
            ],
        ),
        (
            [10, 20],
            [
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                92,
                161,
                226,
                233,
                76,
                11,
                228,
                69,
                224,
                14,
                89,
                120,
                246,
                184,
                197,
                182,
                35,
                215,
                51,
                130,
            ],
        ),
    ),
)
def test_ripemd160(input_list, expected_result):
    assert ripemd160(input_list) == expected_result


def test_ripemd160_symbol():
    input_list = ["bab", symbol_factory.BitVecSym("name", 256)]
    with pytest.raises(NativeContractException):
        ripemd160(input_list)
