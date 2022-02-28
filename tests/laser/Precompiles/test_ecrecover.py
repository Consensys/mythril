import pytest

from mock import patch
from eth_utils import decode_hex
from mythril.laser.ethereum.natives import ecrecover, NativeContractException
from mythril.laser.smt import symbol_factory

msg = b"\x6b\x8d\x2c\x81\xb1\x1b\x2d\x69\x95\x28\xdd\xe4\x88\xdb\xdf\x2f\x94\x29\x3d\x0d\x33\xc3\x2e\x34\x7f\x25\x5f\xa4\xa6\xc1\xf0\xa9"
v = b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x1c"
r = b"\x53\x56\x92\x27\x4f\x15\x24\x34\x00\x2a\x7c\x4c\x7d\x7c\xd0\x16\xea\x3e\x2d\x70\x2f\x2d\x2f\xd5\xb3\x32\x64\x6a\x9e\x40\x9a\x6b"
s = b"\x1f\x59\x24\xf5\x9c\x6d\x77\x66\xa6\x93\x17\xa3\xdf\x72\x9d\x8b\x61\x3c\x67\xaa\xf2\xfe\x06\x13\x39\x8b\x9f\x94\x4b\x98\x8e\xbd"

GOOD_DATA = list(msg + v + r + s)


@pytest.mark.parametrize(
    "input_list, expected_result",
    (
        ([], []),
        ([10, 20], []),
        (
            GOOD_DATA,
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
                131,
                23,
                8,
                48,
                142,
                77,
                185,
                107,
                254,
                47,
                229,
                79,
                224,
                43,
                181,
                99,
                36,
                171,
                166,
                119,
            ],
        ),
    ),
)
def test_ecrecover(input_list, expected_result):
    assert ecrecover(input_list) == expected_result


def test_ecrecover_symbol():
    input_list = ["bab", symbol_factory.BitVecSym("name", 256)]
    with pytest.raises(NativeContractException):
        ecrecover(input_list)
