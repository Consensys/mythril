import pytest

from mock import patch
from eth_utils import decode_hex
from mythril.laser.ethereum.natives import sha256, NativeContractException
from mythril.laser.smt import symbol_factory


@pytest.mark.parametrize(
    "input_list, expected_result",
    (
        (
            [],
            [
                227,
                176,
                196,
                66,
                152,
                252,
                28,
                20,
                154,
                251,
                244,
                200,
                153,
                111,
                185,
                36,
                39,
                174,
                65,
                228,
                100,
                155,
                147,
                76,
                164,
                149,
                153,
                27,
                120,
                82,
                184,
                85,
            ],
        ),
        (
            [10, 20],
            [
                195,
                48,
                250,
                117,
                58,
                197,
                190,
                59,
                143,
                203,
                82,
                116,
                80,
                98,
                247,
                129,
                204,
                158,
                15,
                79,
                169,
                129,
                162,
                189,
                6,
                252,
                185,
                105,
                53,
                91,
                148,
                105,
            ],
        ),
    ),
)
def test_sha256(input_list, expected_result):
    assert sha256(input_list) == expected_result


def test_sha_symbol():
    input_list = ["bab", symbol_factory.BitVecSym("name", 256)]
    with pytest.raises(NativeContractException):
        sha256(input_list)
