from mock import patch
from eth_utils import decode_hex
from mythril.laser.ethereum.natives import ec_add
from py_ecc.optimized_bn128 import FQ

VECTOR_A = decode_hex(
    "0000000000000000000000000000000000000000000000000000000000000001"
    "0000000000000000000000000000000000000000000000000000000000000020"
    "0000000000000000000000000000000000000000000000000000000000000020"
    "03"
    "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2e"
    "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f"
)


def test_ec_add_sanity():
    assert ec_add(VECTOR_A) == []


@patch("mythril.laser.ethereum.natives.validate_point", return_value=1)
@patch("mythril.laser.ethereum.natives.bn128.add", return_value=1)
@patch("mythril.laser.ethereum.natives.bn128.normalize")
def test_ec_add(f1, f2, f3):
    FQ.fielf_modulus = 128
    a = FQ(val=1)
    f1.return_value = (a, a)
    assert ec_add(VECTOR_A) == [
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
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        1,
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
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        1,
    ]
