from mock import patch
from eth_utils import decode_hex
from mythril.laser.ethereum.natives import ec_mul
from py_ecc.optimized_bn128 import FQ

VECTOR_A = decode_hex(
    "0000000000000000000000000000000000000000000000000000000000000001"
    "0000000000000000000000000000000000000000000000000000000000000020"
    "0000000000000000000000000000000000000000000000000000000000000020"
    "03"
    "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2e"
    "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f"
)


@patch("mythril.laser.ethereum.natives.validate_point", return_value=1)
@patch("mythril.laser.ethereum.natives.bn128.multiply", return_value=1)
@patch("mythril.laser.ethereum.natives.bn128.normalize")
def test_ec_mul(f1, f2, f3):
    FQ.fielf_modulus = 128
    a = FQ(val=1)
    f1.return_value = (a, a)
    assert ec_mul(VECTOR_A) == ([0] * 31 + [1]) * 2


def test_ec_mul_validation_failure():
    assert ec_mul(VECTOR_A) == []
