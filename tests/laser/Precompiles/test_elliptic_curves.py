from mock import patch
from mythril.laser.ethereum.natives import ec_pair
from py_ecc.optimized_bn128 import FQ


def test_ec_pair_192_check():
    vec_c = [0] * 100
    assert ec_pair(vec_c) == []


@patch("mythril.laser.ethereum.natives.validate_point", return_value=1)
@patch("mythril.laser.ethereum.natives.bn128.is_on_curve", return_value=True)
@patch("mythril.laser.ethereum.natives.bn128.pairing", return_value=1)
@patch("mythril.laser.ethereum.natives.bn128.normalize")
def test_ec_pair(f1, f2, f3, f4):
    FQ.fielf_modulus = 100
    a = FQ(val=1)
    f1.return_value = (a, a)
    vec_c = [0] * 192
    assert ec_pair(vec_c) == [0] * 31 + [1]


@patch("mythril.laser.ethereum.natives.validate_point", return_value=False)
def test_ec_pair_point_validation_failure(f1):
    vec_c = [0] * 192
    assert ec_pair(vec_c) == []


@patch("mythril.laser.ethereum.natives.validate_point", return_value=1)
def test_ec_pair_field_exceed_mod(f1):
    FQ.fielf_modulus = 100
    a = FQ(val=1)
    f1.return_value = (a, a)
    vec_c = [10] * 192
    assert ec_pair(vec_c) == []
