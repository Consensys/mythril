import pytest
from z3 import BitVec, BitVecVal, BoolVal, IntVal, is_bool
from mythril.laser.ethereum.smt_wrapper import \
    get_concrete_value


def test_get_concrete_value_succ():
    x = BitVecVal(0x100, 256)
    v = get_concrete_value(x)
    assert (v == 0x100)


def test_get_concrete_value_of_bv():
    x = BitVec("x", 256)
    with pytest.raises(TypeError):
        get_concrete_value(x)


def test_get_concrete_value_of_int():
    with pytest.raises(TypeError):
        get_concrete_value(10)


def test_is_bool():
    assert (is_bool(BoolVal(False)))
    assert (not is_bool(BitVec("x", 256)))
    assert (not is_bool(IntVal(1)))
    assert (not is_bool(True))
    assert (not is_bool(1))
