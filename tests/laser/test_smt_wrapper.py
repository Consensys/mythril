import pytest
from z3 import BitVec, BitVecVal, BoolVal, IntVal, is_bool, is_bv_value, is_expr
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


def test_is_bv_value():
    assert (is_bv_value(BitVecVal(0x100, 256)))
    assert (not is_bv_value(BitVec("x", 256)))
    assert (not is_bv_value(IntVal(0x100)))
    assert (not is_bv_value(0x100))


def test_is_expr():
    assert (is_expr(BitVecVal(0x100, 256)))
    assert (is_expr(BitVec("x", 256)))
    assert (not is_expr(0x100))
