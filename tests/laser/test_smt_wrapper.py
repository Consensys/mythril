import pytest
from z3 import BitVec, BitVecVal, BoolVal, IntVal, is_bool, is_bv_value, is_expr
from mythril.laser.ethereum.smt_wrapper import \
    get_concrete_value, \
    Eq, Neq, SLT, SGT


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


def test_Eq():
    operands = [BitVecVal(0x1, 256), IntVal(0x1), BoolVal(False), 0x1, True]
    for lhs, rhs in zip(operands, operands):
        Eq(lhs, rhs)


def test_Eq_type_error():
    with pytest.raises(Exception):
        Eq(BitVecVal(0x1, 256), "x")


def test_Neq():
    operands = [BitVecVal(0x1, 256), IntVal(0x1), BoolVal(False), 0x1, True]
    for lhs, rhs in zip(operands, operands):
        Neq(lhs, rhs)


def test_Neq_type_error():
    with pytest.raises(Exception):
        Neq(BitVecVal(0x1, 256), "x")


def test_SLT():
    operands = [BitVecVal(0x1, 256), 0x1, True]

    lhs = operands[0]
    for rhs in operands:
        SLT(lhs, rhs)

    rhs = operands[0]
    for lhs in operands:
        SLT(lhs, rhs)


def test_SLT_type_error():
    with pytest.raises(TypeError):
        SLT(0x0, 0x1)


def test_SGT():
    operands = [BitVecVal(0x1, 256), 0x1, True]

    lhs = operands[0]
    for rhs in operands:
        SGT(lhs, rhs)

    rhs = operands[0]
    for lhs in operands:
        SGT(lhs, rhs)


def test_SGT_type_error():
    with pytest.raises(TypeError):
        SGT(0x0, 0x1)
