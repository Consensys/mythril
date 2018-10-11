import pytest
from z3 import BoolVal, IntVal
from mythril.laser.ethereum.smt_wrapper import \
    NotConcreteValueError, get_concrete_value, \
    BitVec, BitVecVal, Concat, Extract, \
    Eq, Neq, SLT, SGT, ULT, UGT, UDiv, SDiv, URem, SRem, \
    Not, And, Or, \
    SimplificationError, \
    is_expr, is_bv_value, is_bv, is_bool, is_true, is_false
from mythril.laser.ethereum.smt_wrapper import simplify as simplify_wrapper


def test_get_concrete_value_succ():
    x = BitVecVal(0x100, 256)
    v = get_concrete_value(x)
    assert (v == 0x100)


def test_get_concrete_value_of_bv():
    x = BitVec("x", 256)
    with pytest.raises(NotConcreteValueError):
        get_concrete_value(x)


def test_get_concrete_value_of_int():
    with pytest.raises(NotConcreteValueError):
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


def test_SDiv():
    operands = [BitVecVal(0x1, 256), 0x1, True]

    dividend = operands[0]
    for divisor in operands:
        SDiv(dividend, divisor)

    divisor = operands[0]
    for dividend in operands:
        SDiv(dividend, divisor)


def test_SDiv_type_error():
    with pytest.raises(TypeError):
        SDiv(0x1, 0x2)


def test_simplify():
    simpl = simplify_wrapper(BitVecVal(0x10, 256) + BitVecVal(0x20, 256))
    assert (get_concrete_value(simpl) == 0x30)


def test_simplify_error():
    with pytest.raises(SimplificationError):
        simplify_wrapper(1 + 1 == 2)


def test_is_bv():
    assert (is_bv(BitVec("x", 256)))
    assert (is_bv(BitVecVal(0x100, 256)))
    assert (is_bv(BitVec("x", 256) + BitVecVal(0x100, 256)))
    assert (is_bv(BitVec("x", 256) + 0x100))
    assert (not is_bv(IntVal(0x100)))
    assert (not is_bv(BoolVal(False)))
    assert (not is_bv(0x100))
    assert (not is_bv(False))


def test_is_true():
    assert (is_true(BoolVal(True)))
    assert (not is_true(True))


def test_is_false():
    assert (is_false(BoolVal(False)))
    assert (not is_false(False))


def test_Not():
    Not(BoolVal(False))
    Not(False)


def test_Concat():
    bv0 = BitVecVal(0xffff, 16)
    bv1 = BitVecVal(0xeeee, 16)
    bv = Concat(bv0, bv1)
    assert (get_concrete_value(simplify_wrapper(bv)) == 0xffffeeee)


def test_Extract():
    bv0 = BitVecVal(0xffffeeee, 32)
    bv = Extract(31, 16, bv0)
    assert (get_concrete_value(simplify_wrapper(bv)) == 0xffff)


def test_And():
    operands = [BoolVal(True), True]
    for lhs, rhs in zip(operands, operands):
        And(lhs, rhs)


def test_Or():
    operands = [BoolVal(True), True]
    for lhs, rhs in zip(operands, operands):
        Or(lhs, rhs)


def test_ULT():
    operands = [BitVecVal(0x1, 256), 0x1, True]

    lhs = operands[0]
    for rhs in operands:
        ULT(lhs, rhs)

    rhs = operands[0]
    for lhs in operands:
        ULT(lhs, rhs)


def test_ULT_type_error():
    with pytest.raises(TypeError):
        ULT(0x2, 0x1)


def test_UGT():
    operands = [BitVecVal(0x1, 256), 0x1, True]

    lhs = operands[0]
    for rhs in operands:
        UGT(lhs, rhs)

    rhs = operands[0]
    for lhs in operands:
        UGT(lhs, rhs)


def test_UGT_type_error():
    with pytest.raises(TypeError):
        UGT(0x2, 0x1)


def test_UDiv():
    operands = [BitVecVal(0x1, 256), 0x1, True]

    dividend = operands[0]
    for divisor in operands:
        UDiv(dividend, divisor)

    divisor = operands[0]
    for dividend in operands:
        UDiv(dividend, divisor)


def test_UDiv_type_error():
    with pytest.raises(TypeError):
        UDiv(0x1, 0x2)


def test_URem():
    operands = [BitVecVal(0x1, 256), 0x1, True]

    dividend = operands[0]
    for divisor in operands:
        URem(dividend, divisor)

    divisor = operands[0]
    for dividend in operands:
        URem(dividend, divisor)


def test_URem_type_error():
    with pytest.raises(TypeError):
        URem(0x1, 0x2)


def test_SRem():
    operands = [BitVecVal(0x1, 256), 0x1, True]

    dividend = operands[0]
    for divisor in operands:
        SRem(dividend, divisor)

    divisor = operands[0]
    for dividend in operands:
        SRem(dividend, divisor)


def test_SRem_type_error():
    with pytest.raises(TypeError):
        SRem(0x1, 0x2)
