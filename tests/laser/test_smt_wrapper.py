import pytest

from pysmt.shortcuts import \
    reset_env, get_env, Bool, Int

from mythril.laser.ethereum.smt_wrapper import \
    NotConcreteValueError, get_concrete_value, \
    BitVec, BitVecVal, Concat, Extract, \
    Eq, Neq, SLT, SGT, ULT, UGT, UDiv, SDiv, URem, SRem, \
    Not, And, Or, \
    SimplificationError, \
    is_expr, is_bv_value, is_bv, is_bool, is_true, is_false, \
    Result, solve, Solver
from mythril.laser.ethereum.smt_wrapper import simplify as simplify_wrapper


@pytest.fixture
def reset_pysmt_env():
    reset_env()
    get_env().enable_infix_notation = True


def test_get_concrete_value_succ(reset_pysmt_env):
    x = BitVecVal(0x100, 256)
    v = get_concrete_value(x)
    assert (v == 0x100)


def test_get_concrete_value_of_bv(reset_pysmt_env):
    x = BitVec("x", 256)
    with pytest.raises(NotConcreteValueError):
        get_concrete_value(x)


def test_get_concrete_value_of_int(reset_pysmt_env):
    with pytest.raises(NotConcreteValueError):
        get_concrete_value(10)


def test_is_bool(reset_pysmt_env):
    assert (is_bool(Bool(False)))
    assert (not is_bool(BitVec("x", 256)))
    assert (not is_bool(Int(1)))
    assert (not is_bool(True))
    assert (not is_bool(1))


def test_is_bv_value(reset_pysmt_env):
    assert (is_bv_value(BitVecVal(0x100, 256)))
    assert (not is_bv_value(BitVec("x", 256)))
    assert (not is_bv_value(Int(0x100)))
    assert (not is_bv_value(0x100))


def test_is_expr(reset_pysmt_env):
    assert (is_expr(BitVecVal(0x100, 256)))
    assert (is_expr(BitVec("x", 256)))
    assert (not is_expr(0x100))


def test_Eq(reset_pysmt_env):
    operands = [BitVecVal(0x1, 256), Int(0x1), Bool(False), 0x1, True]
    for lhs, rhs in zip(operands, operands):
        Eq(lhs, rhs)


def test_Eq_type_error(reset_pysmt_env):
    with pytest.raises(Exception):
        Eq(BitVecVal(0x1, 256), "x")


def test_Neq(reset_pysmt_env):
    operands = [BitVecVal(0x1, 256), Int(0x1), Bool(False), 0x1, True]
    for lhs, rhs in zip(operands, operands):
        Neq(lhs, rhs)


def test_Neq_type_error(reset_pysmt_env):
    with pytest.raises(Exception):
        Neq(BitVecVal(0x1, 256), "x")


def test_SLT(reset_pysmt_env):
    operands = [BitVecVal(0x1, 256), Int(0x1), 0x1, Bool(True), True]

    lhs = operands[0]
    for rhs in operands:
        SLT(lhs, rhs)

    rhs = operands[0]
    for lhs in operands:
        SLT(lhs, rhs)


def test_SLT_type_error(reset_pysmt_env):
    with pytest.raises(TypeError):
        SLT(0x0, 0x1)


def test_SGT(reset_pysmt_env):
    operands = [BitVecVal(0x1, 256), Int(0x1), 0x1, Bool(True), True]

    lhs = operands[0]
    for rhs in operands:
        SGT(lhs, rhs)

    rhs = operands[0]
    for lhs in operands:
        SGT(lhs, rhs)


def test_SGT_type_error(reset_pysmt_env):
    with pytest.raises(TypeError):
        SGT(0x0, 0x1)


def test_SDiv(reset_pysmt_env):
    operands = [BitVecVal(0x1, 256), Int(0x1), 0x1, Bool(True), True]

    dividend = operands[0]
    for divisor in operands:
        SDiv(dividend, divisor)

    divisor = operands[0]
    for dividend in operands:
        SDiv(dividend, divisor)


def test_SDiv_type_error(reset_pysmt_env):
    with pytest.raises(TypeError):
        SDiv(0x1, 0x2)


def test_simplify(reset_pysmt_env):
    simpl = simplify_wrapper(BitVecVal(0x10, 256) + BitVecVal(0x20, 256))
    assert (get_concrete_value(simpl) == 0x30)


def test_simplify_error(reset_pysmt_env):
    with pytest.raises(SimplificationError):
        simplify_wrapper(1 + 1 == 2)


def test_is_bv(reset_pysmt_env):
    assert (is_bv(BitVec("x", 256)))
    assert (is_bv(BitVecVal(0x100, 256)))
    assert (is_bv(BitVec("x", 256) + BitVecVal(0x100, 256)))
    assert (is_bv(BitVec("x", 256) + 0x100))
    assert (not is_bv(Int(0x100)))
    assert (not is_bv(Bool(False)))
    assert (not is_bv(0x100))
    assert (not is_bv(False))


def test_is_true(reset_pysmt_env):
    assert (is_true(Bool(True)))
    assert (not is_true(True))


def test_is_false(reset_pysmt_env):
    assert (is_false(Bool(False)))
    assert (not is_false(False))


def test_Not(reset_pysmt_env):
    Not(Bool(False))
    Not(False)


def test_Concat(reset_pysmt_env):
    bv0 = BitVecVal(0xffff, 16)
    bv1 = BitVecVal(0xeeee, 16)
    bv = Concat(bv0, bv1)
    assert (get_concrete_value(simplify_wrapper(bv)) == 0xffffeeee)


def test_Extract(reset_pysmt_env):
    bv0 = BitVecVal(0xffffeeee, 32)
    bv = Extract(31, 16, bv0)
    assert (get_concrete_value(simplify_wrapper(bv)) == 0xffff)


def test_And(reset_pysmt_env):
    operands = [Bool(True), True]
    for lhs, rhs in zip(operands, operands):
        And(lhs, rhs)


def test_Or(reset_pysmt_env):
    operands = [Bool(True), True]
    for lhs, rhs in zip(operands, operands):
        Or(lhs, rhs)


def test_ULT(reset_pysmt_env):
    operands = [BitVecVal(0x1, 256), Int(0x1), 0x1, Bool(True), True]

    lhs = operands[0]
    for rhs in operands:
        ULT(lhs, rhs)

    rhs = operands[0]
    for lhs in operands:
        ULT(lhs, rhs)


def test_ULT_type_error(reset_pysmt_env):
    with pytest.raises(TypeError):
        ULT(0x2, 0x1)


def test_UGT(reset_pysmt_env):
    operands = [BitVecVal(0x1, 256), Int(0x1), 0x1, Bool(True), True]

    lhs = operands[0]
    for rhs in operands:
        UGT(lhs, rhs)

    rhs = operands[0]
    for lhs in operands:
        UGT(lhs, rhs)


def test_UGT_type_error(reset_pysmt_env):
    with pytest.raises(TypeError):
        UGT(0x2, 0x1)


def test_UDiv(reset_pysmt_env):
    operands = [BitVecVal(0x1, 256), Int(0x1), 0x1, Bool(True), True]

    dividend = operands[0]
    for divisor in operands:
        UDiv(dividend, divisor)

    divisor = operands[0]
    for dividend in operands:
        UDiv(dividend, divisor)


def test_UDiv_type_error(reset_pysmt_env):
    with pytest.raises(TypeError):
        UDiv(0x1, 0x2)


def test_URem(reset_pysmt_env):
    operands = [BitVecVal(0x1, 256), Int(0x1), 0x1, Bool(True), True]

    dividend = operands[0]
    for divisor in operands:
        URem(dividend, divisor)

    divisor = operands[0]
    for dividend in operands:
        URem(dividend, divisor)


def test_URem_type_error(reset_pysmt_env):
    with pytest.raises(TypeError):
        URem(0x1, 0x2)


def test_SRem(reset_pysmt_env):
    operands = [BitVecVal(0x1, 256), Int(0x1), 0x1, Bool(True), True]

    dividend = operands[0]
    for divisor in operands:
        SRem(dividend, divisor)

    divisor = operands[0]
    for dividend in operands:
        SRem(dividend, divisor)


def test_SRem_type_error(reset_pysmt_env):
    with pytest.raises(TypeError):
        SRem(0x1, 0x2)


def test_solve(reset_pysmt_env):
    x = BitVec("x", 256)
    y = BitVec("y", 256)
    z = BitVec("z", 256)

    s = Solver()
    s.push()
    s.add_assertion(ULT(x, y))  # x < y
    s.add_assertion(ULT(y, z))  # y < z
    result = solve(s)
    s.pop()
    assert (result == Result.sat)

    s.push()
    s.add_assertion(ULT(x, y))  # x < y
    s.add_assertion(ULT(y, z))  # y < z
    s.add_assertion(ULT(z, x))  # z < x
    result = solve(s)
    s.pop()
    assert (result == Result.unsat)

    s = Solver(timeout=1)
    s.add_assertion(Eq(x * x + y * y, z * z)) # x^2 + y^2 = z^2
    s.add_assertion(ULT(0, x))                # x > 0
    s.add_assertion(ULT(0, y))                # y > 0
    s.add_assertion(ULT(0, z))                # z > 0
    result = solve(s)
    assert (result == Result.unknown)
