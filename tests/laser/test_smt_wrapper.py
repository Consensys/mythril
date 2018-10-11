import pytest
from z3 import BitVec, BitVecVal
from mythril.laser.ethereum.smt_wrapper import \
    NotConcreteValueError, get_concrete_value


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
