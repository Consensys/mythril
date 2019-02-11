from mythril.laser.smt import Solver, symbol_factory, bitvec
import z3
import pytest

import operator


@pytest.mark.parametrize(
    "operation,expected",
    [
        (operator.add, z3.unsat),
        (operator.sub, z3.unsat),
        (operator.and_, z3.sat),
        (operator.or_, z3.sat),
        (operator.xor, z3.unsat),
    ],
)
def test_bitvecfunc_arithmetic(operation, expected):
    # Arrange
    s = Solver()

    input_ = symbol_factory.BitVecVal(1, 8)
    bvf = symbol_factory.BitVecFuncSym("bvf", "sha3", 256, input_=input_)

    x = symbol_factory.BitVecSym("x", 256)
    y = symbol_factory.BitVecSym("y", 256)

    # Act
    s.add(x != y)
    s.add(operation(bvf, x) == operation(y, bvf))

    # Assert
    assert s.check() == expected


@pytest.mark.parametrize(
    "operation,expected",
    [
        (operator.eq, z3.sat),
        (operator.ne, z3.unsat),
        (operator.lt, z3.unsat),
        (operator.le, z3.sat),
        (operator.gt, z3.unsat),
        (operator.ge, z3.sat),
        (bitvec.UGT, z3.unsat),
        (bitvec.UGE, z3.sat),
        (bitvec.ULT, z3.unsat),
        (bitvec.ULE, z3.sat),
    ],
)
def test_bitvecfunc_bitvecfunc_comparison(operation, expected):
    # Arrange
    s = Solver()

    input1 = symbol_factory.BitVecSym("input1", 256)
    input2 = symbol_factory.BitVecSym("input2", 256)
    bvf1 = symbol_factory.BitVecFuncSym("bvf1", "sha3", 256, input_=input1)
    bvf2 = symbol_factory.BitVecFuncSym("bvf2", "sha3", 256, input_=input2)

    # Act
    s.add(operation(bvf1, bvf2))
    s.add(input1 == input2)

    # Assert
    assert s.check() == expected


def test_bitvecfunc_bitvecfuncval_comparison():
    # Arrange
    s = Solver()

    input1 = symbol_factory.BitVecSym("input1", 256)
    input2 = symbol_factory.BitVecVal(1337, 256)
    bvf1 = symbol_factory.BitVecFuncSym("bvf1", "sha3", 256, input_=input1)
    bvf2 = symbol_factory.BitVecFuncVal(12345678910, "sha3", 256, input_=input2)

    # Act
    s.add(bvf1 == bvf2)

    # Assert
    assert s.check() == z3.sat
    assert s.model().eval(input2.raw) == 1337
