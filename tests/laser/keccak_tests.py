from mythril.laser.smt import Solver, symbol_factory, And
from mythril.laser.ethereum.function_managers import keccak_function_manager
import z3
import pytest


@pytest.mark.parametrize(
    "input1, input2, expected",
    [
        (symbol_factory.BitVecVal(100, 8), symbol_factory.BitVecVal(101, 8), z3.unsat),
        (symbol_factory.BitVecVal(100, 8), symbol_factory.BitVecVal(100, 16), z3.unsat),
        (symbol_factory.BitVecVal(100, 8), symbol_factory.BitVecVal(100, 8), z3.sat),
        (
            symbol_factory.BitVecSym("N1", 256),
            symbol_factory.BitVecSym("N2", 256),
            z3.sat,
        ),
        (
            symbol_factory.BitVecVal(100, 256),
            symbol_factory.BitVecSym("N1", 256),
            z3.sat,
        ),
        (
            symbol_factory.BitVecVal(100, 8),
            symbol_factory.BitVecSym("N1", 256),
            z3.unsat,
        ),
    ],
)
def test_keccak_basic(input1, input2, expected):
    s = Solver()

    o1, c1 = keccak_function_manager.create_keccak(input1)
    o2, c2 = keccak_function_manager.create_keccak(input2)
    s.add(And(c1, c2))

    s.add(o1 == o2)
    assert s.check() == expected


def test_keccak_symbol_and_val():
    """
    check keccak(100) == keccak(n) && n == 10
    :return:
    """
    s = Solver()
    hundred = symbol_factory.BitVecVal(100, 256)
    n = symbol_factory.BitVecSym("n", 256)
    o1, c1 = keccak_function_manager.create_keccak(hundred)
    o2, c2 = keccak_function_manager.create_keccak(n)
    s.add(And(c1, c2))
    s.add(o1 == o2)
    s.add(n == symbol_factory.BitVecVal(10, 256))
    assert s.check() == z3.unsat


def test_keccak_complex_eq():
    """
    check for keccak(keccak(b)*2) == keccak(keccak(a)*2) && a != b
    :return:
    """
    s = Solver()
    a = symbol_factory.BitVecSym("a", 160)
    b = symbol_factory.BitVecSym("b", 160)
    o1, c1 = keccak_function_manager.create_keccak(a)
    o2, c2 = keccak_function_manager.create_keccak(b)
    s.add(And(c1, c2))
    two = symbol_factory.BitVecVal(2, 256)
    o1 = two * o1
    o2 = two * o2
    o1, c1 = keccak_function_manager.create_keccak(o1)
    o2, c2 = keccak_function_manager.create_keccak(o2)

    s.add(And(c1, c2))
    s.add(o1 == o2)
    s.add(a != b)

    assert s.check() == z3.unsat


def test_keccak_complex_eq2():
    """
    check for keccak(keccak(b)*2) == keccak(keccak(a)*2)
    This isn't combined with prev test because incremental solving here requires extra-extra work
    (solution is literally the opposite of prev one) so it will take forever to solve.
    :return:
    """
    s = Solver()
    a = symbol_factory.BitVecSym("a", 160)
    b = symbol_factory.BitVecSym("b", 160)
    o1, c1 = keccak_function_manager.create_keccak(a)
    o2, c2 = keccak_function_manager.create_keccak(b)
    s.add(And(c1, c2))
    two = symbol_factory.BitVecVal(2, 256)
    o1 = two * o1
    o2 = two * o2
    o1, c1 = keccak_function_manager.create_keccak(o1)
    o2, c2 = keccak_function_manager.create_keccak(o2)

    s.add(And(c1, c2))
    s.add(o1 == o2)

    assert s.check() == z3.sat


def test_keccak_simple_number():
    """
    check for keccak(b) == 10
    :return:
    """
    s = Solver()
    a = symbol_factory.BitVecSym("a", 160)
    ten = symbol_factory.BitVecVal(10, 256)
    o, c = keccak_function_manager.create_keccak(a)

    s.add(c)
    s.add(ten == o)

    assert s.check() == z3.unsat


def test_keccak_other_num():
    """
    check keccak(keccak(a)*2) == b
    :return:
    """
    s = Solver()
    a = symbol_factory.BitVecSym("a", 160)
    b = symbol_factory.BitVecSym("b", 256)
    o, c = keccak_function_manager.create_keccak(a)
    two = symbol_factory.BitVecVal(2, 256)
    o = two * o
    s.add(c)
    o, c = keccak_function_manager.create_keccak(o)
    s.add(c)
    s.add(b == o)

    assert s.check() == z3.sat
