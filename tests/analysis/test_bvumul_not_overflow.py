import pytest
from z3 import And, BitVec, BitVecVal, Extract, Not, Solver, sat, unsat
from mythril.analysis.modules.integer import _bvumul_not_overflow


def _assert_overflow(op0, op1, expected, assumptions=[]) -> bool:
    s = Solver()
    s.add(Not(_bvumul_not_overflow(op0, op1)))
    for a in assumptions:
        s.add(a)
    assert s.check() == expected


def _assert_not_overflow(op0, op1, expected, assumptions=[]) -> bool:
    s = Solver()
    s.add(_bvumul_not_overflow(op0, op1))
    for a in assumptions:
        s.add(a)
    assert s.check() == expected


def _assert_overflow_sat(op0, op1, assumptions=[]) -> bool:
    _assert_overflow(op0, op1, sat, assumptions)


def _assert_overflow_unsat(op0, op1, assumptions=[]) -> bool:
    _assert_overflow(op0, op1, unsat, assumptions)


def _assert_not_overflow_sat(op0, op1, assumptions=[]) -> bool:
    _assert_not_overflow(op0, op1, sat, assumptions)


def _assert_not_overflow_unsat(op0, op1, assumptions=[]) -> bool:
    _assert_not_overflow(op0, op1, unsat, assumptions)


def test_bvumul_1_bit_not_overflow():
    ops = [BitVecVal(0, 1), BitVecVal(1, 1), BitVec("x", 1), BitVec("y", 1)]
    for op0 in ops:
        for op1 in ops:
            _assert_not_overflow_sat(op0, op1)
            _assert_overflow_unsat(op0, op1)


def test_bvumul_not_overflow():
    ops = [BitVecVal(0xF, 32), BitVec("x", 32)]
    for op0 in ops:
        for op1 in ops:
            _assert_not_overflow_sat(op0, op1)


def test_bvumul_overflow():
    ops = [BitVecVal(0xFFFFF, 32), BitVec("x", 32)]
    for op0 in ops:
        for op1 in ops:
            _assert_overflow_sat(op0, op1)


def test_bvumul_0x7f_0x4_overflow():
    op0 = BitVec("x", 8)
    op1 = BitVec("y", 8)
    assumptions = [op0 == BitVecVal(0x7F, 8), op1 == BitVecVal(0x4, 8)]
    _assert_overflow_sat(op0, op1, assumptions)


def test_bvumul_zero_not_overflow():
    ops = [BitVecVal(0xFFFFFFFF, 32), BitVec("x", 32)]
    for op in ops:
        _assert_not_overflow_sat(op, BitVecVal(0, 32))
        _assert_overflow_unsat(op, BitVecVal(0, 32))
        _assert_not_overflow_sat(BitVecVal(0, 32), op)
        _assert_overflow_unsat(BitVecVal(0, 32), op)


def test_bvumul_one_not_overflow():
    ops = [BitVecVal(0xFFFFFFFF, 32), BitVec("x", 32)]
    for op in ops:
        _assert_not_overflow_sat(op, BitVecVal(1, 32))
        _assert_overflow_unsat(op, BitVecVal(0, 32))
        _assert_not_overflow_sat(BitVecVal(1, 32), op)
        _assert_overflow_unsat(BitVecVal(0, 32), op)


def test_bvumul_msb_always_overflow():
    op0 = BitVec("op0", 4)
    op1 = BitVec("op1", 4)
    for i in range(1, 4):
        assumptions = [Extract(i, i, op0) == BitVecVal(1, 1)]
        for j in range(4 - i + 1, 4):
            assumptions.append(Extract(j, j, op1) == BitVecVal(1, 1))
            _assert_overflow_sat(op0, op1, assumptions)
            _assert_not_overflow_unsat(op0, op1, assumptions)


def test_bvumul_msb_never_overflow():
    op0 = BitVec("op0", 4)
    op1 = BitVec("op1", 4)
    for i in range(1, 4):
        assumption = And(
            Extract(3, i, op0) == BitVecVal(1, 4 - i),
            Extract(3, 4 - i, op1) == BitVecVal(0, i),
        )
        _assert_not_overflow_sat(op0, op1, [assumption])
        _assert_overflow_unsat(op0, op1, [assumption])


def test_bvumul_msb_may_overflow():
    op0 = BitVec("op0", 4)
    op1 = BitVec("op1", 4)
    for i in range(1, 4):
        assumption = And(
            Extract(3, i, op0) == BitVecVal(1, 4 - i),
            Extract(3, 4 - i, op1) == BitVecVal(1, i),
        )
        _assert_overflow_sat(op0, op1, [assumption])
