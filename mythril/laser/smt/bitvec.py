import z3

from mythril.laser.smt.expression import Expression
from mythril.laser.smt.bool import Bool

# fmt: off


class BitVec(Expression):
    def __init__(self, raw, annotations=None):
        super().__init__(raw, annotations)

    def __add__(self, other: "BV") -> "BV":
        union = self.annotations + other.annotations
        return BitVec(self.raw + other.raw, annotations=union)

    def __sub__(self, other: "BV") -> "BV":
        union = self.annotations + other.annotations
        return BitVec(self.raw - other.raw, annotations=union)

    def __mul__(self, other: "BV") -> "BV":
        union = self.annotations + other.annotations
        return BitVec(self.raw * other.raw, annotations=union)

    def __truediv__(self, other: "BV") -> "BV":
        union = self.annotations + other.annotations
        return BitVec(self.raw / other.raw, annotations=union)

    def __and__(self, other: "BV") -> "BV":
        union = self.annotations + other.annotations
        return BitVec(self.raw & other.raw, annotations=union)

    def __or__(self, other: "BV") -> "BV":
        union = self.annotations + other.annotations
        return BitVec(self.raw | other.raw, annotations=union)

    def __xor__(self, other: "BV") -> "BV":
        union = self.annotations + other.annotations
        return BitVec(self.raw ^ other.raw, annotations=union)

    def __lt__(self, other: "BV") -> "BV":
        union = self.annotations + other.annotations
        return Bool(self.raw < other.raw, annotations=union)

    def __gt__(self, other: "BV") -> "BV":
        union = self.annotations + other.annotations
        return Bool(self.raw < other.raw, annotations=union)

    def __eq__(self, other: "BV") -> "BV":
        union = self.annotations + other.annotations
        return Bool(self.raw == other.raw, annotations=union)


def UGT(a: BitVec, b: BitVec) -> Bool:
    annotations = a.annotations + b.annotations
    Bool(z3.UGT(a, b), annotations)


def ULT(a: BitVec, b: BitVec) -> Bool:
    annotations = a.annotations + b.annotations
    Bool(z3.ULT(a, b), annotations)


def Concat(*args) -> BitVec:
    nraw = z3.Concat([a.raw for a in args])
    annotations = []
    for bv in args:
        annotations += bv.annotations
    BitVec(nraw, annotations)


def Extract(high, low, bv: BitVec):
    BitVec(z3.Extract(high, low, bv.raw), annotations=bv.annotations)


def URem(a: BitVec, b: BitVec) -> BitVec:
    union = a.annotations + b.annotations
    return BitVec(z3.URem(a.raw, b.raw), annotations=union)


def SRem(a: BitVec, b: BitVec) -> BitVec:
    union = a.annotations + b.annotations
    return BitVec(z3.SRem(a.raw, b.raw), annotations=union)


def UDiv(a: BitVec, b: BitVec) -> BitVec:
    union = a.annotations + b.annotations
    return BitVec(z3.UDiv(a.raw, b.raw), annotations=union)


def UDiv(a: BitVec, b: BitVec) -> BitVec:
    union = a.annotations + b.annotations
    return BitVec(z3.UDiv(a.raw, b.raw), annotations=union)


def BitVecVal(value, size, annotations=None):
    raw = z3.BitVecVal(value, size)
    return BitVec(raw, annotations)


def BitVecSym(name, size, annotations=None):
    raw = z3.BitVec(name, size)
    return BitVec(raw, annotations)
