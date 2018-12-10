import z3

from mythril.laser.smt.expression import Expression
from mythril.laser.smt.bool import Bool

# fmt: off


class BitVec(Expression):
    """
    Bit vector symbol
    """
    def __init__(self, raw, annotations=None):
        super().__init__(raw, annotations)

    @property
    def symbolic(self):
        """ Returns whether this symbol doesn't have a concrete value """
        self.simplify()
        return not isinstance(self.raw, z3.BitVecNumRef)

    @property
    def value(self):
        """ Returns the value of this symbol if concrete, otherwise None"""
        if self.symbolic:
            return None
        assert isinstance(self.raw, z3.BitVecNumRef)
        return self.raw.as_long()

    def __add__(self, other: "BV") -> "BV":
        """ Create an addition expression """
        union = self.annotations + other.annotations
        return BitVec(self.raw + other.raw, annotations=union)

    def __sub__(self, other: "BV") -> "BV":
        """ Create a subtraction expression """
        union = self.annotations + other.annotations
        return BitVec(self.raw - other.raw, annotations=union)

    def __mul__(self, other: "BV") -> "BV":
        """ Create a multiplication expression """
        union = self.annotations + other.annotations
        return BitVec(self.raw * other.raw, annotations=union)

    def __truediv__(self, other: "BV") -> "BV":
        """ Create a signed division expression """
        union = self.annotations + other.annotations
        return BitVec(self.raw / other.raw, annotations=union)

    def __and__(self, other: "BV") -> "BV":
        """ Create an and expression """
        union = self.annotations + other.annotations
        return BitVec(self.raw & other.raw, annotations=union)

    def __or__(self, other: "BV") -> "BV":
        """ Create an or expression """
        union = self.annotations + other.annotations
        return BitVec(self.raw | other.raw, annotations=union)

    def __xor__(self, other: "BV") -> "BV":
        """ Create a xor expression """
        union = self.annotations + other.annotations
        return BitVec(self.raw ^ other.raw, annotations=union)

    def __lt__(self, other: "BV") -> Bool:
        """ Create a signed less than expression """
        union = self.annotations + other.annotations
        return Bool(self.raw < other.raw, annotations=union)

    def __gt__(self, other: "BV") -> Bool:
        """ Create a signed greater than expression """
        union = self.annotations + other.annotations
        return Bool(self.raw < other.raw, annotations=union)

    def __eq__(self, other: "BV") -> Bool:
        """ Create an equality expression """
        union = self.annotations + other.annotations
        return Bool(self.raw == other.raw, annotations=union)


def If(a: Bool, b: BitVec, c: BitVec):
    """ Create an if-then-else expression """
    union = a.annotations + b.annotations + c.annotations
    return BitVec(z3.If(a, b, c), union)


def UGT(a: BitVec, b: BitVec) -> Bool:
    """ Create an unsigned greater than expression """
    annotations = a.annotations + b.annotations
    return Bool(z3.UGT(a, b), annotations)


def ULT(a: BitVec, b: BitVec) -> Bool:
    """ Create an unsigned less than expression """
    annotations = a.annotations + b.annotations
    return Bool(z3.ULT(a, b), annotations)


def Concat(*args) -> BitVec:
    """ Create a concatenation expression """
    nraw = z3.Concat([a.raw for a in args])
    annotations = []
    for bv in args:
        annotations += bv.annotations
    return BitVec(nraw, annotations)


def Extract(high: int, low: int, bv: BitVec) -> BitVec:
    """ Create an extract expression"""
    return BitVec(z3.Extract(high, low, bv.raw), annotations=bv.annotations)


def URem(a: BitVec, b: BitVec) -> BitVec:
    """ Create an unsigned remainder expression"""
    union = a.annotations + b.annotations
    return BitVec(z3.URem(a.raw, b.raw), annotations=union)


def SRem(a: BitVec, b: BitVec) -> BitVec:
    """ Create a signed remainder expression"""
    union = a.annotations + b.annotations
    return BitVec(z3.SRem(a.raw, b.raw), annotations=union)


def UDiv(a: BitVec, b: BitVec) -> BitVec:
    """ Create an unsigned division expression """
    union = a.annotations + b.annotations
    return BitVec(z3.UDiv(a.raw, b.raw), annotations=union)


def Sum(*args) -> BitVec:
    """ Create sum expression"""
    nraw = z3.Sum([a.raw for a in args])
    annotations = []
    for bv in args:
        annotations += bv.annotations
    return BitVec(nraw, annotations)
