import z3

from mythril.laser.smt.expression import Expression


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


def UREM(a: BitVec, b: BitVec) -> BitVec:
    union = a.annotations + b.annotations
    return BitVec(z3.URem(a.raw, b.raw), annotations=union)


def SREM(a: BitVec, b: BitVec) -> BitVec:
    union = a.annotations + b.annotations
    return BitVec(z3.SRem(a.raw, b.raw), annotations=union)


def UDIV(a: BitVec, b: BitVec) -> BitVec:
    union = a.annotations + b.annotations
    return BitVec(z3.UDIV(a.raw, b.raw), annotations=union)


def BitVecVal(value, size, annotations=None):
    raw = z3.BitVecVal(value, size)
    return BitVec(raw, annotations)


def BitVecSym(name, size, annotations=None):
    raw = z3.BitVec(name, size)
    return BitVec(raw, annotations)


class OverflowAnnotation:
    def __init__(self, location):
        self.location = location

    @staticmethod
    def it_overflows(expression, location):
        a = OverflowAnnotation(location)
        expression.annotate(a)

    @staticmethod
    def does_overflow(expression):
        locs = []
        for annotation in expression.annotations:
            if isinstance(annotation, OverflowAnnotation):
                locs.append(annotation.location)
        return len(locs) > 0


x = BitVecSym("x", 256)

OverflowAnnotation.it_overflows(x, 10)

y = x + BitVecVal(2, 256)

print(OverflowAnnotation.does_overflow(y))
