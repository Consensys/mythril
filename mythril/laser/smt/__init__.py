from mythril.laser.smt.bitvec import BitVec
from mythril.laser.smt.expression import Expression
from mythril.laser.smt.bool import Bool

import z3


class SymbolFactory:
    @staticmethod
    def BitVecVal(value: int, size: int, annotations=None):
        raise NotImplementedError()

    @staticmethod
    def BitVecSym(name: str, size: int, annotations=None):
        raise NotImplementedError()


class SmtSymbolFactory(SymbolFactory):

    @staticmethod
    def BitVecVal(value: int, size: int, annotations=None):
        raw = z3.BitVecVal(value, size)
        return BitVec(raw, annotations)

    @staticmethod
    def BitVecSym(name: str, size: int, annotations=None):
        raw = z3.BitVec(name, size)
        return BitVec(raw, annotations)


class Z3SymbolFactory(SymbolFactory):
    @staticmethod
    def BitVecVal(value: int, size: int, annotations=None):
        return z3.BitVecVal(value, size)

    @staticmethod
    def BitVecSym(name: str, size: int, annotations=None):
        return z3.BitVec(name, size)


symbol_factory = Z3SymbolFactory()

