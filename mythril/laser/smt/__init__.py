from mythril.laser.smt.bitvec import (
    BitVec,
    If,
    UGT,
    ULT,
    Concat,
    Extract,
    URem,
    SRem,
    UDiv,
)
from mythril.laser.smt.expression import Expression, simplify
from mythril.laser.smt.bool import Bool, is_true, is_false

import z3


class SymbolFactory:
    """
    A symbol factory provides a default interface for all the components of mythril to create symbols
    """

    @staticmethod
    def BitVecVal(value: int, size: int, annotations=None):
        """
        Creates a new bit vector with a concrete value
        :param value: The concrete value to set the bit vector to
        :param size: The size of the bit vector
        :param annotations: The annotations to initialize the bit vector with
        :return: The freshly created bit vector
        """
        raise NotImplementedError()

    @staticmethod
    def BitVecSym(name: str, size: int, annotations=None):
        """
        Creates a new bit vector with a symbolic value
        :param name: The name of the symbolic bit vector
        :param size: The size of the bit vector
        :param annotations: The annotations to initialize the bit vector with
        :return: The freshly created bit vector
        """
        raise NotImplementedError()


class _SmtSymbolFactory(SymbolFactory):
    """
    An implementation of a SymbolFactory that creates symbols using
    the classes in: mythril.laser.smt
    """

    @staticmethod
    def BitVecVal(value: int, size: int, annotations=None):
        """ Creates a new bit vector with a concrete value """
        raw = z3.BitVecVal(value, size)
        return BitVec(raw, annotations)

    @staticmethod
    def BitVecSym(name: str, size: int, annotations=None):
        """ Creates a new bit vector with a symbolic value """
        raw = z3.BitVec(name, size)
        return BitVec(raw, annotations)


class _Z3SymbolFactory(SymbolFactory):
    """
    An implementation of a SymbolFactory that directly returns
    z3 symbols
    """

    @staticmethod
    def BitVecVal(value: int, size: int, annotations=None):
        """ Creates a new bit vector with a concrete value """
        return z3.BitVecVal(value, size)

    @staticmethod
    def BitVecSym(name: str, size: int, annotations=None):
        """ Creates a new bit vector with a symbolic value """
        return z3.BitVec(name, size)


# This is the instance that other parts of mythril should use
symbol_factory: SymbolFactory = _Z3SymbolFactory()
