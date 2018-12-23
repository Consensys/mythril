import z3

from mythril.laser.smt.array import K, Array, BaseArray
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
    UGE,
    Sum,
    BVAddNoOverflow,
    BVMulNoOverflow,
    BVSubNoUnderflow,
)
from mythril.laser.smt.bool import Bool, is_true, is_false, Or, Not
from mythril.laser.smt.expression import Expression, simplify
from mythril.laser.smt.solver import Solver, Optimize


class SymbolFactory:
    """A symbol factory provides a default interface for all the components of
    mythril to create symbols."""

    @staticmethod
    def Bool(value: bool, annotations=None):
        """Creates a Bool with concrete value.

        :param value: The boolean value
        :param annotations: The annotations to initialize the bool with
        :return: The freshly created Bool()
        """
        raise NotImplementedError

    @staticmethod
    def BitVecVal(value: int, size: int, annotations=None):
        """Creates a new bit vector with a concrete value.

        :param value: The concrete value to set the bit vector to
        :param size: The size of the bit vector
        :param annotations: The annotations to initialize the bit vector with
        :return: The freshly created bit vector
        """
        raise NotImplementedError()

    @staticmethod
    def BitVecSym(name: str, size: int, annotations=None):
        """Creates a new bit vector with a symbolic value.

        :param name: The name of the symbolic bit vector
        :param size: The size of the bit vector
        :param annotations: The annotations to initialize the bit vector with
        :return: The freshly created bit vector
        """
        raise NotImplementedError()


class _SmtSymbolFactory(SymbolFactory):
    """An implementation of a SymbolFactory that creates symbols using the
    classes in: mythril.laser.smt."""

    @staticmethod
    def Bool(value: bool, annotations=None):
        """Creates a Bool with concrete value.

        :param value: The boolean value
        :param annotations: The annotations to initialize the bool with
        :return: The freshly created Bool()
        """
        raw = z3.Bool(value)
        return Bool(raw, annotations)

    @staticmethod
    def BitVecVal(value: int, size: int, annotations=None):
        """Creates a new bit vector with a concrete value."""
        raw = z3.BitVecVal(value, size)
        return BitVec(raw, annotations)

    @staticmethod
    def BitVecSym(name: str, size: int, annotations=None):
        """Creates a new bit vector with a symbolic value."""
        raw = z3.BitVec(name, size)
        return BitVec(raw, annotations)


class _Z3SymbolFactory(SymbolFactory):
    """An implementation of a SymbolFactory that directly returns z3
    symbols."""

    @staticmethod
    def Bool(value: bool, annotations=None):
        """Creates a new bit vector with a concrete value."""
        return z3.Bool(value)

    @staticmethod
    def BitVecVal(value: int, size: int, annotations=None):
        """Creates a new bit vector with a concrete value."""
        return z3.BitVecVal(value, size)

    @staticmethod
    def BitVecSym(name: str, size: int, annotations=None):
        """Creates a new bit vector with a symbolic value."""
        return z3.BitVec(name, size)


# This is the instance that other parts of mythril should use

# Type hints are not allowed here in 3.5
# symbol_factory: SymbolFactory = _SmtSymbolFactory()
symbol_factory = _SmtSymbolFactory()
