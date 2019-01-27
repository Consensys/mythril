from mythril.laser.smt.bitvec import (
    BitVec,
    BitVecFunc,
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
from mythril.laser.smt.expression import Expression, simplify
from mythril.laser.smt.bool import Bool, is_true, is_false, Or, Not, And
from mythril.laser.smt.array import K, Array, BaseArray
from mythril.laser.smt.solver import Solver, Optimize

from typing import Union, Any, Optional, List, TypeVar, Generic
import z3


Annotations = Optional[List[Any]]
T = TypeVar("T", bound=Union[bool.Bool, z3.BoolRef])
U = TypeVar("U", bound=Union[BitVec, z3.BitVecRef])


class SymbolFactory(Generic[T, U]):
    """A symbol factory provides a default interface for all the components of mythril to create symbols"""

    @staticmethod
    def Bool(value: "__builtins__.bool", annotations: Annotations = None) -> T:
        """
        Creates a Bool with concrete value
        :param value: The boolean value
        :param annotations: The annotations to initialize the bool with
        :return: The freshly created Bool()
        """
        raise NotImplementedError

    @staticmethod
    def BitVecVal(value: int, size: int, annotations: Annotations = None) -> U:
        """Creates a new bit vector with a concrete value.

        :param value: The concrete value to set the bit vector to
        :param size: The size of the bit vector
        :param annotations: The annotations to initialize the bit vector with
        :return: The freshly created bit vector
        """
        raise NotImplementedError()

    @staticmethod
    def BitVecSym(name: str, size: int, annotations: Annotations = None) -> U:
        """Creates a new bit vector with a symbolic value.

        :param name: The name of the symbolic bit vector
        :param size: The size of the bit vector
        :param annotations: The annotations to initialize the bit vector with
        :return: The freshly created bit vector
        """
        raise NotImplementedError()

    @staticmethod
    def BitVecFuncVal(
        func_name: str,
        value: int,
        size: int,
        annotations: Annotations = None,
        input: Union[int, "BitVec"] = None,
    ) -> BitVecFunc:
        """Creates a new bit vector function with a concrete value.

        :param func_name: The name of the function
        :param value: The concrete value to set the bit vector to
        :param size: The size of the bit vector
        :param annotations: The annotations to initialize the bit vector with
        :return: The freshly created bit vector
        """
        raise NotImplementedError()

    @staticmethod
    def BitVecFuncSym(
        name: str, func_name: str, size: int, annotations: Annotations = None
    ) -> U:
        """Creates a new bit vector with a symbolic value.

        :param name: The name of the symbolic bit vector
        :param size: The size of the bit vector
        :param annotations: The annotations to initialize the bit vector with
        :return: The freshly created bit vector
        """
        raise NotImplementedError()


class _SmtSymbolFactory(SymbolFactory[bool.Bool, BitVec]):
    """
    An implementation of a SymbolFactory that creates symbols using
    the classes in: mythril.laser.smt
    """

    @staticmethod
    def Bool(value: "__builtins__.bool", annotations: Annotations = None) -> bool.Bool:
        """
        Creates a Bool with concrete value
        :param value: The boolean value
        :param annotations: The annotations to initialize the bool with
        :return: The freshly created Bool()
        """
        raw = z3.BoolVal(value)
        return Bool(raw, annotations)

    @staticmethod
    def BitVecVal(value: int, size: int, annotations: Annotations = None) -> BitVec:
        """Creates a new bit vector with a concrete value."""
        raw = z3.BitVecVal(value, size)
        return BitVec(raw, annotations)

    @staticmethod
    def BitVecSym(name: str, size: int, annotations: Annotations = None) -> BitVec:
        """Creates a new bit vector with a symbolic value."""
        raw = z3.BitVec(name, size)
        return BitVec(raw, annotations)

    @staticmethod
    def BitVecFuncVal(
        func_name: str,
        value: int,
        size: int,
        annotations: Annotations = None,
        input: Union[int, "BitVec"] = None,
    ) -> BitVecFunc:
        """Creates a new bit vector function with a concrete value."""
        raw = z3.BitVecVal(value, size)
        return BitVecFunc(raw, func_name, input, annotations)

    @staticmethod
    def BitVecFuncSym(
        name: str,
        func_name: str,
        size: int,
        annotations: Annotations = None,
        input: Union[int, "BitVec"] = None,
    ) -> BitVecFunc:
        """Creates a new bit vector function with a symbolic value."""
        raw = z3.BitVec(name, size)
        return BitVecFunc(raw, func_name, input, annotations)


class _Z3SymbolFactory(SymbolFactory[z3.BoolRef, z3.BitVecRef]):
    """
    An implementation of a SymbolFactory that directly returns
    z3 symbols
    """

    @staticmethod
    def Bool(value: "__builtins__.bool", annotations: Annotations = None) -> z3.BoolRef:
        """ Creates a new bit vector with a concrete value """
        return z3.BoolVal(value)

    @staticmethod
    def BitVecVal(
        value: int, size: int, annotations: Annotations = None
    ) -> z3.BitVecRef:
        """Creates a new bit vector with a concrete value."""
        return z3.BitVecVal(value, size)

    @staticmethod
    def BitVecSym(
        name: str, size: int, annotations: Annotations = None
    ) -> z3.BitVecRef:
        """Creates a new bit vector with a symbolic value."""
        return z3.BitVec(name, size)


# This is the instance that other parts of mythril should use

# Type hints are not allowed here in 3.5
# symbol_factory: SymbolFactory = _SmtSymbolFactory()
symbol_factory = _SmtSymbolFactory()
