"""This module contains various helper methods for dealing with EVM operations."""
from mythril.laser.smt import simplify
from enum import Enum
from mythril.laser.ethereum import util


class VarType(Enum):
    """An enum denoting whether a value is symbolic or concrete."""

    SYMBOLIC = 1
    CONCRETE = 2


class Variable:
    """The representation of a variable with value and type."""

    def __init__(self, val, _type):
        """

        :param val:
        :param _type:
        """
        self.val = val
        self.type = _type

    def __str__(self):
        """

        :return:
        """
        return str(self.val)


def get_variable(i):
    """

    :param i:
    :return:
    """
    try:
        return Variable(util.get_concrete_int(i), VarType.CONCRETE)
    except TypeError:
        return Variable(simplify(i), VarType.SYMBOLIC)


class Op:
    """The base type for operations referencing current node and state."""

    def __init__(self, node, state, state_index):
        """

        :param node:
        :param state:
        :param state_index:
        """
        self.node = node
        self.state = state
        self.state_index = state_index


class Call(Op):
    """The representation of a CALL operation."""

    def __init__(
        self,
        node,
        state,
        state_index,
        _type,
        to,
        gas,
        value=Variable(0, VarType.CONCRETE),
        data=None,
    ):
        """

        :param node:
        :param state:
        :param state_index:
        :param _type:
        :param to:
        :param gas:
        :param value:
        :param data:
        """
        super().__init__(node, state, state_index)
        self.to = to
        self.gas = gas
        self.type = _type
        self.value = value
        self.data = data


class SStore(Op):
    """The respresentation of an SSTORE operation."""

    def __init__(self, node, state, state_index, value):
        super().__init__(node, state, state_index)
        self.value = value
