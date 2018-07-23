from z3 import *
from enum import Enum
from mythril.laser.ethereum import util


class VarType(Enum):
    SYMBOLIC = 1
    CONCRETE = 2


class Variable:

    def __init__(self, val, _type):
        self.val = val
        self.type = _type

    def __str__(self):
        return str(self.val)


def get_variable(i):
    try:
        return Variable(util.get_concrete_int(i), VarType.CONCRETE)
    except AttributeError:
        return Variable(simplify(i), VarType.SYMBOLIC)


class Op:

    def __init__(self, node, state, state_index):
        self.node = node
        self.state = state
        self.state_index = state_index


class Call(Op):

    def __init__(self, node, state, state_index, _type, to, gas, value=Variable(0, VarType.CONCRETE), data=None):

        super().__init__(node, state, state_index)
        self.to = to
        self.gas = gas
        self.type = _type
        self.value = value
        self.data = data


class SStore(Op):

    def __init__(self, node, state, state_index, value):
        super().__init__(node, state, state_index)
        self.value = value
