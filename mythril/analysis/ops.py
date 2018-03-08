from z3 import *
from enum import Enum
from laser.ethereum import helper


class VarType(Enum):
    SYMBOLIC = 1
    CONCRETE = 2


class Variable:

    def __init__(self, val, _type):
        self.val = val
        self.type = _type

    def __str__(self):
        return str(self.val)


class Op:

    def __init__(self, node, state, addr):
        self.node = node
        self.state = state
        self.addr = addr


class Call(Op):

    def __init__(self, node, state, addr, _type, to, gas, value=Variable(0, VarType.CONCRETE), data=None):

        super().__init__(node, state, addr)
        self.to = to
        self.gas = gas
        self.type = _type
        self.value = value
        self.data = data


class SStore(Op):

    def __init__(self, node, state, addr, value):
        super().__init__(node, state, addr)
        self.value = value


def get_variable(i):
    try:
        return Variable(helper.get_concrete_int(i), VarType.CONCRETE)
    except AttributeError:
        return Variable(simplify(i), VarType.SYMBOLIC)
