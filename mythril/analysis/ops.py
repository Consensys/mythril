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

    def __init__(self, node, addr):
        self.node = node
        self.addr = addr
        self.state = node.states[addr]


class Call(Op):

    def __init__(self, node, addr, _type, to, value = Variable(0, VarType.CONCRETE), data = None):

        super().__init__(node, addr)
        self.to = to
        self.type = _type
        self.value = value
        self.data = data

class Suicide(Op):

    def __init__(self, node, addr, call_type, to, value):
        super().__init__(node, addr)
        self.to = to

class SStore(Op):

    def __init__(self, node, addr, value):
        super().__init__(node, addr)
        self.value = value


def get_variable(i):
    try:
        return Variable(helper.get_concrete_int(i), VarType.CONCRETE)
    except AttributeError:
        return Variable(simplify(i), VarType.SYMBOLIC)



