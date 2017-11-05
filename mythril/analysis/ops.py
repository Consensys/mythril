from z3 import *
from enum import Enum
from laser.ethereum import helper


class VarType(Enum):
    SYMBOLIC = 1
    CONCRETE = 2


class Variable:

    def __init__(self, value, _type):
        self.value = value
        self.type = _type

    def __str__(self):
        return str(self.value)


class Op:

    def __init__(self, node, addr):
        self.node = node
        self.addr = addr


class Call(Op):

    def __init__(self, node, addr, call_type, to, value = 0, data = None):
        super().__init__(node, addr)
        self.to = to
        self.call_type = call_type
        self.call_value = value
        self.data = data

class Suicide(Op):

    def __init__(self, node, addr, call_type, to, value):
        super().__init__(node, addr)
        self.to = to

class SStore(Op):

    def __init__(self, node, addr, index, value):
        super().__init__(node, addr)
        self.index = index
        self.value = value

class SLoad(Op):

    def __init__(self, node, addr, index, value):
        super().__init__(node, addr)
        self.index = index
        self.value = value


def get_variable(i):
    try:
        return Variable(helper.get_concrete_int(i), VarType.CONCRETE)
    except AttributeError:
        return Variable(simplify(i), VarType.SYMBOLIC)



