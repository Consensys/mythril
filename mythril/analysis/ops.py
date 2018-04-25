import attr

from z3 import *
from enum import Enum
from laser.ethereum import helper


class VarType(Enum):
    SYMBOLIC = 1
    CONCRETE = 2


def get_variable(i):
    try:
        return Variable(helper.get_concrete_int(i), VarType.CONCRETE)
    except AttributeError:
        return Variable(simplify(i), VarType.SYMBOLIC)


@attr.s
class Variable:
    val = attr.ib()
    type = attr.ib()


@attr.s
class Op:
    node = attr.ib()
    state = attr.ib()
    state_index= attr.ib()


@attr.s
class Call(Op):
    to = attr.ib()
    gas = attr.ib()
    type = attr.ib()
    value = attr.ib(default=Variable(0, VarType.CONCRETE))
    data = attr.ib(default=None)


@attr.s
class SStore(Op):
    value = attr.ib()
