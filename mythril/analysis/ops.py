from enum import Enum


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

    def __init__(self, block_uid, addr):
        self.block_uid = block_uid
        self.addr = addr


class Call(Op):

    def __init__(self, block_uid, addr, call_type, to, value):
        super(block_uid, addr)
        self.to = to
        self.call_type = call_type
        self.call_value = value

class SStore(Op):

    def __init__(self, block_uid, addr, index, value):
        super(block_uid, addr)
        self.index = index
        self.value = value

class SLoad(Op):

    def __init__(self, block_uid, addr, index, value):
        super(block_uid, addr)
        self.index = index
        self.value = value
