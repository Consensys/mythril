import re
from z3 import *
import logging

import sha3 as _sha3


TT256 = 2 ** 256
TT256M1 = 2 ** 256 - 1
TT255 = 2 ** 255


def sha3(seed):
    return _sha3.keccak_256(bytes(seed)).digest()


def safe_decode(hex_encoded_string):

    if hex_encoded_string.startswith("0x"):
        return bytes.fromhex(hex_encoded_string[2:])
    else:
        return bytes.fromhex(hex_encoded_string)


def to_signed(i):
    return i if i < TT255 else i - TT256


def get_instruction_index(instruction_list, address):

    index = 0

    for instr in instruction_list:
        if instr["address"] == address:
            return index

        index += 1

    return None


def get_trace_line(instr, state):

    stack = str(state.stack[::-1])

    # stack = re.sub("(\d+)",   lambda m: hex(int(m.group(1))), stack)
    stack = re.sub("\n", "", stack)

    return str(instr["address"]) + " " + instr["opcode"] + "\tSTACK: " + stack


def pop_bitvec(state):
    # pop one element from stack, converting boolean expressions and
    # concrete Python variables to BitVecVal

    item = state.stack.pop()

    if type(item) == BoolRef:
        return If(item, BitVecVal(1, 256), BitVecVal(0, 256))
    elif type(item) == bool:
        if item:
            return BitVecVal(1, 256)
        else:
            return BitVecVal(0, 256)
    elif type(item) == int:
        return BitVecVal(item, 256)
    else:
        return simplify(item)


def get_concrete_int(item):
    if isinstance(item, int):
        return item
    elif isinstance(item, BitVecNumRef):
        return item.as_long()
    elif isinstance(item, BoolRef):
        simplified = simplify(item)
        if is_false(simplified):
            return 0
        elif is_true(simplified):
            return 1
        else:
            raise TypeError("Symbolic boolref encountered")

    try:
        return simplify(item).as_long()
    except AttributeError:
        raise TypeError("Got a symbolic BitVecRef")


def concrete_int_from_bytes(_bytes, start_index):
    _bytes = [
        _byte.as_long() if type(_byte) == BitVecNumRef else _byte for _byte in _bytes
    ]
    b = _bytes[start_index : start_index + 32]
    val = int.from_bytes(b, byteorder="big")

    return val


def concrete_int_to_bytes(val):

    # logging.debug("concrete_int_to_bytes " + str(val))
    if type(val) == int:
        return val.to_bytes(32, byteorder="big")

    return (simplify(val).as_long()).to_bytes(32, byteorder="big")


def bytearray_to_int(arr):
    o = 0
    for a in arr:
        o = (o << 8) + a
    return o
