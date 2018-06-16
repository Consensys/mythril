import re
from z3 import *
import logging

import sha3 as _sha3
import struct

TT256 = 2 ** 256
TT256M1 = 2 ** 256 - 1
TT255 = 2 ** 255


ALL_BYTES = tuple(
            struct.pack('B', i)
            for i in range(256)
            )



def zpad(x, l):
    """ Left zero pad value `x` at least to length `l`.
    >>> zpad('\xca\xfe', 4)
    '\x00\x00\xca\xfe'
    """
    return b'\x00' * max(0, l - len(x)) + x


def sha3(seed):
    return _sha3.keccak_256(bytes(seed)).digest()


def safe_decode(hex_encoded_string):

    if (hex_encoded_string.startswith("0x")):
        return bytes.fromhex(hex_encoded_string[2:])
    else:
        return bytes.fromhex(hex_encoded_string)


def to_signed(i):
    return i if i < TT255 else i - TT256


def get_instruction_index(instruction_list, address):

    index = 0

    for instr in instruction_list:
        if instr['address'] == address:
            return index

        index += 1

    return None


def get_trace_line(instr, state):

    stack = str(state.stack[::-1])

    # stack = re.sub("(\d+)",   lambda m: hex(int(m.group(1))), stack)
    stack = re.sub("\n", "", stack)

    return str(instr['address']) + " " + instr['opcode'] + "\tSTACK: " + stack


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

    if (type(item) == int):
        return item

    if (type(item) == BitVecNumRef):
        return item.as_long()

    return simplify(item).as_long()


def concrete_int_from_bytes(_bytes, start_index):

    # logging.debug("-- concrete_int_from_bytes: " + str(_bytes[start_index:start_index+32]))
    b = _bytes[start_index:start_index+32]

    val = int.from_bytes(b, byteorder='big')

    return val


def concrete_int_to_bytes(val):

    # logging.debug("concrete_int_to_bytes " + str(val))

    if (type(val) == int):
        return val.to_bytes(32, byteorder='big')

    return (simplify(val).as_long()).to_bytes(32, byteorder='big')


def bytearray_to_int(arr):
    o = 0
    for a in arr:
        o = (o << 8) + a
    return o

