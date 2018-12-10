import re
from z3 import BitVecVal, BoolRef, If, simplify, is_false, is_true, ExprRef, BitVecNumRef
from mythril.laser.smt import symbol_factory

import logging
from typing import Union, List, Dict

import sha3 as _sha3


TT256 = 2 ** 256
TT256M1 = 2 ** 256 - 1
TT255 = 2 ** 255


def sha3(seed: str) -> bytes:
    return _sha3.keccak_256(bytes(seed)).digest()


def safe_decode(hex_encoded_string: str) -> bytes:
    if hex_encoded_string.startswith("0x"):
        return bytes.fromhex(hex_encoded_string[2:])
    else:
        return bytes.fromhex(hex_encoded_string)


def to_signed(i: int) -> int:
    return i if i < TT255 else i - TT256


def get_instruction_index(
    instruction_list: List[Dict], address: int
) -> Union[int, None]:
    index = 0
    for instr in instruction_list:
        if instr["address"] == address:
            return index
        index += 1
    return None


def get_trace_line(instr: Dict, state: "MachineState") -> str:
    stack = str(state.stack[::-1])
    # stack = re.sub("(\d+)",   lambda m: hex(int(m.group(1))), stack)
    stack = re.sub("\n", "", stack)
    return str(instr["address"]) + " " + instr["opcode"] + "\tSTACK: " + stack


def pop_bitvec(state: "MachineState") -> BitVecVal:
    # pop one element from stack, converting boolean expressions and
    # concrete Python variables to BitVecVal

    item = state.stack.pop()

    if type(item) == BoolRef:
        return If(item, symbol_factory.BitVecVal(1, 256), symbol_factory.BitVecVal(0, 256))
    elif type(item) == bool:
        if item:
            return symbol_factory.BitVecVal(1, 256)
        else:
            return symbol_factory.BitVecVal(0, 256)
    elif type(item) == int:
        return symbol_factory.BitVecVal(item, 256)
    else:
        return simplify(item)


def get_concrete_int(item: Union[int, ExprRef]) -> int:
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


def concrete_int_from_bytes(concrete_bytes: bytes, start_index: int) -> int:
    concrete_bytes = [
        byte.as_long() if type(byte) == BitVecNumRef else byte
        for byte in concrete_bytes
    ]
    integer_bytes = concrete_bytes[start_index : start_index + 32]

    return int.from_bytes(integer_bytes, byteorder="big")


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
