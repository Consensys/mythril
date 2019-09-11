"""This module contains various utility conversion functions and constants for
LASER."""
import re
from typing import Dict, List, Union, TYPE_CHECKING, cast

if TYPE_CHECKING:
    from mythril.laser.ethereum.state.machine_state import MachineState

from mythril.laser.smt import BitVec, Bool, Expression, If, simplify, symbol_factory

TT256 = 2 ** 256
TT256M1 = 2 ** 256 - 1
TT255 = 2 ** 255


def safe_decode(hex_encoded_string: str) -> bytes:
    """

    :param hex_encoded_string:
    :return:
    """
    if hex_encoded_string.startswith("0x"):
        return bytes.fromhex(hex_encoded_string[2:])
    else:
        return bytes.fromhex(hex_encoded_string)


def to_signed(i: int) -> int:
    """

    :param i:
    :return:
    """
    return i if i < TT255 else i - TT256


def get_instruction_index(
    instruction_list: List[Dict], address: int
) -> Union[int, None]:
    """

    :param instruction_list:
    :param address:
    :return:
    """
    index = 0
    for instr in instruction_list:
        if instr["address"] >= address:
            return index
        index += 1
    return None


def get_trace_line(instr: Dict, state: "MachineState") -> str:
    """

    :param instr:
    :param state:
    :return:
    """
    stack = str(state.stack[::-1])
    # stack = re.sub("(\d+)",   lambda m: hex(int(m.group(1))), stack)
    stack = re.sub("\n", "", stack)
    return str(instr["address"]) + " " + instr["opcode"] + "\tSTACK: " + stack


def pop_bitvec(state: "MachineState") -> BitVec:
    """

    :param state:
    :return:
    """
    # pop one element from stack, converting boolean expressions and
    # concrete Python variables to BitVecVal

    item = state.stack.pop()

    if isinstance(item, Bool):
        return If(
            cast(Bool, item),
            symbol_factory.BitVecVal(1, 256),
            symbol_factory.BitVecVal(0, 256),
        )
    elif isinstance(item, int):
        return symbol_factory.BitVecVal(item, 256)
    else:
        item = cast(BitVec, item)
        return simplify(item)


def get_concrete_int(item: Union[int, Expression]) -> int:
    """

    :param item:
    :return:
    """
    if isinstance(item, int):
        return item
    elif isinstance(item, BitVec):
        if item.symbolic:
            raise TypeError("Got a symbolic BitVecRef")
        return item.value
    elif isinstance(item, Bool):
        value = item.value
        if value is None:
            raise TypeError("Symbolic boolref encountered")
        return value

    assert False, "Unhandled type {} encountered".format(str(type(item)))


def concrete_int_from_bytes(
    concrete_bytes: Union[List[Union[BitVec, int]], bytes], start_index: int
) -> int:
    """

    :param concrete_bytes:
    :param start_index:
    :return:
    """
    concrete_bytes = [
        byte.value if isinstance(byte, BitVec) and not byte.symbolic else byte
        for byte in concrete_bytes
    ]
    integer_bytes = concrete_bytes[start_index : start_index + 32]

    # The below statement is expected to fail in some circumstances whose error is caught
    return int.from_bytes(integer_bytes, byteorder="big")  # type: ignore


def concrete_int_to_bytes(val):
    """

    :param val:
    :return:
    """
    # logging.debug("concrete_int_to_bytes " + str(val))
    if type(val) == int:
        return val.to_bytes(32, byteorder="big")
    return simplify(val).value.to_bytes(32, byteorder="big")


def bytearray_to_int(arr):
    """

    :param arr:
    :return:
    """
    o = 0
    for a in arr:
        o = (o << 8) + a
    return o


def extract_copy(
    data: bytearray, mem: bytearray, memstart: int, datastart: int, size: int
):
    for i in range(size):
        if datastart + i < len(data):
            mem[memstart + i] = data[datastart + i]
        else:
            mem[memstart + i] = 0


def extract32(data: bytearray, i: int) -> int:
    """

    :param data:
    :param i:
    :return:
    """
    if i >= len(data):
        return 0
    o = data[i : min(i + 32, len(data))]
    o.extend(bytearray(32 - len(o)))
    return bytearray_to_int(o)
