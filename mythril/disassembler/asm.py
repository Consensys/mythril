import sys
import re
from typing import Pattern, Match

from ethereum.opcodes import opcodes
from mythril.ether import util


regex_PUSH = re.compile("^PUSH(\d*)$")

# Additional mnemonic to catch failed assertions
opcodes[254] = ["ASSERT_FAIL", 0, 0, 0]


def instruction_list_to_easm(instruction_list):
    result = ""

    for instruction in instruction_list:
        result += "{} {}".format(instruction["address"], instruction["opcode"])
        if "argument" in instruction:
            result += " " + instruction["argument"]
        result += "\n"

    return result


def get_opcode_from_name(operation_name):
    for op_code, value in opcodes.items():
        if operation_name == value[0]:
            return op_code
    raise RuntimeError("Unknown opcode")


def find_opcode_sequence(pattern, instruction_list):
    """
    Returns all indices in instruction_list that point to instruction sequences following a pattern
    :param pattern: The pattern to look for.
        Example:  [["PUSH1", "PUSH2"], ["EQ"]] where ["PUSH1", "EQ"] satisfies the pattern
    :param instruction_list: List of instructions to look in
    :return: Indices to the instruction sequences
    """
    for i in range(0, len(instruction_list) - len(pattern) + 1):
        if is_sequence_match(pattern, instruction_list, i):
            yield i


def is_sequence_match(pattern, instruction_list, index):
    """
    Checks if the instructions starting at index follow a pattern
    :param pattern: List of lists describing a pattern.
        Example:  [["PUSH1", "PUSH2"], ["EQ"]] where ["PUSH1", "EQ"] satisfies the pattern
    :param instruction_list: List of instructions
    :param index: Index to check for
    :return: Pattern matched
    """
    for index, pattern_slot in enumerate(pattern, start=index):
        if not instruction_list[index] in pattern_slot:
            return False
    return True


def disassemble(bytecode):

    instruction_list = []
    addr = 0

    length = len(bytecode)

    if "bzzr" in str(bytecode[-43:]):
        # ignore swarm hash
        length -= 43

    while addr < length:

        instruction = {"address": addr}

        try:
            if sys.version_info > (3, 0):
                opcode = opcodes[bytecode[addr]]
            else:
                opcode = opcodes[ord(bytecode[addr])]

        except KeyError:

            # invalid opcode
            instruction_list.append({"address": addr, "opcode": "INVALID"})
            addr += 1
            continue

        instruction["opcode"] = opcode[0]

        m = re.search(regex_PUSH, opcode[0])

        if m:
            argument = bytecode[addr + 1 : addr + 1 + int(m.group(1))]
            instruction["argument"] = "0x" + argument.hex()

            addr += int(m.group(1))

        instruction_list.append(instruction)

        addr += 1

    return instruction_list


def assemble(instruction_list):

    bytecode = b""

    for instruction in instruction_list:

        try:
            opcode = get_opcode_from_name(instruction["opcode"])
        except RuntimeError:
            opcode = 0xBB

        bytecode += opcode.to_bytes(1, byteorder="big")

        if "argument" in instruction:

            bytecode += util.safe_decode(instruction["argument"])

    return bytecode
