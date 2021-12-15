"""This module contains various helper classes and functions to deal with EVM
code disassembly."""

import re
from collections.abc import Generator
from functools import lru_cache

from mythril.ethereum import util
from mythril.support.opcodes import OPCODES, ADDRESS, ADDRESS_OPCODE_MAPPING

regex_PUSH = re.compile(r"^PUSH(\d*)$")


class EvmInstruction:
    """Model to hold the information of the disassembly."""

    def __init__(self, address, op_code, argument=None):
        self.address = address
        self.op_code = op_code
        self.argument = argument

    def to_dict(self) -> dict:
        """

        :return:
        """
        result = {"address": self.address, "opcode": self.op_code}
        if self.argument:
            result["argument"] = self.argument
        return result


def instruction_list_to_easm(instruction_list: list) -> str:
    """Convert a list of instructions into an easm op code string.

    :param instruction_list:
    :return:
    """
    result = ""

    for instruction in instruction_list:
        result += "{} {}".format(instruction["address"], instruction["opcode"])
        if "argument" in instruction:
            result += " " + instruction["argument"]
        result += "\n"

    return result


def get_opcode_from_name(operation_name: str) -> int:
    """Get an op code based on its name.

    :param operation_name:
    :return:
    """
    if operation_name in OPCODES:
        return OPCODES[operation_name][ADDRESS]
    raise RuntimeError("Unknown opcode")


def find_op_code_sequence(pattern: list, instruction_list: list) -> Generator:
    """Returns all indices in instruction_list that point to instruction
    sequences following a pattern.

    :param pattern: The pattern to look for, e.g. [["PUSH1", "PUSH2"], ["EQ"]] where ["PUSH1", "EQ"] satisfies pattern
    :param instruction_list: List of instructions to look in
    :return: Indices to the instruction sequences
    """
    for i in range(0, len(instruction_list) - len(pattern) + 1):
        if is_sequence_match(pattern, instruction_list, i):
            yield i


def is_sequence_match(pattern: list, instruction_list: list, index: int) -> bool:
    """Checks if the instructions starting at index follow a pattern.

    :param pattern: List of lists describing a pattern, e.g. [["PUSH1", "PUSH2"], ["EQ"]] where ["PUSH1", "EQ"] satisfies pattern
    :param instruction_list: List of instructions
    :param index: Index to check for
    :return: Pattern matched
    """
    for index, pattern_slot in enumerate(pattern, start=index):
        try:
            if not instruction_list[index]["opcode"] in pattern_slot:
                return False
        except IndexError:
            return False
    return True


lru_cache(maxsize=2 ** 10)


def disassemble(bytecode) -> list:
    """Disassembles evm bytecode and returns a list of instructions.

    :param bytecode:
    :return:
    """
    instruction_list = []
    address = 0
    length = len(bytecode)

    if type(bytecode) == str:
        bytecode = util.safe_decode(bytecode)
        length = len(bytecode)
        part_code = bytecode[-43:]
    else:
        try:
            part_code = bytes(bytecode[-43:])
        except TypeError:
            part_code = ""
    try:
        if "bzzr" in str(part_code):
            # ignore swarm hash
            length -= 43
    except ValueError:
        pass

    while address < length:
        try:
            op_code = ADDRESS_OPCODE_MAPPING[bytecode[address]]
        except KeyError:
            instruction_list.append(EvmInstruction(address, "INVALID"))
            address += 1
            continue

        current_instruction = EvmInstruction(address, op_code)

        match = re.search(regex_PUSH, op_code)
        if match:
            argument_bytes = bytecode[address + 1 : address + 1 + int(match.group(1))]
            if type(argument_bytes) == bytes:
                current_instruction.argument = "0x" + argument_bytes.hex()
            else:
                current_instruction.argument = argument_bytes
            address += int(match.group(1))

        instruction_list.append(current_instruction)
        address += 1

    # We use a to_dict() here for compatibility reasons
    return [element.to_dict() for element in instruction_list]
