import re
from collections import Generator

from ethereum.opcodes import opcodes

regex_PUSH = re.compile("^PUSH(\d*)$")

# Additional mnemonic to catch failed assertions
opcodes[254] = ["ASSERT_FAIL", 0, 0, 0]


class EvmInstruction:
    """ Model to hold the information of the disassembly """
    def __init__(self, address, op_code, argument=None):
        self.address = address
        self.op_code = op_code
        self.argument = argument

    def to_dict(self) -> dict:
        result = {"address": self.address, "opcode": self.op_code}
        if self.argument:
            result["argument"] = self.argument
        return result


def instruction_list_to_easm(instruction_list: dict) -> str:
    result = ""

    for instruction in instruction_list:
        result += "{} {}".format(instruction["address"], instruction["opcode"])
        if "argument" in instruction:
            result += " " + instruction["argument"]
        result += "\n"

    return result


def get_opcode_from_name(operation_name: str) -> int:
    for op_code, value in opcodes.items():
        if operation_name == value[0]:
            return op_code
    raise RuntimeError("Unknown opcode")


def find_op_code_sequence(pattern: list, instruction_list: list) -> Generator:
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


def is_sequence_match(pattern: list, instruction_list: list, index: int) -> bool:
    """
    Checks if the instructions starting at index follow a pattern
    :param pattern: List of lists describing a pattern.
        Example:  [["PUSH1", "PUSH2"], ["EQ"]] where ["PUSH1", "EQ"] satisfies the pattern
    :param instruction_list: List of instructions
    :param index: Index to check for
    :return: Pattern matched
    """
    for index, pattern_slot in enumerate(pattern, start=index):
        try:
            if not instruction_list[index]['opcode'] in pattern_slot:
                return False
        except IndexError:
            return False
    return True


def disassemble(bytecode: str) -> list:
    """Disassembles evm bytecode and returns a list of instructions"""
    instruction_list = []
    address = 0
    length = len(bytecode)
    if "bzzr" in str(bytecode[-43:]):
        # ignore swarm hash
        length -= 43

    while address < length:
        try:
            op_code = opcodes[bytecode[address]]
        except KeyError:
            instruction_list.append(EvmInstruction(address, "INVALID"))
            address += 1
            continue

        op_code_name = op_code[0]
        current_instruction = EvmInstruction(address, op_code_name)

        match = re.search(regex_PUSH, op_code_name)
        if match:
            argument_bytes = bytecode[address + 1: address + 1 + int(match.group(1))]
            current_instruction.argument = "0x" + argument_bytes.hex()
            address += int(match.group(1))

        instruction_list.append(current_instruction)
        address += 1

    # We use a to_dict() here for compatibility reasons
    return list(map(lambda element: element.to_dict(), instruction_list))
