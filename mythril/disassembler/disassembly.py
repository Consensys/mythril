from mythril.ether import asm, util
from mythril.support.signatures import SignatureDb
import logging


class Disassembly(object):
    """
    Disassembly class

    Stores bytecode, and its disassembly.
    Additionally it will gather the following information on the existing functions in the disassembled code:
     - function hashes
     - function name to entry point mapping
     - function entry point to function name mapping
    """
    def __init__(self, code: str, enable_online_lookup: bool=False):
        self.bytecode = code
        self.instruction_list = asm.disassemble(util.safe_decode(code))

        self.func_hashes = []
        self.function_name_to_address = {}
        self.address_to_function_name = {}

        signatures = SignatureDb(
            enable_online_lookup=enable_online_lookup
        )  # control if you want to have online signature hash lookups
        try:
            signatures.open()  # open from default locations
        except FileNotFoundError:
            logging.info(
                "Missing function signature file. Resolving of function names from signature file disabled."
            )

        # Need to take from PUSH1 to PUSH4 because solc seems to remove excess 0s at the beginning for optimizing
        jump_table_indices = asm.find_opcode_sequence(
            [("PUSH1", "PUSH2", "PUSH3", "PUSH4"), ("EQ",)], self.instruction_list
        )

        for index in jump_table_indices:
            function_hash, jump_target, function_name = _get_function_info(
                index, self.instruction_list, signatures
            )
            self.func_hashes.append(function_hash)

            if jump_target is not None and function_name is not None:
                self.function_name_to_address[function_name] = jump_target
                self.address_to_function_name[jump_target] = function_name

        signatures.write()  # store resolved signatures (potentially resolved online)

    def get_easm(self):
        return asm.instruction_list_to_easm(self.instruction_list)


def _get_function_info(index: int, instruction_list: list, signature_database: SignatureDb) -> (str, int, str):
    """
    Finds the function information for a call table entry
    Solidity uses the first 4 bytes of the calldata to indicate which function the message call should execute
    The generated code that directs execution to the correct function looks like this:
    - PUSH function_hash
    - EQ
    - PUSH entry_point
    - JUMPI

    This function takes an index that points to the first instruction, and from that finds out the function hash,
    function entry and the function name.

    :param index: Start of the entry pattern
    :param instruction_list: Instruction list for the contract that is being analyzed
    :param signature_database: Database used to map function hashes to their respective function names
    :return: function hash, function entry point, function name
    """

    # Append with missing 0s at the beginning
    function_hash = "0x" + instruction_list[index]["argument"][2:].rjust(8, "0")

    function_names = signature_database.get(function_hash)
    if len(function_names) > 1:
        # In this case there was an ambiguous result
        function_name = (
            "**ambiguous** {}".format(function_names[0])
        )
    elif len(function_names) == 1:
        function_name = function_names[0]
    else:
        function_name = "_function_" + function_hash

    try:
        offset = instruction_list[index + 2]["argument"]
        entry_point = int(offset, 16)
    except IndexError:
        return function_hash, None, None

    return function_hash, entry_point, function_name
