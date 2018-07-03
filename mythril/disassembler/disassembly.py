from mythril.ether import asm,util
from mythril.support.signatures import Signatures
import logging


class Disassembly:

    def __init__(self, code):
        self.instruction_list = asm.disassemble(util.safe_decode(code))
        self.xrefs = []
        self.func_to_addr = {}
        self.addr_to_func = {}
        self.bytecode = code

        signatures = Signatures(enable_online_lookkup=True)  # control if you want to have online sighash lookups
        try:
            signatures.open()  # open from default locations
        except FileNotFoundError:
            logging.info("Missing function signature file. Resolving of function names from disabled.")

        # Parse jump table & resolve function names

        jmptable_indices = asm.find_opcode_sequence(["PUSH4", "EQ"], self.instruction_list)

        for i in jmptable_indices:
            func_hash = self.instruction_list[i]['argument']
            try:
                func_name = signatures.get(func_hash)  # tries local cache, file and optional online lookup
            except KeyError:
                func_name = "_function_" + func_hash

            try:
                offset = self.instruction_list[i+2]['argument']
                jump_target = int(offset, 16)

                self.func_to_addr[func_name] = jump_target
                self.addr_to_func[jump_target] = func_name
            except:
                continue

    def get_easm(self):
        return asm.instruction_list_to_easm(self.instruction_list)
