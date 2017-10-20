from mythril.ether import asm,util
import os
import json


class Disassembly:

    def __init__(self, code):
        self.instruction_list = asm.disassemble(util.safe_decode(code))
        self.xrefs = []
        self.func_to_addr = {}
        self.addr_to_func = {}

        # Parse jump table & resolve function names

        script_dir = os.path.dirname(os.path.realpath(__file__))
        signature_file = os.path.join(script_dir, 'signatures.json')

        with open(signature_file) as f:
            signatures = json.load(f)

        jmptable_indices = asm.find_opcode_sequence(["PUSH4", "EQ"], self.instruction_list)

        for i in jmptable_indices:
            func_hash = self.instruction_list[i]['argument']
            try:
                func_name = signatures[func_hash]
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
