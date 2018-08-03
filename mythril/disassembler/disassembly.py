from mythril.ether import asm, util
from mythril.support.signatures import SignatureDb
import logging


class Disassembly(object):

    def __init__(self, code, decode=True):
        if decode:
            self.instruction_list = asm.disassemble(util.safe_decode(code))
        else:
            self.instruction_list = asm.disassemble(code)
        self.func_hashes = []
        self.func_to_addr = {}
        self.addr_to_func = {}
        self.bytecode = code

        signatures = SignatureDb(enable_online_lookup=True)  # control if you want to have online sighash lookups
        try:
            signatures.open()  # open from default locations
        except FileNotFoundError:
            logging.info("Missing function signature file. Resolving of function names from signature file disabled.")

        # Parse jump table & resolve function names

        jmptable_indices = asm.find_opcode_sequence(["PUSH4", "EQ"], self.instruction_list)

        for i in jmptable_indices:
            func_hash = self.instruction_list[i]['argument']
            self.func_hashes.append(func_hash)
            try:
                # tries local cache, file and optional online lookup
                # may return more than one function signature. since we cannot probe for the correct one we'll use the first
                func_names = signatures.get(func_hash)
                if len(func_names) > 1:
                    # ambigious result
                    func_name = "**ambiguous** %s" % func_names[0]  # return first hit but note that result was ambiguous
                else:
                    # only one item
                    func_name = func_names[0]
            except KeyError:
                func_name = "_function_" + func_hash

            try:
                offset = self.instruction_list[i + 2]['argument']
                jump_target = int(offset, 16)

                self.func_to_addr[func_name] = jump_target
                self.addr_to_func[jump_target] = func_name
            except:
                continue

        signatures.write()  # store resolved signatures (potentially resolved online)

    def get_easm(self):
        # todo: tintinweb - print funcsig resolved data from self.addr_to_func?
        return asm.instruction_list_to_easm(self.instruction_list)
