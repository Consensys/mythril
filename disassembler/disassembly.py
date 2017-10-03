from mythril.ether import asm,evm,util
from mythril.rpc.client import EthJsonRpc
from ethereum import utils
import binascii
import sys
import os
import json


class Block:

    def __init__(self, code_index, start_addr, funcname):
        self.code_index = code_index
        self.funcname = funcname
        self.xrefs = []


    def update_length(self, num_instructions):
        self.length = num_instructions



class Disassembly:

    def __init__(self, code):
        self.instruction_list = asm.disassemble(util.safe_decode(code))
        self.blocks = []
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
                func_name = "UNK_" + func_hash

            try:
                offset = self.instruction_list[i+2]['argument']
                jump_target = int(offset, 16)

                self.func_to_addr[func_name] = jump_target
                self.addr_to_func[jump_target] = func_name
            except:
                continue

        # Parse instructions into basic blocks

        current_block = Block(0, 0, "PROLOGUE")

        index = 0
        blocklen = 0

        for instruction in self.instruction_list:

            blocklen += 1

            if (instruction['opcode'] == "JUMPDEST"):

                try:
                    func_name = self.addr_to_func[instruction['address']]
                except KeyError:
                    func_name = "JUMPDEST_UNK"
                
                current_block.update_length(blocklen)
                self.blocks.append(current_block)
                current_block = Block(index, instruction['address'], func_name)
                blocklen = 0

            index += 1



    def get_easm(self):

        easm = asm.instruction_list_to_easm(self.instruction_list[0:self.blocks[0].length])

        for block in self.blocks[1:]:
            easm += str(self.instruction_list[block.code_index]['address']) + " #### " + block.funcname + " ####\n"
            
            easm += asm.instruction_list_to_easm(self.instruction_list[block.code_index + 1:block.code_index + block.length])

        return easm