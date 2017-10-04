from mythril.ether import asm,util
import os
import json


class Block:

    def __init__(self, id, code_index, funcname):
        self.id = id
        self.code_index = code_index
        self.funcname = funcname
        self.instruction_list = []

    def update_length(self, num_instructions):
        self.length = num_instructions
        self.start_addr = self.instruction_list[0]['address']
        self.end_addr = self.instruction_list[-1]['address']

    def get_easm(self):

        easm = str(self.instruction_list[0]['address']) + " " + self.funcname + "\n"
        easm += asm.instruction_list_to_easm(self.instruction_list[1:])

        return easm


class Disassembly:

    def __init__(self, code):
        self.instruction_list = asm.disassemble(util.safe_decode(code))
        self.blocks = []
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
        blocknumber = 1

        for instruction in self.instruction_list:

            if (instruction['opcode'] == "JUMPDEST"):

                try:
                    func_name = "- FUNCTION " + self.addr_to_func[instruction['address']] + " -"
                except KeyError:
                    func_name = "- JUMPDEST_UNK -"
                
                current_block.update_length(blocklen)
                self.blocks.append(current_block)
                current_block = Block(blocknumber, index, func_name)
                blocklen = 0
                blocknumber += 1
                
            current_block.instruction_list.append(instruction)
            blocklen += 1

            index += 1
        
        # Add the last block

        current_block.update_length(blocklen)
        self.blocks.append(current_block)

        # Resolve cross-references

        for block in self.blocks:

            jmp_indices = asm.find_opcode_sequence(["JUMP"], block.instruction_list)
            jmp_indices += asm.find_opcode_sequence(["JUMPI"], block.instruction_list)

            for i in jmp_indices:
                try:
                    dest_hex = block.instruction_list[i - 1]['argument']
                    dest = int(dest_hex[2:], 16)
                except:
                    continue

                j = 0

                try:
                    while(self.blocks[j].end_addr < dest):
                        j += 1
                except IndexError:
                    continue


                if not (block.id, self.blocks[j].id) in self.xrefs:
                    self.xrefs.append((block.id, self.blocks[j].id))

            # if the last instruction isn't an unconditional jump or halt, also add a reference to the following block

            if (block.id < len(self.blocks)) and (block.instruction_list[block.length - 1]['opcode'] not in ['JUMP', 'STOP', 'THROW', 'REVERT', 'INVALID']):
                if not (block.id, self.blocks[j].id) in self.xrefs:
                    self.xrefs.append((block.id, block.id + 1))
                

    def get_easm(self):

        easm = asm.instruction_list_to_easm(self.instruction_list[0:self.blocks[0].length])

        for block in self.blocks[1:]:
            easm += block.get_easm()

        return easm