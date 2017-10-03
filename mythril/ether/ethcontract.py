from mythril.ether import asm, util
import re
import persistent
from ethereum import utils


class ETHContract(persistent.Persistent):

    def __init__(self, code = ""):

        self.code = code


    def get_xrefs(self):

        instruction_list = asm.disassemble(util.safe_decode(self.code))

        xrefs = []

        for instruction in instruction_list:
            if instruction['opcode'] == "PUSH20":
                if instruction['argument']:
                    addr = instruction['argument']

                    if (re.match(r'^0x[a-zA-Z0-9]{40}$', addr) and addr != "0xffffffffffffffffffffffffffffffffffffffff"):
                        if addr not in xrefs:
                            xrefs.append(addr)

        return xrefs


    def get_instruction_list(self):

        return asm.disassemble(util.safe_decode(self.code))


    def get_easm(self):

        return asm.instruction_list_to_easm(asm.disassemble(util.safe_decode(self.code)))


    def matches_expression(self, expression):

        easm_code = self.get_easm()
        str_eval = ''

        matches = re.findall(r'func#([a-zA-Z0-9\s_,(\\)\[\]]+)#', expression)

        for m in matches:
            # Calculate function signature hashes

            sign_hash = utils.sha3(m)[:4].hex()

            expression = expression.replace(m, sign_hash)

        tokens = re.split("( and | or )", expression, re.IGNORECASE)

        for token in tokens:

            if token == " and " or token == " or ":
                str_eval += token
                continue

            m = re.match(r'^code#([a-zA-Z0-9\s,\[\]]+)#', token)

            if (m):
                code = m.group(1).replace(",", "\\n")
                str_eval += "\"" + code + "\" in easm_code"
                continue

            m = re.match(r'^func#([a-fA-F0-9]+)#$', token)

            if (m):
                str_eval += "\"" + m.group(1) + "\" in easm_code" 

                continue

        return eval(str_eval)


class InstanceList(persistent.Persistent):

    def __init__(self):
        self.addresses = []
        self.balances = []
        pass

    def add(self, address, balance = 0):
        self.addresses.append(address)
        self.balances.append(balance)
        self._p_changed = True
