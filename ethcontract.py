from ether import asm, util
import re
import persistent


class ETHCode(persistent.Persistent):

    def __init__(self, code = ""):

        self.code = code


    def matches_expression(self, expression):

        disassembly = asm.disassemble(util.safe_decode(self.code))

        easm_code = asm.disassembly_to_easm(disassembly)

        str_eval = ""

        tokens = re.split("( and | or )", expression, re.IGNORECASE)

        for token in tokens:

            if token == " and " or token == " or ":
                str_eval += token
                continue

            m = re.match(r'^code\[([a-zA-Z0-9\s,]+)\]$', token)

            if (m):
                code = m.group(1).replace(",", "\\n")
                str_eval += "\"" + code + "\" in easm_code"
                continue

            m = re.match(r'^func\[([a-zA-Z0-9\s,()]+)\]$', token)

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
