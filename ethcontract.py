from ether import asm, util
import re
import persistent



class ETHCode(persistent.Persistent):

    def __init__(self, code = ""):

        self.disassembly = asm.disassemble(util.safe_decode(code))

    def matches_expression(self, expression):

        str_eval = ""

        tokens = re.split("( and | or )", expression, re.IGNORECASE)

        for token in tokens:

            if token == " and " or token == " or ":
                str_eval += token
                continue

            m = re.match(r'^code\[([a-zA-Z0-9\s,]+)\]$', token)

            if (m):
                code = m.group(1).replace(",", "\\n")
                str_eval += "\"" + code + "\" in self.easm_code"
                continue

            m = re.match(r'^balance\s*[=><]+\s*\d+$', token)

            if (m):
                str_eval += "self." + m.group(0)
                continue

            m = re.match(r'^func\[([a-zA-Z0-9\s,()]+)\]$', token)

            if (m):
                str_eval += "\"" + m.group(1) + "\" in self.easm_code"               

                continue

        return eval(str_eval)


class CodeHashByAddress(persistent.Persistent):

    def __init__(self, code_hash, balance = 0):
        self.code_hash = code_hash
        self.balance = balance

class AddressesByCodeHash(persistent.Persistent):

    def __init__(self, address, balance = 0):
        self.addresses = [address]
        self.balances = [balance]

    def add(self, address, balance = 0):
        self.addresses.append(address)
        self.balances.append(balance)
        self._p_changed = True
