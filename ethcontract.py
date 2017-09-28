from ether import asm, util
import re



class ETHContract:

    def __init__(self, code = "", balance = 0):

        self.easm_code = asm.disassembly_to_easm(asm.disassemble(util.safe_decode(code)))
        self.balance = balance

    def matches_expression(self, expression):

        str_eval = ""

        tokens = re.split("( and | or )", expression, re.IGNORECASE)

        for token in tokens:

            if token == " and " or token == " or ":
                str_eval += token
                continue

            m = re.match(r'^code\(([a-zA-Z0-9\s,]+)\)$', token)

            if (m):
                code = m.group(1).replace(",", "\\n")
                str_eval += "\"" + code + "\" in self.easm_code"
                continue

            m = re.match(r'^balance\s*[=><]+\s*\d+$', token)
            if (m):
                str_eval += "self." + m.group(0)
                continue

        return eval(str_eval)

