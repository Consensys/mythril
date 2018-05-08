from mythril.disassembler.disassembly import Disassembly
from ethereum import utils
import persistent
import re


class ETHContract(persistent.Persistent):

    def __init__(self, code, creation_code="", name="Unknown"):

        self.creation_code = creation_code
        self.name = name

        # Workaround: We currently do not support compile-time linking.
        # Dynamic contract addresses of the format __[contract-name]_____________ are replaced with a generic address

        code = re.sub(r'(_+.*_+)', 'aa' * 20, code)

        self.code = code
        self.disassembly = Disassembly(self.code)

    def as_dict(self):

        return {
            'address': self.address,
            'name': self.name,
            'code': self.code,
            'creation_code': self.creation_code,
            'disassembly': self.disassembly
        }

    def get_easm(self):

        return Disassembly(self.code).get_easm()

    def matches_expression(self, expression):

        easm_code = self.get_easm()
        str_eval = ''

        matches = re.findall(r'func#([a-zA-Z0-9\s_,(\\)\[\]]+)#', expression)

        for m in matches:
            # Calculate function signature hashes

            sign_hash = utils.sha3(m)[:4].hex()

            expression = expression.replace(m, sign_hash)

        tokens = filter(None, re.split("(and|or|not)", expression.replace(" ", ""), re.IGNORECASE))

        for token in tokens:

            if token in ("and", "or", "not"):
                str_eval += " " + token + " "
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

        return eval(str_eval.strip())


class InstanceList(persistent.Persistent):

    def __init__(self):
        self.addresses = []
        self.balances = []
        pass

    def add(self, address, balance=0):
        self.addresses.append(address)
        self.balances.append(balance)
        self._p_changed = True
