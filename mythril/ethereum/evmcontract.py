"""This module contains the class representing EVM contracts, aka Smart
Contracts."""
import re
import logging
import persistent

from mythril.support.support_utils import sha3
from mythril.disassembler.disassembly import Disassembly
from mythril.support.support_utils import get_code_hash

log = logging.getLogger(__name__)


class EVMContract(persistent.Persistent):
    """This class represents an address with associated code (Smart
    Contract)."""

    def __init__(
        self, code="", creation_code="", name="Unknown", enable_online_lookup=False
    ):
        """Create a new contract.

        Workaround: We currently do not support compile-time linking.
        Dynamic contract addresses of the format __[contract-name]_____________ are replaced with a generic address
        Apply this for creation_code & code

        :param code:
        :param creation_code:
        :param name:
        :param enable_online_lookup:
        """
        creation_code = re.sub(r"(_{2}.{38})", "aa" * 20, creation_code)
        code = re.sub(r"(_{2}.{38})", "aa" * 20, code)
        self.creation_code = creation_code
        self.name = name
        self.code = code
        self.disassembly = Disassembly(code, enable_online_lookup=enable_online_lookup)

        self.creation_disassembly = Disassembly(
            creation_code, enable_online_lookup=enable_online_lookup
        )

    @property
    def bytecode_hash(self):
        """

        :return: runtime bytecode hash
        """
        return get_code_hash(self.code)

    @property
    def creation_bytecode_hash(self):
        """

        :return: Creation bytecode hash
        """
        return get_code_hash(self.creation_code)

    def as_dict(self):
        """

        :return:
        """
        return {
            "name": self.name,
            "code": self.code,
            "creation_code": self.creation_code,
            "disassembly": self.disassembly,
        }

    def get_easm(self):
        """

        :return:
        """
        return self.disassembly.get_easm()

    def get_creation_easm(self):
        """

        :return:
        """
        return self.creation_disassembly.get_easm()

    def matches_expression(self, expression):
        """

        :param expression:
        :return:
        """
        str_eval = ""
        easm_code = None

        tokens = re.split("\s+(and|or|not)\s+", expression, re.IGNORECASE)

        for token in tokens:

            if token in ("and", "or", "not"):
                str_eval += " " + token + " "
                continue

            m = re.match(r"^code#([a-zA-Z0-9\s,\[\]]+)#", token)

            if m:
                if easm_code is None:
                    easm_code = self.get_easm()

                code = m.group(1).replace(",", "\\n")
                str_eval += '"' + code + '" in easm_code'
                continue

            m = re.match(r"^func#([a-zA-Z0-9\s_,(\\)\[\]]+)#$", token)

            if m:

                sign_hash = "0x" + sha3(m.group(1))[:4].hex()
                str_eval += '"' + sign_hash + '" in self.disassembly.func_hashes'

        return eval(str_eval.strip())
