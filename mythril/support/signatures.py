import re
from ethereum import utils

def add_signatures_from_file(file, sigs={}):

    funcs = []

    with open(file, encoding="utf-8") as f:
        for line in f:

            m = re.search(r'function\s+(.*\))', line)

            if m:
                funcs.append(m.group(1))

    for f in funcs:
        m = re.search(r'^([A-Za-z0-9_]+)', f)

        signature = m.group(1)

        m = re.search(r'\((.*)\)', f)
        _args = m.group(1).split(",")

        types = []

        for arg in _args:

            _type = arg.lstrip().split(" ")[0]
            if _type == "uint":
                _type = "uint256"

            types.append(_type)

        typelist = ",".join(types)
        signature += "(" + typelist + ")"

        sigs["0x" + utils.sha3(signature)[:4].hex()] = signature
