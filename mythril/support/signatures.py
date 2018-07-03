import re
import os
import logging
import json
from ethereum import utils

try:
    # load if available but do not fail
    import ethereum_input_decoder
except ImportError:
    ethereum_input_decoder = None


# TODO: tintinweb: move this and signature functionality from mythril.py to class Signatures to have one single interface.
def add_signatures_from_file(file, sigs={}):

    funcs = []

    with open(file, encoding="utf-8") as f:

        code = f.read()

    funcs = re.findall(r'function[\s]+(\w+\([^\)]*\))', code, re.DOTALL)

    for f in funcs:

        f = re.sub(r'[\n]', '', f)

        m = re.search(r'^([A-Za-z0-9_]+)', f)

        if (m):

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

            signature = re.sub(r'\s', '', signature)

            sigs["0x" + utils.sha3(signature)[:4].hex()] = signature


class Signatures(object):

    def __init__(self, enable_online_lookup=True):
        self.signatures = {}  # signatures in-mem cache
        self.enable_online_lookup =enable_online_lookup  # enable online funcsig resolving

    def open(self, path=None):
        if not path:
            #  try default locations
            try:
                mythril_dir = os.environ['MYTHRIL_DIR']
            except KeyError:
                mythril_dir = os.path.join(os.path.expanduser('~'), ".mythril")
            path = os.path.join(mythril_dir, 'signatures.json')

        if not os.path.exists(path):
            raise FileNotFoundError("Missing function signature file. Resolving of function names disabled.")

        with open(path) as f:
            sigs = json.load(f)

        # normalize it to {sighash:list(signatures,...)}
        for sighash,funcsig in sigs.items():
            self.signatures.setdefault(sighash, [])
            self.signatures[sighash].append(funcsig)

        return self

    def get(self, sighash):
        """
        get a function signature for a sighash
        1) try local cache
        2) try online lookup
        :param sighash:
        :return: list of function signatures
        """
        if not self.signatures.get(sighash) and self.enable_online_lookup:
            funcsigs = Signatures.lookup_online(sighash)  # might return multiple sigs
            if funcsigs:
                # only store if we get at least one result
                self.signatures[sighash] = funcsigs
        return self.signatures[sighash]  # raise keyerror


    @staticmethod
    def lookup_online(sighash):
        """
        Lookup function signatures from 4byte.directory.
        //tintinweb: the smart-contract-sanctuary project dumps contracts from etherscan.io and feeds them into
                     4bytes.directory.
                     https://github.com/tintinweb/smart-contract-sanctuary

        :param s: function signature as hexstr
        :return: a list of possible function signatures for this hash
        """
        if not ethereum_input_decoder:
            return None
        return list(ethereum_input_decoder.decoder.FourByteDirectory.lookup_signatures(sighash))
