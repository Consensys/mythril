from ethereum.abi import encode_abi, encode_int
from ethereum.utils import zpad
from ethereum.abi import method_id
from mythril.exceptions import CompilerError
from subprocess import Popen, PIPE
import binascii
import os
import json


def safe_decode(hex_encoded_string):

    if (hex_encoded_string.startswith("0x")):
        return bytes.fromhex(hex_encoded_string[2:])
    else:
        return bytes.fromhex(hex_encoded_string)


def get_solc_json(file, solc_binary="solc", solc_args=None):

    cmd = [solc_binary, "--combined-json", "bin,bin-runtime,srcmap-runtime,abi", '--allow-paths', "."]

    if solc_args:
        cmd.extend(solc_args.split(" "))

    cmd.append(file)

    try:
        p = Popen(cmd, stdout=PIPE, stderr=PIPE)

        stdout, stderr = p.communicate()
        ret = p.returncode

        if ret != 0:
            raise CompilerError("Solc experienced a fatal error (code %d).\n\n%s" % (ret, stderr.decode('UTF-8')))
    except FileNotFoundError:
        raise CompilerError("Compiler not found. Make sure that solc is installed and in PATH, or set the SOLC environment variable.")

    out = stdout.decode("UTF-8")

    if not len(out):
        raise CompilerError("Compilation failed.")

    return json.loads(out)


def encode_calldata(func_name, arg_types, args):
    mid = method_id(func_name, arg_types)
    function_selector = zpad(encode_int(mid), 4)
    args = encode_abi(arg_types, args)
    return "0x" + function_selector.hex() + args.hex()


def get_random_address():
    return binascii.b2a_hex(os.urandom(20)).decode('UTF-8')


def get_indexed_address(index):
    return "0x" + (hex(index)[2:] * 40)


def solc_exists(version):
    solc_binary = os.path.join(os.environ['HOME'], ".py-solc/solc-v" + version, "bin/solc")
    if os.path.exists(solc_binary):
        return True
    else:
        return False
