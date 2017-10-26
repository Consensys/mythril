from ethereum.abi import encode_abi, encode_int
from ethereum.utils import zpad
from ethereum.abi import method_id
import subprocess
import re


def safe_decode(hex_encoded_string):
    if (hex_encoded_string.startswith("0x")):
        return bytes.fromhex(hex_encoded_string[2:])
    else:
        return bytes.fromhex(hex_encoded_string)


def compile_solidity(solc_binary, file):
    output = subprocess.check_output(["solc", "--bin-runtime", file],  stderr=subprocess.DEVNULL)

    m = re.search(r"runtime part: \\n(.*)\\n", str(output))
    return m.group(1)


def encode_calldata(func_name, arg_types, args):
    mid = method_id(func_name, arg_types)
    function_selector = zpad(encode_int(mid), 4)
    args = encode_abi(arg_types, args)
    return "0x" + function_selector.hex() + args.hex()
