from ethereum.abi import encode_abi, encode_int
from ethereum.utils import zpad
from ethereum.abi import method_id
from mythril.exceptions import CompilerError
from subprocess import Popen, PIPE
import binascii
import os
import re


def safe_decode(hex_encoded_string):

    if (hex_encoded_string.startswith("0x")):
        return bytes.fromhex(hex_encoded_string[2:])
    else:
        return bytes.fromhex(hex_encoded_string)


def compile_solidity(file, solc_binary="solc"):
    
    try:
        p = Popen([solc_binary, "--bin-runtime", '--allow-paths', ".", file], stdout=PIPE, stderr=PIPE)
        stdout, stderr = p.communicate()
        ret = p.returncode
        if ret < 0:
            raise CompilerError("The Solidity compiler experienced a fatal error (code %d). Please check the Solidity compiler." % ret)
    except FileNotFoundError:
        raise CompilerError("Compiler not found. Make sure that solc is installed and in PATH, or set the SOLC environment variable.")        

    out = stdout.decode("UTF-8")

    if out == "":
        err = "Error compiling input file. Solc returned:\n" + stderr.decode("UTF-8")
        raise CompilerError(err)

    m = re.search(r":(.*?) =======\nBinary of the runtime part:", out)
    contract_name = m.group(1)

    if m:

        m = re.search(r"runtime part: \n([0-9a-f]+)\n", out)

        if (m):
            return [contract_name, m.group(1)]
        else:
            return [contract_name, "0x00"]

    else:
        err = "Could not retrieve bytecode from solc output. Solc returned:\n" + stdout.decode("UTF-8")
        raise CompilerError(err)       


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
    solc_binary = os.environ['HOME'] + "/.py-solc/solc-v" + version + "/bin/solc"
    if os.path.exists(solc_binary):
        return True
    else:
        return False
        