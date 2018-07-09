from re import search
from mythril.exceptions import CompilerError
from subprocess import Popen, PIPE
import json
import sys

class CalldataMap:

    def __init__(self, abi, solc_v):
        pass

    def __init__(self, solidity_file, solc_v):
        pass

def get_minimal_param_encoding_len(abi_inputs):
    len = 0
    return len

def get_minimal_byte_enc_len(abi_obj):
    if type(abi_obj) == list:
        return sum([head_byte_length_min(t) for t in abi_obj]) + sum([tail_byte_length_min(t) for t in abi_obj])
    if type(abi_obj) == str:
        stype = abi_obj
    else:
        stype = abi_obj['type']
    if stype == 'tuple':
        return get_minimal_byte_enc_len(abi_obj['components'])
    try:
        match = search(r'(?P<pre>.*)\[(?P<post>[0-9]+)\]', stype)
        pre = match['pre']
        post = match['post']
        return int(post) * get_minimal_byte_enc_len(pre)
    except (KeyError, TypeError) as e:
        pass
    if stype.endswith("[]"):
        return 32

    if stype == "string":
        return 32
    elif stype == "bytes":
        return 32 # 2 was the smallest observed value, remix did not allow specification of zero size bytes
    elif [stype.startswith(prefix_type) for prefix_type in ["int", "uint", "address", "bool", "fixed", "ufixed", "bytes"]]:
        return 32

def head_byte_length_min(abi_obj):
    if is_dynamic(abi_obj):
        return 32
    else:
        return get_minimal_byte_enc_len(abi_obj)


def tail_byte_length_min(abi_obj):
    if is_dynamic(abi_obj):
        return get_minimal_byte_enc_len(abi_obj)
    else:
        return 0

def get_minimal_wsize(abi_obj):
    stype = abi_obj['type']
    if type(stype) == list:
        return sum(list(map(lambda a: get_minimal_wsize(a), stype)))
    if stype in ["bytes", "string"] or stype.endswith("[]"):
        return True
    if stype == 'tuple':
        return True in [is_dynamic(elem) for elem in abi_obj['components']]
    try:
        match = search(r'(?P<pre>.*)(?P<post>\[[0-9]+\])', stype)
        pre = match['pre']
        # post = match['post']
        return is_dynamic(pre)
    except (KeyError | TypeError):
        pass
    return False


def get_minimal_constructor_param_encoding_len(abi):
    for spec in abi:
        try:
            if spec['type'] == 'constructor':
                con_inputs = spec['inputs']
                return get_minimal_byte_enc_len(con_inputs)
        except KeyError:
            print("ABI does not contain inputs for constructor")
    return -1

def get_minimal_constr_param_byte_length(filename, contract_name=None):
    abi_decoded = get_solc_abi_json(filename)
    return get_minimal_constructor_param_encoding_len(abi_decoded)

def is_dynamic(abi_obj):
    if type(abi_obj) == list:
        return True in list(map(lambda a: is_dynamic(a), abi_obj))
    if type(abi_obj) == str:
        stype = abi_obj
    else:
        stype = abi_obj['type']
    if stype in ["bytes", "string"] or stype.endswith("[]"):
        return True
    if stype == 'tuple':
        return True in [is_dynamic(elem) for elem in abi_obj['components']]
    try:
        match = search(r'(?P<pre>.*)(?P<post>\[[0-9]+\])', stype)
        pre = match['pre']
        # post = match['post']
        return is_dynamic(pre)
    except (KeyError, TypeError) as e:
        pass
    return False

def get_solc_abi_json(file, solc_binary="solc", solc_args=None):

    cmd = [solc_binary, "--abi", '--allow-paths', "."]

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

    out = out[out.index("["):]

    print(out)

    return json.loads(out)

def abi_json_to_abi(abi_json):
    return json.loads(abi_json)


if __name__ == "__main__":
    if len(sys.argv) > 1:
        print("Size:")
        print(get_minimal_constr_param_byte_length(sys.argv[1]))
    else:
        print("Error: No file specified")
