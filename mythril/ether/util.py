from mythril.rpc.client import EthJsonRpc
from ethereum.abi import encode_abi, encode_int
from ethereum.utils import zpad
from ethereum.abi import method_id


def safe_decode(hex_encoded_string):

    # print(type(hex_encoded_string))

    if (hex_encoded_string.startswith("0x")):
        return bytes.fromhex(hex_encoded_string[2:])
        # return codecs.decode(, 'hex_codec')
    else:
        return bytes.fromhex(hex_encoded_string)
        # return codecs.decode(hex_encoded_string, 'hex_codec')


def bytecode_from_blockchain(creation_tx_hash, rpc_host='127.0.0.1', rpc_port=8545):
    """Load bytecode from a local node via
    creation_tx_hash = ID of transaction that created the contract.
    """

    eth = EthJsonRpc(rpc_host, rpc_port)

    trace = eth.traceTransaction(creation_tx_hash)

    if trace['returnValue']:

        return trace['returnValue']

    raise RuntimeError("Transaction trace didn't return any bytecode")


def encode_calldata(func_name, arg_types, args):

    mid = method_id(func_name, arg_types)
    function_selector = zpad(encode_int(mid), 4)
    args = encode_abi(arg_types, args)
    return "0x" + function_selector.hex() + args.hex()

def raw_bytes_to_file(filename, bytestring):
    with open(filename, 'wb') as f:
        f.write(bytestring)


def file_to_raw_bytes(filename):
    with open(filename, 'rb') as f:
        data = f.read()
    return data


def string_to_file(filename, string):
    with open(filename, 'w') as f:
        f.write(string)


def file_to_string(filename):
    with open(filename, 'r') as f:
        data = f.read()
    return data
