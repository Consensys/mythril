from ether.jsonrpc import EthJsonRpcWithDebug
import codecs


def safe_decode(hex_encoded_string):
    if (hex_encoded_string.startswith("0x")):
        return codecs.decode(hex_encoded_string[2:], 'hex_codec')
    else:
        return codecs.decode(hex_encoded_string, 'hex_codec')


def bytecode_from_blockchain(creation_tx_hash, rpc_host='127.0.0.1', rpc_port=8545):
    """Load bytecode from a local node via
    creation_tx_hash = ID of transaction that created the contract.
    """

    eth = EthJsonRpcWithDebug(rpc_host, rpc_port)

    trace = eth.traceTransaction(creation_tx_hash)

    if trace['returnValue']:

        return trace['returnValue']

    raise RuntimeError("Transaction trace didn't return any bytecode")


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
