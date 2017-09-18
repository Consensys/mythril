from ether.jsonrpc import EthJsonRpcWithDebug


def safe_decode(hex_encoded_string):
    if (hex_encoded_string.startswith("0x")):
        return hex_encoded_string[2:].decode("hex")
    else:
        return hex_encoded_string.decode("hex")


def bytecode_from_blockchain(creation_tx_hash, rpc_host='127.0.0.1', rpc_port=8545):
    """Load bytecode from a local node via
    creation_tx_hash = ID of transaction that created the contract.
    """

    eth = EthJsonRpcWithDebug(rpc_host, 8545)

    trace = eth.traceTransaction(creation_tx_hash)

    if trace['returnValue']:

        return trace['returnValue']

    raise RuntimeError("Transaction trace didn't return any bytecode")


def string_to_file(filename, string):
    outfile = open(filename, "w")
    outfile.write(string)
    outfile.close()


def file_to_string(filename):
    infile = open(filename, "r")
    return infile.read()
