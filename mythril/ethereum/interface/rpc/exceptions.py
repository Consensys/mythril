class EthJsonRpcError(Exception):
    pass


class ConnectionError(EthJsonRpcError):
    pass


class BadStatusCodeError(EthJsonRpcError):
    pass


class BadJsonError(EthJsonRpcError):
    pass


class BadResponseError(EthJsonRpcError):
    pass
