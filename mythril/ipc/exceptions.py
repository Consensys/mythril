class EthIpcError(Exception):
    pass


class ConnectionError(EthIpcError):
    pass


class BadStatusCodeError(EthIpcError):
    pass


class BadJsonError(EthIpcError):
    pass


class BadResponseError(EthIpcError):
    pass
