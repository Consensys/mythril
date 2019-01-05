"""This module contains exceptions regarding JSON-RPC communication."""


class EthJsonRpcError(Exception):
    """The JSON-RPC base exception type."""

    pass


class ConnectionError(EthJsonRpcError):
    """An RPC exception denoting there was an error in connecting to the RPC
    instance."""

    pass


class BadStatusCodeError(EthJsonRpcError):
    """An RPC exception denoting a bad status code returned by the RPC
    instance."""

    pass


class BadJsonError(EthJsonRpcError):
    """An RPC exception denoting that the RPC instance returned a bad JSON
    object."""

    pass


class BadResponseError(EthJsonRpcError):
    """An RPC exception denoting that the RPC instance returned a bad
    response."""

    pass
