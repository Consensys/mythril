"""This module provides a basic RPC interface client.

This code is adapted from: https://github.com/ConsenSys/ethjsonrpc
"""

from abc import abstractmethod

from .constants import BLOCK_TAGS, BLOCK_TAG_LATEST
from .utils import hex_to_dec, validate_block

GETH_DEFAULT_RPC_PORT = 8545
ETH_DEFAULT_RPC_PORT = 8545
PARITY_DEFAULT_RPC_PORT = 8545
PYETHAPP_DEFAULT_RPC_PORT = 4000
MAX_RETRIES = 3
JSON_MEDIA_TYPE = "application/json"


class BaseClient(object):
    """The base RPC client class."""

    @abstractmethod
    def _call(self, method, params=None, _id=1):
        """TODO: documentation

        :param method:
        :param params:
        :param _id:
        :return:
        """

        pass

    def eth_coinbase(self):
        """TODO: documentation

        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_coinbase

        TESTED
        """
        return self._call("eth_coinbase")

    def eth_blockNumber(self):
        """TODO: documentation

        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_blocknumber

        TESTED
        """
        return hex_to_dec(self._call("eth_blockNumber"))

    def eth_getBalance(self, address=None, block=BLOCK_TAG_LATEST):
        """TODO: documentation

        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_getbalance

        TESTED
        """
        address = address or self.eth_coinbase()
        block = validate_block(block)
        return hex_to_dec(self._call("eth_getBalance", [address, block]))

    def eth_getStorageAt(self, address=None, position=0, block=BLOCK_TAG_LATEST):
        """TODO: documentation

        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_getstorageat

        TESTED
        """
        block = validate_block(block)
        return self._call("eth_getStorageAt", [address, hex(position), block])

    def eth_getCode(self, address, default_block=BLOCK_TAG_LATEST):
        """TODO: documentation

        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_getcode

        NEEDS TESTING
        """
        if isinstance(default_block, str):
            if default_block not in BLOCK_TAGS:
                raise ValueError
        return self._call("eth_getCode", [address, default_block])

    def eth_getBlockByNumber(self, block=BLOCK_TAG_LATEST, tx_objects=True):
        """TODO: documentation

        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_getblockbynumber

        TESTED
        """
        block = validate_block(block)
        return self._call("eth_getBlockByNumber", [block, tx_objects])

    def eth_getTransactionReceipt(self, tx_hash):
        """TODO: documentation

        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_gettransactionreceipt

        TESTED
        """
        return self._call("eth_getTransactionReceipt", [tx_hash])
