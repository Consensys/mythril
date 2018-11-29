from unittest import TestCase
from tests import BaseTestCase

from mythril.ethereum.interface.rpc.client import EthJsonRpc


class RpcTest(BaseTestCase):
    client = None

    def setUp(self):
        self.client = EthJsonRpc()

    def tearDown(self):
        self.client.close()

    def test_eth_coinbase(self):
        coinbase = self.client.eth_coinbase()
        self.assertTrue(coinbase.startswith("0x"), "coinbase should be a hex string")
        self.assertEqual(len(coinbase), 42, "coinbase is a string with length of 42")

    def test_eth_blockNumber(self):
        block_number = self.client.eth_blockNumber()
        self.assertGreater(
            block_number, 0, "we have made sure the blockNumber is > 0 for testing"
        )

    def test_eth_getBalance(self):
        balance = self.client.eth_getBalance(
            address="0x0000000000000000000000000000000000000000"
        )
        self.assertGreater(
            balance, 10000000, "specified address should have a lot of balance"
        )

    def test_eth_getStorageAt(self):
        storage = self.client.eth_getStorageAt(
            address="0x0000000000000000000000000000000000000000"
        )
        self.assertEqual(
            storage,
            "0x0000000000000000000000000000000000000000000000000000000000000000",
        )

    def test_eth_getBlockByNumber(self):
        block = self.client.eth_getBlockByNumber(0)
        self.assertEqual(
            block["extraData"],
            "0x11bbe8db4e347b4e8c937c1c8370e4b5ed33adb3db69cbdb7a38e1e50b1b82fa",
            "the data of the first block should be right",
        )

    def test_eth_getCode(self):
        # TODO: can't find a proper address for getting code
        code = self.client.eth_getCode(
            address="0x0000000000000000000000000000000000000001"
        )
        self.assertEqual(code, "0x")

    def test_eth_getTransactionReceipt(self):
        transaction = self.client.eth_getTransactionReceipt(
            tx_hash="0xe363505adc6b2996111f8bd774f8653a61d244cc6567b5372c2e781c6c63b737"
        )
        self.assertEqual(
            transaction["from"], "0x22f2dcff5ad78c3eb6850b5cb951127b659522e6"
        )
        self.assertEqual(
            transaction["to"], "0x0000000000000000000000000000000000000000"
        )
