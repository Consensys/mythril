from unittest import TestCase, skip

from mythril.ipc.utils import hex_to_dec
from mythril.rpc.client import EthJsonRpc

class RpcTest(TestCase):
    client = None

    def _new_filter(self):
        return self.client.eth_newFilter(from_block="0x1", to_block="0x2", address="0x8888f1f195afa192cfee860698584c030f4c9db1")

    def setUp(self):
        self.client = EthJsonRpc()

    def tearDown(self):
        self.client.close()

    def test_web3_clientVersion(self):
        version = self.client.web3_clientVersion()
        self.assertTrue("Geth/" in version, "We should use real `geth` to test")

    def test_web3_sha3(self):
        sha3 = self.client.web3_sha3("contract A {}")
        self.assertEqual(sha3, "0x713073fa3404d26d3eb1ada031e6b51a3a0c135d0ee7c72ec87e0e77e004cf8c")

    def test_net_version(self):
        version = self.client.net_version()
        self.assertEqual(version, '1', "We use mainnet for testing, whose version is '1'")

    def test_net_listening(self):
        listening = self.client.net_listening()
        self.assertTrue(listening, "should be listening")

    def test_net_peerCount(self):
        count = self.client.net_peerCount()
        self.assertGreater(count, 0, "peerCount should >0 when syncing")

    def test_eth_protocolVersion(self):
        version = self.client.eth_protocolVersion()
        self.assertTrue(version.startswith("0x"))

    def test_eth_syncing(self):
        syncing = self.client.eth_syncing()
        highest_block = hex_to_dec(syncing["highestBlock"])
        current_block = hex_to_dec(syncing["currentBlock"])
        self.assertTrue(current_block > 0, "current_block should > 0 since we make sure of it for testing")
        self.assertTrue(highest_block >= current_block)

    def test_eth_coinbase(self):
        coinbase = self.client.eth_coinbase()
        self.assertTrue(coinbase.startswith("0x"), "coinbase should be a hex string")
        self.assertEqual(len(coinbase), 42, "coinbase is a string with length of 42")

    def test_eth_mining(self):
        mining = self.client.eth_mining()
        self.assertEqual(type(mining), bool)

    def test_eth_hashrate(self):
        hashrate = self.client.eth_hashrate()
        self.assertEqual(type(hashrate), int)

    def test_eth_gasPrice(self):
        price = self.client.eth_gasPrice()
        self.assertGreater(price, 0, "gas price should be > 0")

    def test_eth_accounts(self):
        accounts = self.client.eth_accounts()
        self.assertGreater(len(accounts), 0)
        self.assertEqual(len(accounts[0]), 42, "account is a string with length of 42")
        self.assertTrue(accounts[0].startswith("0x"), "account is hex string")

    def test_eth_blockNumber(self):
        block_number = self.client.eth_blockNumber()
        self.assertGreater(block_number, 0, "we have made sure the blockNumber is > 0 for testing")

    def test_eth_getBalance(self):
        balance = self.client.eth_getBalance(address="0x0000000000000000000000000000000000000000")
        self.assertGreater(balance, 10000000, "specified address should have a lot of balance")

    def test_eth_getStorageAt(self):
        storage = self.client.eth_getStorageAt(address="0x0000000000000000000000000000000000000000")
        self.assertEqual(storage, '0x0000000000000000000000000000000000000000000000000000000000000000')

    @skip("Not sure how to test this unless use some kind of mocks")
    def test_create_contract(self):
        self.client.create_contract(from_="0x0000000000000000000000000000000000000000", code="0x636f6e747261637420417b7d", gas=1)
        pass

    def test_eth_call(self):
        # TODO need to give a better test case
        result = self.client.eth_call(to_address="0x0000000000000000000000000000000000000000")
        self.assertEqual(result, "0x")

    @skip("{'jsonrpc': '2.0', 'id': 1, 'error': {'code': -32602, 'message': 'too many arguments, want at most 1'}}")
    def test_eth_estimateGas(self):
        x = self.client.eth_estimateGas()
        print(x)

    def test_eth_getBlockByHash(self):
        block = self.client.eth_getBlockByHash("0xd4e56740f876aef8c010b86a40d5f56745a118d0906a34e69aec8c0db1cb8fa3")
        self.assertEqual(block["extraData"], "0x11bbe8db4e347b4e8c937c1c8370e4b5ed33adb3db69cbdb7a38e1e50b1b82fa", "the data of the first block should be right")

    def test_eth_getBlockByNumber(self):
        block = self.client.eth_getBlockByNumber(0)
        self.assertEqual(block["extraData"], "0x11bbe8db4e347b4e8c937c1c8370e4b5ed33adb3db69cbdb7a38e1e50b1b82fa", "the data of the first block should be right")

    def test_eth_getBlockTransactionCountByHash(self):
        # TODO: can't find a block which contains transactions after checking thousands of blocks
        count = self.client.eth_getBlockTransactionCountByHash("0xd4e56740f876aef8c010b86a40d5f56745a118d0906a34e69aec8c0db1cb8fa3")
        self.assertEqual(count, 0)

    def test_eth_getBlockTransactionCountByNumber(self):
        # TODO: can't find a proper block
        count = self.client.eth_getBlockTransactionCountByNumber(0)
        self.assertEqual(count, 0)

    def test_eth_getCode(self):
        # TODO: can't find a proper address for getting code
        code = self.client.eth_getCode(address="0x0000000000000000000000000000000000000001")
        self.assertEqual(code, "0x")

    def test_eth_getFilterChanges(self):
        filter_id = self._new_filter()
        changes = self.client.eth_getFilterChanges(filter_id)
        self.assertEqual(type(changes), list)

    def test_eth_getFilterLogs(self):
        filter_id = self._new_filter()
        logs = self.client.eth_getFilterLogs(filter_id)
        self.assertEqual(type(logs), list)

    def test_eth_getLogs(self):
        # TODO: can't find proper filter_object to return an non-empty response
        logs = self.client.eth_getLogs(filter_object={
            "topics": ["0x000000000000000000000000a94f5374fce5edbc8e2a8697c15331677e6ebf0b"]
        })
        self.assertEqual(type(logs), list)

    def test_eth_getTransactionByBlockHashAndIndex(self):
        transaction = self.client.eth_getTransactionByBlockHashAndIndex(block_hash="0x7e5a9336dd82efff0bfe8c25ccb0e8cf44b4c6f781b25b3fc3578f004f60b872")
        self.assertEqual(transaction["from"], "0x22f2dcff5ad78c3eb6850b5cb951127b659522e6")
        self.assertEqual(transaction["to"], "0x0000000000000000000000000000000000000000")

    def test_eth_getTransactionByBlockNumberAndIndex(self):
        transaction = self.client.eth_getTransactionByBlockNumberAndIndex(block=46420)
        self.assertEqual(transaction["blockHash"], "0x7e5a9336dd82efff0bfe8c25ccb0e8cf44b4c6f781b25b3fc3578f004f60b872")

    def test_eth_getTransactionByHash(self):
        transaction = self.client.eth_getTransactionByHash(tx_hash="0xe363505adc6b2996111f8bd774f8653a61d244cc6567b5372c2e781c6c63b737")
        self.assertEqual(transaction["from"], "0x22f2dcff5ad78c3eb6850b5cb951127b659522e6")
        self.assertEqual(transaction["to"], "0x0000000000000000000000000000000000000000")

    def test_eth_getTransactionCount(self):
        count = self.client.eth_getTransactionCount(address="0x22f2dcff5ad78c3eb6850b5cb951127b659522e6")
        self.assertGreater(count, 17, "The address should at least have 18 transactions")

    def test_eth_getTransactionReceipt(self):
        transaction = self.client.eth_getTransactionReceipt(tx_hash="0xe363505adc6b2996111f8bd774f8653a61d244cc6567b5372c2e781c6c63b737")
        self.assertEqual(transaction["from"], "0x22f2dcff5ad78c3eb6850b5cb951127b659522e6")
        self.assertEqual(transaction["to"], "0x0000000000000000000000000000000000000000")

    def test_eth_getUncleByBlockHashAndIndex(self):
        uncle = self.client.eth_getUncleByBlockHashAndIndex(block_hash="0x07efc5598ed7e5e6e707eb087110f2dfb2772d6355508b75f4696d96d0f747ec")
        self.assertEqual(uncle["hash"], "0x78b57d7dd0b797cdf91f88807d761a7a0099f417be98b08ec600a2142e66af9e")

    def test_eth_getUncleByBlockNumberAndIndex(self):
        uncle = self.client.eth_getUncleByBlockNumberAndIndex(block=105)
        self.assertEqual(uncle["hash"], "0x78b57d7dd0b797cdf91f88807d761a7a0099f417be98b08ec600a2142e66af9e")

    def test_eth_getUncleCountByBlockHash(self):
        count = self.client.eth_getUncleCountByBlockHash(block_hash="0x07efc5598ed7e5e6e707eb087110f2dfb2772d6355508b75f4696d96d0f747ec")
        self.assertEqual(count, 1, "there should be 1 uncle at block 105")

    def test_eth_getUncleCountByBlockNumber(self):
        count = self.client.eth_getUncleCountByBlockNumber(105)
        self.assertEqual(count, 1, "there should be 1 uncle at block 105")

    def test_eth_getWork(self):
        work = self.client.eth_getWork()
        self.assertEqual(len(work), 3)
        self.assertTrue(work[0].startswith("0x"), "should be a hex")
        self.assertTrue(work[1].startswith("0x"), "should be a hex")
        self.assertTrue(work[2].startswith("0x"), "should be a hex")

    def test_eth_newBlockFilter(self):
        filter_id = self.client.eth_newBlockFilter()
        self.assertTrue(filter_id.startswith("0x"), "filter_id is a hex string")

    def test_eth_newFilter(self):
        filter_id = self.client.eth_newFilter(from_block="0x1", to_block="0x2", address="0x8888f1f195afa192cfee860698584c030f4c9db1",
                                              topics=["0x000000000000000000000000a94f5374fce5edbc8e2a8697c15331677e6ebf0b"])
        self.assertTrue(filter_id.startswith("0x"))

    def test_eth_newPendingTransactionFilter(self):
        filter_id = self.client.eth_newPendingTransactionFilter()
        self.assertTrue(filter_id.startswith("0x"), "filter_id should be a hex")

    @skip("{'jsonrpc': '2.0', 'id': 1, 'error': {'code': -32000, 'message': 'rlp: element is larger than containing list'}}")
    def test_eth_sendRawTransaction(self):
        x = self.client.eth_sendRawTransaction(data="0xd46e8dd67c5d32be8d46e8dd67c5d32be8058bb8eb970870f072445675058bb8eb970870f072445675")
        print(x)

    @skip("{'jsonrpc': '2.0', 'id': 1, 'error': {'code': -32000, 'message': 'authentication needed: password or unlock'}}")
    def test_eth_sendTransaction(self):
        x = self.client.eth_sendTransaction(to_address="0x0000000000000000000000000000000000000000",
                                            gas=30400, gas_price=10000000000000, value=2441406250,
                                            data="0xd46e8dd67c5d32be8d46e8dd67c5d32be8058bb8eb970870f072445675058bb8eb970870f072445675")
        print(x)

    @skip("server returns {'jsonrpc': '2.0', 'id': 1, 'error': {'code': -32000, 'message': 'unknown account'}}, not sure how to fix it")
    def test_eth_sign(self):
        x = self.client.eth_sign(address="0x9b2055d370f73ec7d8a03e965129118dc8f5bf83", data="0xdeadbeaf")
        print(x)

    def test_eth_submitHashrate(self):
        submitted = self.client.eth_submitHashrate(hash_rate=5242880,
                                                   client_id="0x59daa26581d0acd1fce254fb7e85952f4c09d0915afd33d3886cd914bc7d283c")
        self.assertTrue(submitted, "Should submit hashrate successfully")

    def test_eth_submitWork(self):
        work_accepted = self.client.eth_submitWork(nonce="0x0000000000000001",
                                                   header="0x1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef",
                                                   mix_digest="0xD1FE5700000000000000000000000000D1FE5700000000000000000000000000")
        self.assertFalse(work_accepted, "Work should be rejected")

    def test_eth_uninstallFilter(self):
        filter_id = self._new_filter()
        uninstalled = self.client.eth_uninstallFilter(filter_id)
        self.assertTrue(uninstalled, "filter_id should be uninstalled")

    def test_get_contract_address(self):
        # TODO need to find a tx which has non-none contract address
        address = self.client.get_contract_address(tx="0xe363505adc6b2996111f8bd774f8653a61d244cc6567b5372c2e781c6c63b737")
        self.assertEqual(address, None)

    def test_shh_version(self):
        version = self.client.shh_version()
        self.assertEqual(version, "5.0", "shh_version should be 5.0 for current ethereum release")

    @skip("{'jsonrpc': '2.0', 'id': 1, 'error': {'code': -32000, 'message': 'unknown account'}}")
    def test_transfer(self):
        x = self.client.transfer(from_="0x22f2dcff5ad78c3eb6850b5cb951127b659522e6", to="0x0000000000000000000000000000000000000000", amount=1)
        print(x)
