from mythril.rpc.client import EthJsonRpc
from mythril.ether.ethcontract import ETHContract, InstanceList
import hashlib
import os
import persistent
import persistent.list
import transaction
from BTrees.OOBTree import BTree
import ZODB
from ZODB import FileStorage


def get_persistent_storage(db_dir):
    if not os.path.exists(db_dir):
        os.makedirs(db_dir)

    db_path = os.path.join(db_dir, "contractstorage.fs")

    storage = FileStorage.FileStorage(db_path)
    db = ZODB.DB(storage)
    connection = db.open()
    storage_root = connection.root()

    try:
        contract_storage = storage_root['contractStorage']
    except KeyError:
        contract_storage = ContractStorage()
        storage_root['contractStorage'] = contract_storage

    return contract_storage


class ContractStorage(persistent.Persistent):

    def __init__(self):
        self.contracts = BTree()
        self.instance_lists= BTree()
        self.last_block = 0


    def get_contract_by_hash(self, contract_hash):
        return self.contracts[contract_hash]


    def initialize(self, rpchost, rpcport, sync_all):

        eth = EthJsonRpc(rpchost, rpcport)

        if self.last_block:
            blockNum = self.last_block
            print("Resuming synchronization from block " + str(blockNum))
        else:

            blockNum = eth.eth_blockNumber()
            print("Starting synchronization from latest block: " + str(blockNum))

        while(blockNum > 0):

            if not blockNum % 1000:
                print("Processing block " + str(blockNum) + ", " + str(len(self.contracts.keys())) + " individual contracts in database")

            block = eth.eth_getBlockByNumber(blockNum)

            for tx in block['transactions']:

                if not tx['to']:

                    receipt = eth.eth_getTransactionReceipt(tx['hash'])

                    contract_address = receipt['contractAddress']

                    contract_code = eth.eth_getCode(contract_address)
                    contract_balance = eth.eth_getBalance(contract_address)

                    if not contract_balance or sync_all:
                        # skip contracts with zero balance (disable with --sync-all)
                        continue

                    code = ETHContract(contract_code)

                    m = hashlib.md5()
                    m.update(contract_code.encode('UTF-8'))
                    contract_hash = m.digest()

                    try:
                        self.contracts[contract_hash]
                    except KeyError:
                        self.contracts[contract_hash] = code
                        m = InstanceList()
                        self.instance_lists[contract_hash] = m

                    self.instance_lists[contract_hash].add(contract_address, contract_balance)

                    transaction.commit()

            self.last_block = blockNum
            blockNum -= 1


    def search(self, expression, callback_func):

        all_keys = list(self.contracts)

        for k in all_keys:

            if self.contracts[k].matches_expression(expression):

                m = hashlib.md5()
                m.update(self.contracts[k].code.encode('UTF-8'))
                contract_hash = m.digest()

                m = self.instance_lists[contract_hash]

                callback_func(contract_hash.hex(), self.contracts[k], m.addresses, m.balances)
