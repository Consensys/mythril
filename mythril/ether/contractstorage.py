from mythril.rpc.client import EthJsonRpc
from mythril.ipc.client import EthIpc
from mythril.ether.ethcontract import ETHContract, InstanceList
import hashlib
import os
import time
import persistent
import persistent.list
import transaction
from BTrees.OOBTree import BTree
import ZODB
from ZODB import FileStorage
from mythril import ether

def get_persistent_storage(db_dir = None):

    if not db_dir:
        db_dir = os.path.join(os.path.expanduser('~'), ".mythril")

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


    def initialize(self, eth, sync_all):

        if self.last_block:
            blockNum = self.last_block
            print("Resuming synchronization from block " + str(blockNum))
        else:

            blockNum = eth.eth_blockNumber()
            print("Starting synchronization from latest block: " + str(blockNum))

        ''' 
        On INFURA, the latest block is not immediately available. Here is a workaround to allow for database sync over INFURA.
        Note however that this is extremely slow, contracts should always be loaded from a local node.
        '''

        block = eth.eth_getBlockByNumber(blockNum)

        if not block:
            blockNum -= 2

        while(blockNum > 0):
            # print("blockNum: " + str(blockNum))
            ether.sync_count += 1
            if ether.sync_count == 10000:
                end_time = time.time()
                print("10000 blocks cost {} seconds".format(end_time - ether.start_time))


            if not blockNum % 1000:
                print("Processing block " + str(blockNum) + ", " + str(len(self.contracts.keys())) + " unique contracts in database")

            block = eth.eth_getBlockByNumber(blockNum)

            for tx in block['transactions']:

                if not tx['to']:

                    receipt = eth.eth_getTransactionReceipt(tx['hash'])

                    if receipt is not None:

                        contract_address = receipt['contractAddress']

                        contract_code = eth.eth_getCode(contract_address)
                        contract_balance = eth.eth_getBalance(contract_address)

                        if not contract_balance and not sync_all:
                            # skip contracts with zero balance (disable with --sync-all)
                            continue

                        code = ETHContract(contract_code, tx['input'])

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

        # If we've finished initializing the database, start over from the end of the chain if we want to initialize again
        self.last_block = 0
        transaction.commit()


    def search(self, expression, callback_func):

        all_keys = list(self.contracts)

        for k in all_keys:

            if self.contracts[k].matches_expression(expression):

                m = self.instance_lists[k]

                callback_func(k.hex(), self.contracts[k], m.addresses, m.balances)
