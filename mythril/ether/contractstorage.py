import os
import hashlib
import persistent
import persistent.list
import transaction
from BTrees.OOBTree import BTree
import ZODB
from ZODB import FileStorage
from multiprocessing import Pool
import logging
from mythril.ether.ethcontract import ETHContract, InstanceList


BLOCKS_PER_THREAD = 256
NUM_THREADS = 8


def get_persistent_storage(db_dir=None):

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
        self.instance_lists = BTree()
        self.last_block = 0
        self.eth = None

    def get_contract_by_hash(self, contract_hash):
        return self.contracts[contract_hash]

    def sync_blocks(self, startblock):
        logging.info("SYNC_BLOCKS %d to %d" % (startblock, startblock + BLOCKS_PER_THREAD))

        contracts = {}

        for blockNum in range(startblock, startblock + BLOCKS_PER_THREAD):
            block = self.eth.eth_getBlockByNumber(blockNum)

            for tx in block['transactions']:

                if not tx['to']:

                    receipt = self.eth.eth_getTransactionReceipt(tx['hash'])

                    if receipt is not None:

                        contract_address = receipt['contractAddress']

                        contract_code = self.eth.eth_getCode(contract_address)
                        contract_balance = self.eth.eth_getBalance(contract_address)

                        if not contract_balance:
                            continue

                        ethcontract = ETHContract(contract_code, tx['input'])

                        m = hashlib.md5()
                        m.update(contract_code.encode('UTF-8'))
                        contract_hash = m.digest()

                        contracts[contract_hash] = {'ethcontract': ethcontract, 'address': contract_address, 'balance': contract_balance}

            blockNum -= 1

        return contracts

    def initialize(self, eth):

        self.eth = eth

        if self.last_block:
            blockNum = self.last_block
            print("Resuming synchronization from block " + str(blockNum))
        else:

            blockNum = eth.eth_blockNumber()
            print("Starting synchronization from latest block: " + str(blockNum))

        processed = 0

        while (blockNum > 0):

            numbers = []

            for i in range(1, NUM_THREADS + 1):
                numbers.append(blockNum - (i * BLOCKS_PER_THREAD))

            pool = Pool(NUM_THREADS)
            results = pool.map(self.sync_blocks, numbers)
            pool.close()
            pool.join()

            for result in results:
                for (contract_hash, data) in result.items():

                    try:
                        self.contracts[contract_hash]
                    except KeyError:
                        self.contracts[contract_hash] = data['ethcontract']
                        m = InstanceList()
                        self.instance_lists[contract_hash] = m

                    self.instance_lists[contract_hash].add(data['address'], data['balance'])

            blockNum -= NUM_THREADS * BLOCKS_PER_THREAD
            processed += NUM_THREADS * BLOCKS_PER_THREAD
            self.last_block = blockNum
            transaction.commit()
            print("%d blocks processed, %d unique contracts in database, next block: %d" % (processed, len(self.contracts), blockNum))

        # If we've finished initializing the database, start over from the end of the chain if we want to initialize again
        self.last_block = 0

    def search(self, expression, callback_func):

        all_keys = list(self.contracts)

        for k in all_keys:

            if self.contracts[k].matches_expression(expression):

                m = self.instance_lists[k]

                callback_func(k.hex(), self.contracts[k], m.addresses, m.balances)
