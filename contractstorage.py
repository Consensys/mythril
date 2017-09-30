from rpc.client import EthJsonRpc
from ether.ethcontract import ETHCode, InstanceList
from ethereum import utils
import hashlib
import re
import persistent
import persistent.list
import transaction
from BTrees.OOBTree import BTree


class ContractStorage(persistent.Persistent):

    def __init__(self):
        self.contracts = BTree()
        self.instance_lists= BTree()
        self.last_block = 0

    def initialize(self, rpchost, rpcport):

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

                    if not contract_balance:
                        # skip contracts with zero balance.
                        continue

                    code = ETHCode(contract_code)

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

        matches = re.findall(r'func\[([a-zA-Z0-9\s,()]+)\]', expression)

        for m in matches:
            # Pre-calculate function signature hashes

            sign_hash = utils.sha3(m)[:4].hex()

            expression = expression.replace(m, sign_hash)

        all_keys = list(self.contracts)

        for k in all_keys:

            if self.contracts[k].matches_expression(expression):

                m = hashlib.md5()
                m.update(self.contracts[k].code.encode('UTF-8'))
                contract_hash = m.digest()

                m = self.instance_lists[contract_hash]

                callback_func(self.contracts[k].code, m.addresses)
