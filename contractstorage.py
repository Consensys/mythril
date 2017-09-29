from rpc.client import EthJsonRpc
from ethcontract import ETHCode, AddressesByCodeHash, CodeHashByAddress
from ether import util
from ethereum import utils
import codecs
import hashlib
import re
import ZODB
import persistent
import persistent.list
import transaction
from BTrees.OOBTree import BTree


class ContractStorage(persistent.Persistent):

    def __init__(self):
        self.contracts = BTree()
        self.address_to_hash_map = BTree()
        self.hash_to_addresses_map = BTree()
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
                print("Processing block: " + str(blockNum))

            block = eth.eth_getBlockByNumber(blockNum)

            for tx in block['transactions']:

                if not tx['to']:

                    receipt = eth.eth_getTransactionReceipt(tx['hash'])

                    contract_address = receipt['contractAddress']

                    contract_code = eth.eth_getCode(contract_address)
                    contract_balance = eth.eth_getBalance(contract_address)

                    code = ETHCode(contract_code)

                    m = hashlib.md5()
                    m.update(contract_code.encode('UTF-8'))
                    contract_hash = m.digest()

                    try:
                        self.contracts[contract_hash]
                    except KeyError:
                        self.contracts[contract_hash] = code

                    m = CodeHashByAddress(contract_hash, contract_balance)
                    self.address_to_hash_map[contract_address] = m

                    m = AddressesByCodeHash(contract_address, contract_balance)
                    self.hash_to_addresses_map[contract_hash] = m

                    transaction.commit()

            self.last_block = blockNum
            blockNum -= 1



    def get_all(self):
        return self.contracts

    def get_contract_code_by_address(self, address):

        pass


    def search(self, expression, callback_func):

        matches = re.findall(r'func\[([a-zA-Z0-9\s,()]+)\]', expression)

        for m in matches:
            # Pre-calculate function signature hashes

            sign_hash = utils.sha3(m)[:4].hex()

            expression = expression.replace(m, sign_hash)

        for c in self.contracts:

            for instance in c['instances']:

                contract = ETHContract(c['code'], instance['balance'])

                if (contract.matches_expression(expression)):
                    callback_func(instance['address'])

