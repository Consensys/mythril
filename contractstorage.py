from rpc.client import EthJsonRpc
from ethcontract import ETHContract
from tinydb import TinyDB, Query
import codecs
import hashlib


class ContractStorage:

    def __init__(self):
        self.db = TinyDB('./contracts.json')


    def initialize(self, rpchost, rpcport):

        eth = EthJsonRpc(rpchost, rpcport)

        blockNum = eth.eth_blockNumber()

        while(blockNum > 0):

            if not blockNum % 1000:
                print("Processing block: " + str(blockNum))

            block = eth.eth_getBlockByNumber(blockNum)

            for tx in block['transactions']:

                if not tx['to']:

                    receipt = eth.eth_getTransactionReceipt(tx['hash'])

                    contract_address = receipt['contractAddress']

                    contract_code = eth.eth_getCode(contract_address)

                    m = hashlib.md5()

                    m.update(contract_code.encode('UTF-8'))

                    contract_hash = codecs.encode(m.digest(), 'hex_codec')
                    contract_id = contract_hash.decode("utf-8")

                    contract_balance = eth.eth_getBalance(contract_address)

                    Contract = Query()

                    new_instance = {'address': contract_address, 'balance': contract_balance}

                    s = self.db.search(Contract.id == contract_id)

                    if not len(s):

                        self.db.insert({'id': contract_id, 'code': contract_code, 'instances': [new_instance]})

                    else:

                        instances = s[0]['instances']

                        instances.append(new_instance)

                        self.db.update({'instances': instances}, Contract.id == contract_id)

            blockNum -= 1



    def search(self, expression):

        all_contracts = self.db.all()

        for c in all_contracts:

            for instance in c['instances']:

                if ('balance' in instance):
                    contract = ETHContract(c['code'], instance['balance'])

                    if (contract.matches_expression(expression)):
                        print("Found contract:" + instance['address'])

