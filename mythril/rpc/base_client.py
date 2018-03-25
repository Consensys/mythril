from abc import (abstractmethod)

from ethereum.abi import encode_abi, decode_abi
from ethereum import utils

from .constants import BLOCK_TAGS, BLOCK_TAG_LATEST
from .utils import hex_to_dec, clean_hex, validate_block

GETH_DEFAULT_RPC_PORT = 8545
ETH_DEFAULT_RPC_PORT = 8545
PARITY_DEFAULT_RPC_PORT = 8545
PYETHAPP_DEFAULT_RPC_PORT = 4000
MAX_RETRIES = 3
JSON_MEDIA_TYPE = 'application/json'

'''
This code is adapted from: https://github.com/ConsenSys/ethjsonrpc
'''
class BaseClient(object):

    @abstractmethod
    def _call(self, method, params=None, _id=1):
        pass

    def _encode_function(self, signature, param_values):

        prefix = utils.big_endian_to_int(utils.sha3(signature)[:4])

        if signature.find('(') == -1:
            raise RuntimeError('Invalid function signature. Missing "(" and/or ")"...')

        if signature.find(')') - signature.find('(') == 1:
            return utils.encode_int(prefix)

        types = signature[signature.find('(') + 1: signature.find(')')].split(',')
        encoded_params = encode_abi(types, param_values)
        return utils.zpad(utils.encode_int(prefix), 4) + encoded_params

################################################################################
# high-level methods
################################################################################

    def transfer(self, from_, to, amount):
        '''
        Send wei from one address to another
        '''
        return self.eth_sendTransaction(from_address=from_, to_address=to, value=amount)

    def create_contract(self, from_, code, gas, sig=None, args=None):
        '''
        Create a contract on the blockchain from compiled EVM code. Returns the
        transaction hash.
        '''
        from_ = from_ or self.eth_coinbase()
        if sig is not None and args is not None:
             types = sig[sig.find('(') + 1: sig.find(')')].split(',')
             encoded_params = encode_abi(types, args)
             code += encoded_params.hex()

        return self.eth_sendTransaction(from_address=from_, gas=gas, data=code)

    def get_contract_address(self, tx):
        '''
        Get the address for a contract from the transaction that created it
        '''
        receipt = self.eth_getTransactionReceipt(tx)
        return receipt['contractAddress']

    def call(self, address, sig, args, result_types):
        '''
        Call a contract function on the RPC server, without sending a
        transaction (useful for reading data)
        '''
        data = self._encode_function(sig, args)
        data_hex = data.encode('hex')
        response = self.eth_call(to_address=address, data=data_hex)
        return decode_abi(result_types, response[2:].decode('hex'))

    def call_with_transaction(self, from_, address, sig, args, gas=None, gas_price=None, value=None):
        '''
        Call a contract function by sending a transaction (useful for storing
        data)
        '''
        gas = gas or self.DEFAULT_GAS_PER_TX
        gas_price = gas_price or self.DEFAULT_GAS_PRICE
        data = self._encode_function(sig, args)
        data_hex = data.encode('hex')
        return self.eth_sendTransaction(from_address=from_, to_address=address, data=data_hex, gas=gas,
                                        gas_price=gas_price, value=value)

################################################################################
# JSON-RPC methods
################################################################################

    def web3_clientVersion(self):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#web3_clientversion

        TESTED
        '''
        return self._call('web3_clientVersion')

    def web3_sha3(self, data):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#web3_sha3

        TESTED
        '''
        data = str(data).encode('hex')
        return self._call('web3_sha3', [data])

    def net_version(self):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#net_version

        TESTED
        '''
        return self._call('net_version')

    def net_listening(self):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#net_listening

        TESTED
        '''
        return self._call('net_listening')

    def net_peerCount(self):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#net_peercount

        TESTED
        '''
        return hex_to_dec(self._call('net_peerCount'))

    def eth_protocolVersion(self):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_protocolversion

        TESTED
        '''
        return self._call('eth_protocolVersion')

    def eth_syncing(self):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_syncing

        TESTED
        '''
        return self._call('eth_syncing')

    def eth_coinbase(self):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_coinbase

        TESTED
        '''
        return self._call('eth_coinbase')

    def eth_mining(self):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_mining

        TESTED
        '''
        return self._call('eth_mining')

    def eth_hashrate(self):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_hashrate

        TESTED
        '''
        return hex_to_dec(self._call('eth_hashrate'))

    def eth_gasPrice(self):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_gasprice

        TESTED
        '''
        return hex_to_dec(self._call('eth_gasPrice'))

    def eth_accounts(self):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_accounts

        TESTED
        '''
        return self._call('eth_accounts')

    def eth_blockNumber(self):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_blocknumber

        TESTED
        '''
        return hex_to_dec(self._call('eth_blockNumber'))

    def eth_getBalance(self, address=None, block=BLOCK_TAG_LATEST):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_getbalance

        TESTED
        '''
        address = address or self.eth_coinbase()
        block = validate_block(block)
        return hex_to_dec(self._call('eth_getBalance', [address, block]))

    def eth_getStorageAt(self, address=None, position=0, block=BLOCK_TAG_LATEST):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_getstorageat

        TESTED
        '''
        block = validate_block(block)
        return self._call('eth_getStorageAt', [address, hex(position), block])

    def eth_getTransactionCount(self, address, block=BLOCK_TAG_LATEST):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_gettransactioncount

        TESTED
        '''
        block = validate_block(block)
        return hex_to_dec(self._call('eth_getTransactionCount', [address, block]))

    def eth_getBlockTransactionCountByHash(self, block_hash):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_getblocktransactioncountbyhash

        TESTED
        '''
        return hex_to_dec(self._call('eth_getBlockTransactionCountByHash', [block_hash]))

    def eth_getBlockTransactionCountByNumber(self, block=BLOCK_TAG_LATEST):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_getblocktransactioncountbynumber

        TESTED
        '''
        block = validate_block(block)
        return hex_to_dec(self._call('eth_getBlockTransactionCountByNumber', [block]))

    def eth_getUncleCountByBlockHash(self, block_hash):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_getunclecountbyblockhash

        TESTED
        '''
        return hex_to_dec(self._call('eth_getUncleCountByBlockHash', [block_hash]))

    def eth_getUncleCountByBlockNumber(self, block=BLOCK_TAG_LATEST):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_getunclecountbyblocknumber

        TESTED
        '''
        block = validate_block(block)
        return hex_to_dec(self._call('eth_getUncleCountByBlockNumber', [block]))

    def eth_getCode(self, address, default_block=BLOCK_TAG_LATEST):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_getcode

        NEEDS TESTING
        '''
        if isinstance(default_block, str):
            if default_block not in BLOCK_TAGS:
                raise ValueError
        return self._call('eth_getCode', [address, default_block])

    def eth_sign(self, address, data):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_sign

        NEEDS TESTING
        '''
        return self._call('eth_sign', [address, data])

    def eth_sendTransaction(self, to_address=None, from_address=None, gas=None, gas_price=None, value=None, data=None,
                            nonce=None):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_sendtransaction

        NEEDS TESTING
        '''
        params = {}
        params['from'] = from_address or self.eth_coinbase()
        if to_address is not None:
            params['to'] = to_address
        if gas is not None:
            params['gas'] = hex(gas)
        if gas_price is not None:
            params['gasPrice'] = clean_hex(gas_price)
        if value is not None:
            params['value'] = clean_hex(value)
        if data is not None:
            params['data'] = data
        if nonce is not None:
            params['nonce'] = hex(nonce)
        return self._call('eth_sendTransaction', [params])

    def eth_sendRawTransaction(self, data):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_sendrawtransaction

        NEEDS TESTING
        '''
        return self._call('eth_sendRawTransaction', [data])

    def eth_call(self, to_address, from_address=None, gas=None, gas_price=None, value=None, data=None,
                 default_block=BLOCK_TAG_LATEST):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_call

        NEEDS TESTING
        '''
        if isinstance(default_block, str):
            if default_block not in BLOCK_TAGS:
                raise ValueError
        obj = {}
        obj['to'] = to_address
        if from_address is not None:
            obj['from'] = from_address
        if gas is not None:
            obj['gas'] = hex(gas)
        if gas_price is not None:
            obj['gasPrice'] = clean_hex(gas_price)
        if value is not None:
            obj['value'] = value
        if data is not None:
            obj['data'] = data
        return self._call('eth_call', [obj, default_block])

    def eth_estimateGas(self, to_address=None, from_address=None, gas=None, gas_price=None, value=None, data=None,
                        default_block=BLOCK_TAG_LATEST):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_estimategas

        NEEDS TESTING
        '''
        if isinstance(default_block, str):
            if default_block not in BLOCK_TAGS:
                raise ValueError
        obj = {}
        if to_address is not None:
            obj['to'] = to_address
        if from_address is not None:
            obj['from'] = from_address
        if gas is not None:
            obj['gas'] = hex(gas)
        if gas_price is not None:
            obj['gasPrice'] = clean_hex(gas_price)
        if value is not None:
            obj['value'] = value
        if data is not None:
            obj['data'] = data
        return hex_to_dec(self._call('eth_estimateGas', [obj, default_block]))

    def eth_getBlockByHash(self, block_hash, tx_objects=True):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_getblockbyhash

        TESTED
        '''
        return self._call('eth_getBlockByHash', [block_hash, tx_objects])

    def eth_getBlockByNumber(self, block=BLOCK_TAG_LATEST, tx_objects=True):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_getblockbynumber

        TESTED
        '''
        block = validate_block(block)
        return self._call('eth_getBlockByNumber', [block, tx_objects])

    def eth_getTransactionByHash(self, tx_hash):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_gettransactionbyhash

        TESTED
        '''
        return self._call('eth_getTransactionByHash', [tx_hash])

    def eth_getTransactionByBlockHashAndIndex(self, block_hash, index=0):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_gettransactionbyblockhashandindex

        TESTED
        '''
        return self._call('eth_getTransactionByBlockHashAndIndex', [block_hash, hex(index)])

    def eth_getTransactionByBlockNumberAndIndex(self, block=BLOCK_TAG_LATEST, index=0):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_gettransactionbyblocknumberandindex

        TESTED
        '''
        block = validate_block(block)
        return self._call('eth_getTransactionByBlockNumberAndIndex', [block, hex(index)])

    def eth_getTransactionReceipt(self, tx_hash):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_gettransactionreceipt

        TESTED
        '''
        return self._call('eth_getTransactionReceipt', [tx_hash])

    def eth_getUncleByBlockHashAndIndex(self, block_hash, index=0):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_getunclebyblockhashandindex

        TESTED
        '''
        return self._call('eth_getUncleByBlockHashAndIndex', [block_hash, hex(index)])

    def eth_getUncleByBlockNumberAndIndex(self, block=BLOCK_TAG_LATEST, index=0):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_getunclebyblocknumberandindex

        TESTED
        '''
        block = validate_block(block)
        return self._call('eth_getUncleByBlockNumberAndIndex', [block, hex(index)])

    def eth_newFilter(self, from_block=BLOCK_TAG_LATEST, to_block=BLOCK_TAG_LATEST, address=None, topics=None):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_newfilter

        NEEDS TESTING
        '''
        _filter = {
            'fromBlock': from_block,
            'toBlock':   to_block,
            'address':   address,
            'topics':    topics,
        }
        return self._call('eth_newFilter', [_filter])

    def eth_newBlockFilter(self):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_newblockfilter

        TESTED
        '''
        return self._call('eth_newBlockFilter')

    def eth_newPendingTransactionFilter(self):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_newpendingtransactionfilter

        TESTED
        '''
        return hex_to_dec(self._call('eth_newPendingTransactionFilter'))

    def eth_uninstallFilter(self, filter_id):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_uninstallfilter

        NEEDS TESTING
        '''
        return self._call('eth_uninstallFilter', [filter_id])

    def eth_getFilterChanges(self, filter_id):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_getfilterchanges

        NEEDS TESTING
        '''
        return self._call('eth_getFilterChanges', [filter_id])

    def eth_getFilterLogs(self, filter_id):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_getfilterlogs

        NEEDS TESTING
        '''
        return self._call('eth_getFilterLogs', [filter_id])

    def eth_getLogs(self, filter_object):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_getlogs

        NEEDS TESTING
        '''
        return self._call('eth_getLogs', [filter_object])

    def eth_getWork(self):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_getwork

        TESTED
        '''
        return self._call('eth_getWork')

    def eth_submitWork(self, nonce, header, mix_digest):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_submitwork

        NEEDS TESTING
        '''
        return self._call('eth_submitWork', [nonce, header, mix_digest])

    def eth_submitHashrate(self, hash_rate, client_id):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_submithashrate

        TESTED
        '''
        return self._call('eth_submitHashrate', [hex(hash_rate), client_id])

    def shh_version(self):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#shh_version

        N/A
        '''
        return self._call('shh_version')

    def getBlockRlp(self, number=0):

        return self._call('debug_getBlockRlp', [number])

    def traceTransaction(self, txHash):

        return self._call('debug_traceTransaction', [txHash])
