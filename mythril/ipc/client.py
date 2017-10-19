import json
import warnings

from ethereum import utils
from ethereum.abi import encode_abi, decode_abi
from web3 import Web3, IPCProvider
#HTTPProvider, 

from .constants import BLOCK_TAGS, BLOCK_TAG_LATEST
from .utils import hex_to_dec, clean_hex, validate_block
from .exceptions import (ConnectionError, BadStatusCodeError,
                                   BadJsonError, BadResponseError)
IPC_PATH = None


'''
This code is adapted from: https://github.com/ConsenSys/ethjsonrpc
'''
class EthIpc(object):
    '''
    Ethereum IPC client class using web3.py
    '''
    web3 = Web3(IPCProvider())

    DEFAULT_GAS_PER_TX = 90000
    DEFAULT_GAS_PRICE = 50 * 10**9  # 50 gwei

    def __init__(self, ipc_path=IPC_PATH):
        #not used so far
        self.ipc_path = ipc_path

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
        http://web3py.readthedocs.io/en/latest/web3.version.html#web3.version.Version.node

        
        '''
        return self.web3.version.node

    def web3_sha3(self, data):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#web3_sha3
        http://web3py.readthedocs.io/en/latest/overview.html#Web3.sha3
        Encoding probably not necessary
        
        '''
        data = str(data).encode('hex')
        return self.web3.sha3(data)

    def net_version(self):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#net_version
        http://web3py.readthedocs.io/en/latest/web3.version.html#web3.version.Version.network

        
        '''
        return self.web3.version.network

    def net_listening(self):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#net_listening
        ONLY indirectly available
        TESTED
        '''
        return self.web3net.listening()

    def net_peerCount(self):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#net_peercount
        ONLY indirectly available
        TESTED
        '''
        return self.web3.net.peerCount()

    def eth_protocolVersion(self):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_protocolversion
        http://web3py.readthedocs.io/en/latest/web3.version.html?highlight=net#web3.version.Version.ethereum
        
        '''
        return self.web3.version.ethereum

    def eth_syncing(self):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_syncing

        http://web3py.readthedocs.io/en/latest/web3.eth.html?highlight=syncing#web3.eth.Eth.syncing
        '''
        return self.web3.eth.syncing

    def eth_coinbase(self):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_coinbase
        http://web3py.readthedocs.io/en/latest/web3.eth.html?highlight=syncing#web3.eth.Eth.coinbase

        '''
        return self.web3.eth.coinbase

    def eth_mining(self):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_mining
        http://web3py.readthedocs.io/en/latest/web3.eth.html?highlight=syncing#web3.eth.Eth.mining
        
        '''
        return self.web3.Eth.mining

    def eth_hashrate(self):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_hashrate
        http://web3py.readthedocs.io/en/latest/web3.eth.html?highlight=syncing#web3.eth.Eth.hashrate
        
        '''
        return hex_to_dec(web3.eth.hashrate)

    def eth_gasPrice(self):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_gasprice

        http://web3py.readthedocs.io/en/latest/web3.eth.html?highlight=gasprice#web3.eth.Eth.gasPrice
        '''
        return hex_to_dec(web3.eth.gasPrice)

    def eth_accounts(self):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_accounts
        http://web3py.readthedocs.io/en/latest/web3.eth.html?highlight=gasprice#web3.eth.Eth.accounts
        
        '''
        return self.web3.eth.accounts

    def eth_blockNumber(self):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_blocknumber
        http://web3py.readthedocs.io/en/latest/web3.eth.html?highlight=gasprice#web3.eth.Eth.blockNumber
        
        '''
        return hex_to_dec(self.web3.eth.blockNumber)

    def eth_getBalance(self, address=None, block=BLOCK_TAG_LATEST):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_getbalance
        http://web3py.readthedocs.io/en/latest/web3.eth.html?highlight=gasprice#web3.eth.Eth.getBalance
        
        '''
        address = address or self.eth_coinbase()
        block = validate_block(block)
        return self.web3.eth.getBalance(address, block_identifier=block)

    def eth_getStorageAt(self, address=None, position=0, block=BLOCK_TAG_LATEST):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_getstorageat
        http://web3py.readthedocs.io/en/latest/web3.eth.html?highlight=gasprice#web3.eth.Eth.getStorageAt
        
        '''
        block = validate_block(block)
        return self.web3.eth.getStorageAt(address, position, block_identifier=block)

    def eth_getTransactionCount(self, address, block=BLOCK_TAG_LATEST):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_gettransactioncount
        http://web3py.readthedocs.io/en/latest/web3.eth.html?highlight=gasprice#web3.eth.Eth.getTransactionCount
        
        '''
        block = validate_block(block)
        return self.web3.eth.getTransactionCount(address, block_identifier=block)

    def eth_getBlockTransactionCountByHash(self, block_hash):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_getblocktransactioncountbyhash
        http://web3py.readthedocs.io/en/latest/web3.eth.html?highlight=gasprice#web3.eth.Eth.getBlockTransactionCount
        
        '''
        return self.web3.eth.getBlockTransactionCount(block_hash)

    def eth_getBlockTransactionCountByNumber(self, block=BLOCK_TAG_LATEST):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_getblocktransactioncountbynumber
        http://web3py.readthedocs.io/en/latest/web3.eth.html?highlight=gasprice#web3.eth.Eth.getBlockTransactionCount
        
        '''
        block = validate_block(block)
        return self.web3.eth.getBlockTransactionCount(block)

    def eth_getUncleCountByBlockHash(self, block_hash):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_getunclecountbyblockhash
        http://web3py.readthedocs.io/en/latest/web3.eth.html?highlight=gasprice#web3.eth.Eth.getUncle
        
        '''
        return self.web3.eth.getUncleCount(block_hash)

    def eth_getUncleCountByBlockNumber(self, block=BLOCK_TAG_LATEST):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_getunclecountbyblocknumber
        http://web3py.readthedocs.io/en/latest/web3.eth.html?highlight=gasprice#web3.eth.Eth.getUncle
        
        '''
        block = validate_block(block)
        return self.web3.eth.getUncleCount(block)

    def eth_getCode(self, address, default_block=BLOCK_TAG_LATEST):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_getcode
        http://web3py.readthedocs.io/en/latest/web3.eth.html?highlight=gasprice#web3.eth.Eth.getCode
        NEEDS TESTING
        '''
        if isinstance(default_block, str):
            if default_block not in BLOCK_TAGS:
                raise ValueError
        return self.web3.eth.getCode(address, block_identifier=default_block)

    def eth_sign(self, address, data):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_sign
        http://web3py.readthedocs.io/en/latest/web3.eth.html?highlight=gasprice#web3.eth.Eth.sign
        either data= hexstr= or text= probably not needed now but if used should be differentiated
        NEEDS TESTING
        '''
        return self.web3.eth.sign(address, data)

    def eth_sendTransaction(self, to_address=None, from_address=None, gas=None, gas_price=None, value=None, data=None,
                            nonce=None):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_sendtransaction
        http://web3py.readthedocs.io/en/latest/web3.eth.html?highlight=syncing#web3.eth.Eth.sendTransaction
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
        return self.web3.eth.sendTransaction(params)

    def eth_sendRawTransaction(self, data):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_sendrawtransaction
        http://web3py.readthedocs.io/en/latest/web3.eth.html?highlight=syncing#web3.eth.Eth.sendRawTransaction
        NEEDS TESTING
        '''
        return self.web3.eth.sendRawTransaction(data)

    def eth_call(self, to_address, from_address=None, gas=None, gas_price=None, value=None, data=None,
                 default_block=BLOCK_TAG_LATEST):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_call
        http://web3py.readthedocs.io/en/latest/web3.eth.html?highlight=syncing#web3.eth.Eth.call

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
        return self.web3.eth.call(obj, block_identifier=default_block)

    def eth_estimateGas(self, to_address=None, from_address=None, gas=None, gas_price=None, value=None, data=None,
                        default_block=BLOCK_TAG_LATEST):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_estimategas
        http://web3py.readthedocs.io/en/latest/web3.eth.html?highlight=gasprice#web3.eth.Eth.estimateGas
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
        return self.web3.eth.estimateGas(obj)

    def eth_getBlockByHash(self, block_hash, tx_objects=True):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_getblockbyhash
        http://web3py.readthedocs.io/en/latest/web3.eth.html?highlight=gasprice#web3.eth.Eth.getBlock
        TESTED
        '''
        return self.web3.eth.getBlock(block_identifier=block_hash, full_transactions=tx_objects)

    def eth_getBlockByNumber(self, block=BLOCK_TAG_LATEST, tx_objects=True):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_getblockbynumber
        http://web3py.readthedocs.io/en/latest/web3.eth.html?highlight=gasprice#web3.eth.Eth.getBlock
        TESTED
        '''
        block = validate_block(block)
        return self.web3.eth.getBlock(block_identifier=block, full_transactions=tx_objects)

    def eth_getTransactionByHash(self, tx_hash):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_gettransactionbyhash
        http://web3py.readthedocs.io/en/latest/web3.eth.html?highlight=gasprice#web3.eth.Eth.getTransaction
        TESTED
        '''
        return self.web3.eth.getTransactionByHash(tx_hash)

    def eth_getTransactionByBlockHashAndIndex(self, block_hash, index=0):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_gettransactionbyblockhashandindex
        http://web3py.readthedocs.io/en/latest/web3.eth.html#web3.eth.Eth.getTransactionFromBlock
        TESTED
        '''
        return self.web3.eth.getTransactionFromBlock(block_identifier=block_hash, transaction_index=index)

    def eth_getTransactionByBlockNumberAndIndex(self, block=BLOCK_TAG_LATEST, index=0):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_gettransactionbyblocknumberandindex
        http://web3py.readthedocs.io/en/latest/web3.eth.html#web3.eth.Eth.getTransactionFromBlock

        TESTED
        '''
        block = validate_block(block)
        return self.web3.eth.getTransactionFromBlock(block_identifier=block, transaction_index=index)

    def eth_getTransactionReceipt(self, tx_hash):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_gettransactionreceipt
        http://web3py.readthedocs.io/en/latest/web3.eth.html?highlight=gasprice#web3.eth.Eth.getTransactionReceipt
        TESTED
        '''
        return self.web3.eth.getTransactionReceipt(tx_hash)

    def eth_getUncleByBlockHashAndIndex(self, block_hash, index=0):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_getunclebyblockhashandindex
        NOT IMPLEMENTED
        TESTED
        '''
        return "Not implemented"

    def eth_getUncleByBlockNumberAndIndex(self, block=BLOCK_TAG_LATEST, index=0):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_getunclebyblocknumberandindex
        NOT IMPLEMENTED
        TESTED
        '''
        block = validate_block(block)
        return "Not implemented"

    def eth_getCompilers(self):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_getcompilers
        Does not seem to be implemented
        TESTED
        '''
        return "Not implemented"

    def eth_compileSolidity(self, code):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_compilesolidity
        Implemented?
        TESTED
        '''
        return self.web3.eth.compileSolidity(code)

    def eth_compileLLL(self, code):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_compilelll
        Implemented?
        N/A
        '''
        return self.web3.eth.compileLLL(code)

    def eth_compileSerpent(self, code):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_compileserpent
        Implemented?
        N/A
        '''
        return self.web3.eth.compileSerpent(code)

    def eth_newFilter(self, from_block=BLOCK_TAG_LATEST, to_block=BLOCK_TAG_LATEST, address=None, topics=None):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_newfilter
        http://web3py.readthedocs.io/en/latest/web3.eth.html#web3.eth.Eth.filter
        NEEDS TESTING
        '''
        filter_params = {
            'fromBlock': from_block,
            'toBlock':   to_block,
            'address':   address,
            'topics':    topics,
        }
        return self.web3.eth.newFilter(filter_params)

    def eth_newBlockFilter(self):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_newblockfilter
        http://web3py.readthedocs.io/en/latest/web3.eth.html#web3.eth.Eth.filter
        TESTED
        '''
        return self.web3.eth.newFilter('latest')

    def eth_newPendingTransactionFilter(self):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_newpendingtransactionfilter
        http://web3py.readthedocs.io/en/latest/web3.eth.html#web3.eth.Eth.filter
        TESTED
        '''
        return self.web3.eth.newFilter('pending')

    def eth_uninstallFilter(self, filter_id):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_uninstallfilter
        http://web3py.readthedocs.io/en/latest/web3.eth.html#web3.eth.Eth.uninstallFilter
        NEEDS TESTING
        '''
        return self.web3.eth.uninstallFilter(filter_id)

    def eth_getFilterChanges(self, filter_id):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_getfilterchanges
        http://web3py.readthedocs.io/en/latest/web3.eth.html#web3.eth.Eth.getFilterChanges
        NEEDS TESTING
        '''
        return self.web3.eth.getFilterChanges(filter_id)

    def eth_getFilterLogs(self, filter_id):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_getfilterlogs
        http://web3py.readthedocs.io/en/latest/web3.eth.html#web3.eth.Eth.getFilterLogs
        NEEDS TESTING
        '''
        return self.web3.eth.getFilterLogs(filter_id)

    def eth_getLogs(self, filter_object):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_getlogs
        http://web3py.readthedocs.io/en/latest/filters.html?highlight=getLogs#web3.utils.filters.LogFilter.get
        NEEDS TESTING
        '''
        return self.filter_object.get()

    def eth_getWork(self):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_getwork
        http://web3py.readthedocs.io/en/latest/releases.html?highlight=getWork#id15
        TESTED
        '''
        return self.web3.eth.getWork()

    def eth_submitWork(self, nonce, header, mix_digest):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_submitwork
        Not sure if implemented
        NEEDS TESTING
        '''
        return self.web3.eth.submitWork(nonce, header, mix_digest)

    def eth_submitHashrate(self, hash_rate, client_id):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_submithashrate
        Not sure if implemented
        TESTED
        '''
        return self.web3.eth.submitHashrate(hash_rate, client_id)

    def db_putString(self, db_name, key, value):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#db_putstring
        Not implemented I think
        TESTED
        '''
        warnings.warn('deprecated', DeprecationWarning)
        return self.web3.db.putString(db_name, key, value)

    def db_getString(self, db_name, key):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#db_getstring
        Not implemented I think
        TESTED
        '''
        warnings.warn('deprecated', DeprecationWarning)
        return self.web3.db.getString(db_name, key)

    def db_putHex(self, db_name, key, value):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#db_puthex

        TESTED
        '''
        if not value.startswith('0x'):
            value = '0x{}'.format(value)
        warnings.warn('deprecated', DeprecationWarning)
        return self.web3.db.putHex(db_name, key, value)

    def db_getHex(self, db_name, key):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#db_gethex

        TESTED
        '''
        warnings.warn('deprecated', DeprecationWarning)
        return self.web3.db.getHex(db_name, key)

    def shh_version(self):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#shh_version
        http://web3py.readthedocs.io/en/latest/web3.shh.html#web3.shh.Shh.version
        N/A
        '''
        return self.web3.shh.version()

    def shh_post(self, topics, payload, priority, ttl, from_=None, to=None):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#shh_post

        NEEDS TESTING
        '''
        whisper_object = {
            'from':     from_,
            'to':       to,
            'topics':   topics,
            'payload':  payload,
            'priority': hex(priority),
            'ttl':      hex(ttl),
        }
        return self._call('shh_post', [whisper_object])

    def shh_newIdentity(self):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#shh_newidentity

        N/A
        '''
        return self._call('shh_newIdentity')

    def shh_hasIdentity(self, address):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#shh_hasidentity

        NEEDS TESTING
        '''
        return self._call('shh_hasIdentity', [address])

    def shh_newGroup(self):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#shh_newgroup

        N/A
        '''
        return self._call('shh_newGroup')

    def shh_addToGroup(self):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#shh_addtogroup

        NEEDS TESTING
        '''
        return self._call('shh_addToGroup')

    def shh_newFilter(self, to, topics):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#shh_newfilter

        NEEDS TESTING
        '''
        _filter = {
            'to':     to,
            'topics': topics,
        }
        return self._call('shh_newFilter', [_filter])

    def shh_uninstallFilter(self, filter_id):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#shh_uninstallfilter

        NEEDS TESTING
        '''
        return self._call('shh_uninstallFilter', [filter_id])

    def shh_getFilterChanges(self, filter_id):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#shh_getfilterchanges
        http://web3py.readthedocs.io/en/latest/web3.eth.html?highlight=syncing#web3.eth.Eth.getFilterChanges
        NEEDS TESTING
        '''
        filt = self.web3.eth.filter()
        return self._call('shh_getFilterChanges', [filter_id])

    def shh_getMessages(self, filter_id):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#shh_getmessages

        NEEDS TESTING
        '''
        return self._call('shh_getMessages', [filter_id])

    def getBlockRlp(self, number=0):

        return self._call('debug_getBlockRlp', [number])

    def traceTransaction(self, txHash):
        #atm not directly accessible, so something like this is needed
        #https://github.com/pipermerriam/web3.py/issues/308
        #web3.manager.request_blocking('debug_traceTransaction', ["TX_ID_AS_HEX_STRING"])
        return self.web3.manager.request_blocking('debug_traceTransaction', [txHash])

