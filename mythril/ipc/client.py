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
        Call a contract function on the IPC server, without sending a
        transaction (useful for reading data)
        '''
        data = self._encode_function(sig, args)
        data_hex = data.encode('hex')
        # could be made to use web3py directly, but instead uses eth_call which is adapted
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
        Only indirectly available
        
        '''
        return self.web3net.listening()

    def net_peerCount(self):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#net_peercount
        ONLY indirectly available
        
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
        return web3.eth.hashrate

    def eth_gasPrice(self):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_gasprice

        http://web3py.readthedocs.io/en/latest/web3.eth.html?highlight=gasprice#web3.eth.Eth.gasPrice
        '''
        return web3.eth.gasPrice

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
        return self.web3.eth.blockNumber

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
        (not implemented with convenience functions)
        '''
        return self.web3.manager.request_blocking('eth_getUncleCountByBlockHash', [block_hash])
        return self.web3.eth.getUncleCount(block_hash)

    def eth_getUncleCountByBlockNumber(self, block=BLOCK_TAG_LATEST):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_getunclecountbyblocknumber
        http://web3py.readthedocs.io/en/latest/web3.eth.html?highlight=gasprice#web3.eth.Eth.getUncle
        
        '''
        block = validate_block(block)
        self.web3.manager.request_blocking('debug_getBlockRlp', [number])
        return self.web3.eth.getUncleCount(block)

    def eth_getCode(self, address, default_block=BLOCK_TAG_LATEST):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_getcode
        http://web3py.readthedocs.io/en/latest/web3.eth.html?highlight=gasprice#web3.eth.Eth.getCode
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
        '''
        return self.web3.eth.sign(address, data)

    def eth_sendTransaction(self, to_address=None, from_address=None, gas=None, gas_price=None, value=None, data=None,
                            nonce=None):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_sendtransaction
        http://web3py.readthedocs.io/en/latest/web3.eth.html?highlight=syncing#web3.eth.Eth.sendTransaction
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
        '''
        return self.web3.eth.sendRawTransaction(data)

    def eth_call(self, to_address, from_address=None, gas=None, gas_price=None, value=None, data=None,
                 default_block=BLOCK_TAG_LATEST):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_call
        http://web3py.readthedocs.io/en/latest/web3.eth.html?highlight=syncing#web3.eth.Eth.call

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
        '''
        return self.web3.eth.getBlock(block_identifier=block_hash, full_transactions=tx_objects)

    def eth_getBlockByNumber(self, block=BLOCK_TAG_LATEST, tx_objects=True):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_getblockbynumber
        http://web3py.readthedocs.io/en/latest/web3.eth.html?highlight=gasprice#web3.eth.Eth.getBlock
        '''
        block = validate_block(block)
        return self.web3.eth.getBlock(block_identifier=block, full_transactions=tx_objects)

    def eth_getTransactionByHash(self, tx_hash):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_gettransactionbyhash
        http://web3py.readthedocs.io/en/latest/web3.eth.html?highlight=gasprice#web3.eth.Eth.getTransaction
        '''
        return self.web3.eth.getTransactionByHash(tx_hash)

    def eth_getTransactionByBlockHashAndIndex(self, block_hash, index=0):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_gettransactionbyblockhashandindex
        http://web3py.readthedocs.io/en/latest/web3.eth.html#web3.eth.Eth.getTransactionFromBlock
        '''
        return self.web3.eth.getTransactionFromBlock(block_identifier=block_hash, transaction_index=index)

    def eth_getTransactionByBlockNumberAndIndex(self, block=BLOCK_TAG_LATEST, index=0):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_gettransactionbyblocknumberandindex
        http://web3py.readthedocs.io/en/latest/web3.eth.html#web3.eth.Eth.getTransactionFromBlock

        '''
        block = validate_block(block)
        return self.web3.eth.getTransactionFromBlock(block_identifier=block, transaction_index=index)

    def eth_getTransactionReceipt(self, tx_hash):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_gettransactionreceipt
        http://web3py.readthedocs.io/en/latest/web3.eth.html?highlight=gasprice#web3.eth.Eth.getTransactionReceipt
        '''
        return self.web3.eth.getTransactionReceipt(tx_hash)

    def eth_getUncleByBlockHashAndIndex(self, block_hash, index=0):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_getunclebyblockhashandindex
        Indirectly accessible
        self.web3.manager.request_blocking('rpc/ipc function', [params])
        
        '''
        return self.web3.manager.request_blocking('eth_getUncleByBlockHashAndIndex', [block_hash, web3.toHex(index)])

    def eth_getUncleByBlockNumberAndIndex(self, block=BLOCK_TAG_LATEST, index=0):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_getunclebyblocknumberandindex
        Indirectly accessible
        '''
        block = validate_block(block)
        return self.web3.manager.request_blocking('eth_getUncleByBlockNumberAndIndex', [block, web3.toHex(index)])

    def eth_getCompilers(self):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_getcompilers
        Indirectly implemented
        '''
        return self.web3.manager.request_blocking('eth_getCompilers')

    def eth_compileSolidity(self, code):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_compilesolidity
        Indirectly implemented
        '''
        return self.web3.manager.request_blocking('eth_compileSolidity', [code])


    def eth_compileLLL(self, code):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_compilelll
        Indirectly accessible
        '''
        return self.web3.manager.request_blocking('eth_compileLLL', [code])

    def eth_compileSerpent(self, code):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_compileserpent
        Indirectly implemented
        '''
        return self.web3.manager.request_blocking('eth_compileSerpent', [code])


    def eth_newFilter(self, from_block=BLOCK_TAG_LATEST, to_block=BLOCK_TAG_LATEST, address=None, topics=None):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_newfilter
        http://web3py.readthedocs.io/en/latest/web3.eth.html#web3.eth.Eth.filter
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
        '''
        return self.web3.eth.newFilter('latest')

    def eth_newPendingTransactionFilter(self):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_newpendingtransactionfilter
        http://web3py.readthedocs.io/en/latest/web3.eth.html#web3.eth.Eth.filter
        '''
        return self.web3.eth.newFilter('pending')

    def eth_uninstallFilter(self, filter_id):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_uninstallfilter
        http://web3py.readthedocs.io/en/latest/web3.eth.html#web3.eth.Eth.uninstallFilter
        '''
        return self.web3.eth.uninstallFilter(filter_id)

    def eth_getFilterChanges(self, filter_id):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_getfilterchanges
        http://web3py.readthedocs.io/en/latest/web3.eth.html#web3.eth.Eth.getFilterChanges
        '''
        return self.web3.eth.getFilterChanges(filter_id)

    def eth_getFilterLogs(self, filter_id):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_getfilterlogs
        http://web3py.readthedocs.io/en/latest/web3.eth.html#web3.eth.Eth.getFilterLogs
        '''
        return self.web3.eth.getFilterLogs(filter_id)

    def eth_getLogs(self, filter_object):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_getlogs
        http://web3py.readthedocs.io/en/latest/filters.html?highlight=getLogs#web3.utils.filters.LogFilter.get
        '''
        return self.filter_object.get()

    def eth_getWork(self):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_getwork
        http://web3py.readthedocs.io/en/latest/releases.html?highlight=getWork#id15
        '''
        return self.web3.eth.getWork()

    def eth_submitWork(self, nonce, header, mix_digest):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_submitwork
        Implemented indirectly
        '''
        return self.web3.manager.request_blocking('eth_submitWork', [nonce, header, mix_digest])

    def eth_submitHashrate(self, hash_rate, client_id):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_submithashrate
        Implemented indirectly
        '''
        return self.web3.manager.request_blocking('eth_submitHashrate', [hash_rate, client_id])

    def shh_version(self):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#shh_version
        http://web3py.readthedocs.io/en/latest/web3.shh.html#web3.shh.Shh.version
        '''
        return self.web3.shh.version()

    def shh_post(self, topics, payload, priority, ttl, from_=None, to=None):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#shh_post
        http://web3py.readthedocs.io/en/latest/web3.shh.html#web3.shh.Shh.post
        # only topics and payload are necessary according to web3.py
        '''
        whisper_object = {
            'from':     from_,
            'to':       to,
            'topics':   web3.toHex(topics),
            'payload':  web3.toHex(payload),
            'priority': web3.toHex(priority),
            'ttl':      web3.toHex(ttl)
        }
        return self.web3.shh.post(whisper_object)

    def shh_newIdentity(self):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#shh_newidentity
        http://web3py.readthedocs.io/en/latest/web3.shh.html#web3.shh.Shh.newIdentity
        '''
        return self.web3.shh.newIdentity()

    def shh_hasIdentity(self, address):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#shh_hasidentity
        http://web3py.readthedocs.io/en/latest/web3.shh.html#web3.shh.Shh.hasIdentity
        '''
        return self.web3.shh.hasIdentity(address)

    def shh_newGroup(self):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#shh_newgroup
        http://web3py.readthedocs.io/en/latest/web3.shh.html#web3.shh.Shh.newGroup
        '''
        return self.web3.shh.newGroup()

    def shh_addToGroup(self):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#shh_addtogroup
        http://web3py.readthedocs.io/en/latest/web3.shh.html#web3.shh.Shh.addToGroup
        '''
        return self.web3.shh.addToGroup()

    def shh_newFilter(self, to, topics):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#shh_newfilter
        http://web3py.readthedocs.io/en/latest/web3.shh.html#web3.shh.Shh.filter
        # to is optional
        '''
        _filter = {
            'topics': topics,
            'to':     to
        }
        return self.web3.shh.newFilter(_filter)

    def shh_uninstallFilter(self, filter_id):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#shh_uninstallfilter
        http://web3py.readthedocs.io/en/latest/web3.shh.html#web3.shh.Shh.uninstallFilter
        '''
        return self.web3.shh.uninstallFilter(filter_id)

    def shh_getFilterChanges(self, filter_id):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#shh_getfilterchanges
        http://web3py.readthedocs.io/en/latest/web3.eth.html?highlight=syncing#web3.eth.Eth.getFilterChanges
        '''
        filt = self.web3.eth.filter()
        return self.web3.shh.getFilterChanges(filter_id)

    def shh_getMessages(self, filter_id):
        '''
        https://github.com/ethereum/wiki/wiki/JSON-RPC#shh_getmessages
        http://web3py.readthedocs.io/en/latest/web3.shh.html#web3.shh.Shh.getMessages
        '''
        return self.web3.shh.getMessages(filter_id)

    def getBlockRlp(self, number=0):

        #not accessible with convenience functions

        return self.web3.manager.request_blocking('debug_getBlockRlp', [number])

    def traceTransaction(self, txHash):
        #atm not directly accessible, so something like this is needed
        #https://github.com/pipermerriam/web3.py/issues/308
        
        return self.web3.manager.request_blocking('debug_traceTransaction', [txHash])

