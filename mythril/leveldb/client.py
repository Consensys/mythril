import plyvel
import binascii
import rlp
from mythril.leveldb.accountindexing import CountableList
import hashlib
import logging
from ethereum import utils
from ethereum.block import BlockHeader, Block
from mythril.leveldb.accountindexing import ReceiptForStorage, AccountIndexer
from mythril.leveldb.state import State, Account
from mythril.leveldb.eth_db import ETH_DB
from mythril.ether.ethcontract import ETHContract, InstanceList

# Per https://github.com/ethereum/go-ethereum/blob/master/core/database_util.go
# prefixes and suffixes for keys in geth
headerPrefix = b'h'         # headerPrefix + num (uint64 big endian) + hash -> header
bodyPrefix = b'b'           # bodyPrefix + num (uint64 big endian) + hash -> block body
numSuffix = b'n'            # headerPrefix + num (uint64 big endian) + numSuffix -> hash
blockHashPrefix = b'H'      # blockHashPrefix + hash -> num (uint64 big endian)
blockReceiptsPrefix = b'r'  # blockReceiptsPrefix + num (uint64 big endian) + hash -> block receipts
# known geth keys
headHeaderKey = b'LastBlock' # head (latest) header hash
# custom prefixes
addressPrefix = b'AM'       # addressPrefix + hash -> address
# custom keys
addressMappingHeadKey = b'accountMapping' # head (latest) number of indexed block

def _formatBlockNumber(number):
    '''
    formats block number to uint64 big endian
    '''
    return utils.zpad(utils.int_to_big_endian(number), 8)

def _encode_hex(v):
    '''
    encodes hash as hex
    '''
    return '0x' + utils.encode_hex(v)

class LevelDBReader(object):
    '''
    level db reading interface, can be used with snapshot
    '''

    def __init__(self, db):
        self.db = db
        self.headBlockHeader = None
        self.headState = None

    def _get_head_state(self):
        '''
        gets head state
        '''
        if not self.headState:
            root = self._get_head_block().state_root
            self.headState = State(self.db, root)
        return self.headState

    def _get_account(self, address):
        '''
        gets account by address
        '''
        state = self._get_head_state()
        accountAddress = binascii.a2b_hex(utils.remove_0x_head(address))
        return state.get_and_cache_account(accountAddress)

    def _get_block_hash(self, number):
        '''
        gets block hash by block number
        '''
        num = _formatBlockNumber(number)
        hashKey = headerPrefix + num + numSuffix
        return self.db.get(hashKey)

    def _get_head_block(self):
        '''
        gets head block header
        '''
        if not self.headBlockHeader:
            hash = self.db.get(headHeaderKey)
            num = self._get_block_number(hash)
            self.headBlockHeader = self._get_block_header(hash, num)
            # find header with valid state
            while not self.db.get(self.headBlockHeader.state_root) and self.headBlockHeader.prevhash is not None:
                hash = self.headBlockHeader.prevhash
                num = self._get_block_number(hash)
                self.headBlockHeader = self._get_block_header(hash, num)

        return self.headBlockHeader

    def _get_block_number(self, hash):
        '''
        gets block number by hash
        '''
        numberKey = blockHashPrefix + hash
        return self.db.get(numberKey)

    def _get_block_header(self, hash, num):
        '''
        get block header by block header hash & number
        '''
        headerKey = headerPrefix + num + hash
        blockHeaderData = self.db.get(headerKey)
        header = rlp.decode(blockHeaderData, sedes=BlockHeader)
        return header

    def _get_address_by_hash(self, hash):
        '''
        get mapped address by its hash
        '''
        addressKey = addressPrefix + hash
        return self.db.get(addressKey)

    def _get_last_indexed_number(self):
        '''
        latest indexed block number
        '''
        return self.db.get(addressMappingHeadKey)

    def _get_block_receipts(self, hash, num):
        '''
        get block transaction receipts by block header hash & number
        '''
        number = _formatBlockNumber(num)
        receiptsKey = blockReceiptsPrefix + number + hash
        receiptsData = self.db.get(receiptsKey)
        receipts = rlp.decode(receiptsData, sedes=CountableList(ReceiptForStorage))
        return receipts

class LevelDBWriter(object):
    '''
    level db writing interface
    '''

    def __init__(self, db):
        self.db = db
        self.wb = None

    def _set_last_indexed_number(self, number):
        '''
        sets latest indexed block number
        '''
        return self.db.put(addressMappingHeadKey, _formatBlockNumber(number))

    def _start_writing(self):
        '''
        start writing a batch
        '''
        self.wb = self.db.write_batch()

    def _commit_batch(self):
        '''
        commit batch
        '''
        self.wb.write()

    def _store_account_address(self, address):
        '''
        get block transaction receipts by block header hash & number
        '''
        addressKey = addressPrefix + utils.sha3(address)
        self.wb.put(addressKey, address)

class EthLevelDB(object):
    '''
    Go-Ethereum LevelDB client class
    '''

    def __init__(self, path):
        self.path = path
        self.db = ETH_DB(path)
        self.reader = LevelDBReader(self.db)
        self.writer = LevelDBWriter(self.db)

    def get_contracts(self):
        '''
        iterate through all contracts
        '''
        indexer = AccountIndexer(self)
        for account in self.reader._get_head_state().get_all_accounts():
            if account.code is not None:
                code = _encode_hex(account.code)
                contract = ETHContract(code)
                address = indexer.get_contract_by_hash(account.address)
                if address is None:
                    address = account.address
                yield contract, _encode_hex(address), account.balance

    def search(self, expression, callback_func):
        '''
        searches through non-zero balance contracts
        '''
        cnt = 0

        for contract, address, balance in self.get_contracts():

            if contract.matches_expression(expression):
                callback_func(contract.name, contract, [address], [balance])

            cnt += 1

            if not cnt % 10:
                logging.info("Searched %d contracts" % cnt)

    def contract_hash_to_address(self, hash):
        '''
        tries to find corresponding account address
        '''
        indexer = AccountIndexer(self)
        addressHash = binascii.a2b_hex(utils.remove_0x_head(hash))
        address = indexer.get_contract_by_hash(addressHash)
        if address:
            return _encode_hex(address)
        else:
            return "Not found"

    def eth_getBlockHeaderByNumber(self, number):
        '''
        gets block header by block number
        '''
        hash = self.reader._get_block_hash(number)
        blockNumber = _formatBlockNumber(number)
        return self.reader._get_block_header(hash, blockNumber)

    def eth_getBlockByNumber(self, number):
        '''
        gets block body by block number
        '''
        blockHash = self.reader._get_block_hash(number)
        blockNumber = _formatBlockNumber(number)
        bodyKey = bodyPrefix + blockNumber + blockHash
        blockData = self.db.get(bodyKey)
        body = rlp.decode(blockData, sedes=Block)
        return body

    def eth_getCode(self, address):
        '''
        gets account code
        '''
        account = self.reader._get_account(address)
        return _encode_hex(account.code)

    def eth_getBalance(self, address):
        '''
        gets account balance
        '''
        account = self.reader._get_account(address)
        return account.balance

    def eth_getStorageAt(self, address, position):
        '''
        gets account storage data at position
        '''
        account = self.reader._get_account(address)
        return _encode_hex(utils.zpad(utils.encode_int(account.get_storage_data(position)), 32))