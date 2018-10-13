import rlp
import binascii
from ethereum.utils import normalize_address, hash32, trie_root, \
    big_endian_int, address, int256, encode_hex, encode_int, \
    big_endian_to_int, int_to_addr, zpad, parse_as_bin, parse_as_int, \
    decode_hex, sha3, is_string, is_numeric
from rlp.sedes import big_endian_int, Binary, binary, CountableList
from ethereum import utils
from ethereum import trie
from ethereum.trie import Trie
from ethereum.securetrie import SecureTrie

BLANK_HASH = utils.sha3(b'')
BLANK_ROOT = utils.sha3rlp(b'')

STATE_DEFAULTS = {
    "txindex": 0,
    "gas_used": 0,
    "gas_limit": 3141592,
    "block_number": 0,
    "block_coinbase": '\x00' * 20,
    "block_difficulty": 1,
    "timestamp": 0,
    "logs": [],
    "receipts": [],
    "bloom": 0,
    "suicides": [],
    "recent_uncles": {},
    "prev_headers": [],
    "refunds": 0,
}


class Account(rlp.Serializable):
    """
    adjusted account from ethereum.state
    """

    fields = [
        ('nonce', big_endian_int),
        ('balance', big_endian_int),
        ('storage', trie_root),
        ('code_hash', hash32)
    ]

    def __init__(self, nonce, balance, storage, code_hash, db, addr):
        self.db = db
        self.address = addr
        super(Account, self).__init__(nonce, balance, storage, code_hash)
        self.storage_cache = {}
        self.storage_trie = SecureTrie(Trie(self.db))
        self.storage_trie.root_hash = self.storage
        self.touched = False
        self.existent_at_start = True
        self._mutable = True
        self.deleted = False

    @property
    def code(self):
        """
        code rlp data
        """
        return self.db.get(self.code_hash)

    def get_storage_data(self, key):
        """
        get storage data
        """
        if key not in self.storage_cache:
            v = self.storage_trie.get(utils.encode_int32(key))
            self.storage_cache[key] = utils.big_endian_to_int(
                rlp.decode(v) if v else b'')
        return self.storage_cache[key]

    @classmethod
    def blank_account(cls, db, addr, initial_nonce=0):
        """
        creates a blank account
        """
        db.put(BLANK_HASH, b'')
        o = cls(initial_nonce, 0, trie.BLANK_ROOT, BLANK_HASH, db, addr)
        o.existent_at_start = False
        return o

    def is_blank(self):
        """
        checks if is a blank account
        """
        return self.nonce == 0 and self.balance == 0 and self.code_hash == BLANK_HASH

class State:
    """
    adjusted state from ethereum.state
    """

    def __init__(self, db, root):
        self.db = db
        self.trie = Trie(self.db, root)
        self.secure_trie = SecureTrie(self.trie)
        self.journal = []
        self.cache = {}

    def get_and_cache_account(self, addr):
        """Gets and caches an account for an addres, creates blank if not found"""

        if addr in self.cache:
            return self.cache[addr]
        rlpdata = self.secure_trie.get(addr)
        if rlpdata == trie.BLANK_NODE and len(addr) == 32: # support for hashed addresses
            rlpdata = self.trie.get(addr)

        if rlpdata != trie.BLANK_NODE:
            o = rlp.decode(rlpdata, Account, db=self.db, address=addr)
        else:
            o = Account.blank_account(
                self.db, addr, 0)
        self.cache[addr] = o
        o._mutable = True
        o._cached_rlp = None
        return o

    def get_all_accounts(self):
        """
        iterates through trie to and yields non-blank leafs as accounts
        """
        for address_hash, rlpdata in self.secure_trie.trie.iter_branch():
            if rlpdata != trie.BLANK_NODE:
                yield rlp.decode(rlpdata, Account, db=self.db, address=address_hash)
