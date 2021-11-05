"""This module contains the ETH_DB class, which the base database used by
pyethereum."""

from ethereum.db import BaseDB

has_plyvel = True
try:
    import plyvel
except ImportError:
    has_plyvel = False


class ETH_DB(BaseDB):
    """Adopts pythereum BaseDB using plyvel."""

    def __init__(self, path):
        if has_plyvel is False:
            raise ImportError(
                "Plyvel is not installed, please install plyvel and leveldb"
            )
        self.db = plyvel.DB(path)

    def get(self, key):
        """gets value for key."""
        return self.db.get(key)

    def put(self, key, value):
        """puts value for key."""
        self.db.put(key, value)

    def write_batch(self):
        """start writing a batch."""
        return self.db.write_batch()
