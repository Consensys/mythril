from ethereum.db import BaseDB
import leveldb
from ethereum import slogging

slogging.set_level('db', 'debug')
log = slogging.get_logger('db')

compress = decompress = lambda x: x


class LevelDB(BaseDB):
    """
    filename                                    the database directory
    block_cache_size  (default: 8 * (2 << 20))  maximum allowed size for the block cache in bytes
    write_buffer_size (default  2 * (2 << 20))
    block_size        (default: 4096)           unit of transfer for the block cache in bytes
    max_open_files:   (default: 1000)
    create_if_missing (default: True)           if True, creates a new database if none exists
    error_if_exists   (default: False)          if True, raises and error if the database exists
    paranoid_checks   (default: False)          if True, raises an error as soon as an internal
                                                corruption is detected
    """

    max_open_files = 32000
    block_cache_size = 8 * 1024**2
    write_buffer_size = 4 * 1024**2

    def __init__(self, dbfile):
        self.uncommitted = dict()
        log.info('opening LevelDB',
                 path=dbfile,
                 block_cache_size=self.block_cache_size,
                 write_buffer_size=self.write_buffer_size,
                 max_open_files=self.max_open_files)
        self.dbfile = dbfile
        self.db = leveldb.LevelDB(dbfile, max_open_files=self.max_open_files)
        self.commit_counter = 0

    def reopen(self):
        del self.db
        self.db = leveldb.LevelDB(self.dbfile)

    def get(self, key):
        log.trace('getting entry', key=key.encode('hex')[:8])
        if key in self.uncommitted:
            if self.uncommitted[key] is None:
                raise KeyError("key not in db")
            log.trace('from uncommitted')
            return self.uncommitted[key]
        log.trace('from db')
        o = decompress(self.db.Get(key))
        self.uncommitted[key] = o
        return o

    def put(self, key, value):
        log.trace('putting entry', key=key.encode('hex')[:8], len=len(value))
        self.uncommitted[key] = value

    def commit(self):
        log.debug('committing', db=self)
        batch = leveldb.WriteBatch()
        for k, v in self.uncommitted.items():
            if v is None:
                batch.Delete(k)
            else:
                batch.Put(k, compress(v))
        self.db.Write(batch, sync=False)
        self.uncommitted.clear()
        log.debug('committed', db=self, num=len(self.uncommitted))
        # self.commit_counter += 1
        # if self.commit_counter % 100 == 0:
        #     self.reopen()

    def delete(self, key):
        log.trace('deleting entry', key=key)
        self.uncommitted[key] = None

    def _has_key(self, key):
        try:
            self.get(key)
            return True
        except KeyError:
            return False

    def __contains__(self, key):
        return self._has_key(key)

    def __eq__(self, other):
        return isinstance(other, self.__class__) and self.db == other.db

    def __repr__(self):
        return '<DB at %d uncommitted=%d>' % (id(self.db), len(self.uncommitted))

    def inc_refcount(self, key, value):
        self.put(key, value)

    def dec_refcount(self, key):
        pass

    def revert_refcount_changes(self, epoch):
        pass

    def commit_refcount_changes(self, epoch):
        pass

    def cleanup(self, epoch):
        pass

    def put_temporarily(self, key, value):
        self.inc_refcount(key, value)
        self.dec_refcount(key)

