import re
from mythril.exceptions import CriticalError


class MythrilLevelDB(object):
    """
    Class which does operations on leveldb
    """

    def __init__(self, leveldb):
        self.level_db = leveldb

    def search_db(self, search):
        """
        Searches 
        :param search:
        """

        def search_callback(_, address, balance):
            """

            :param _:
            :param address:
            :param balance:
            """
            print("Address: " + address + ", balance: " + str(balance))

        try:
            self.level_db.search(search, search_callback)

        except SyntaxError:
            raise CriticalError("Syntax error in search expression.")

    def contract_hash_to_address(self, hash):
        """
        Returns address of the corresponding hash by searching the leveldb
        :param hash: Hash to be searched
        """
        if not re.match(r"0x[a-fA-F0-9]{64}", hash):
            raise CriticalError("Invalid address hash. Expected format is '0x...'.")

        print(self.level_db.contract_hash_to_address(hash))
