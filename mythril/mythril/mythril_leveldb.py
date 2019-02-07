import re
from mythril.exceptions import CriticalError


class MythrilLevelDB:
    """
    Class which does search operations on leveldb
    There are two DBs
    1) Key value pairs of hashes and it's corresponding address
    2) The LevelDB Trie
    """

    def __init__(self, leveldb):
        """

        :param leveldb: Leveldb path
        """
        self.leveldb = leveldb

    def search_db(self, search):
        """
        Searches the corresponding code
        :param search: The code part to be searched
        """

        def search_callback(_, address, balance):
            """

            :param _:
            :param address: The address of the contract with the code in search
            :param balance: The balance of the corresponding contract
            """
            print("Address: " + address + ", balance: " + str(balance))

        try:
            self.leveldb.search(search, search_callback)

        except SyntaxError:
            raise CriticalError("Syntax error in search expression.")

    def contract_hash_to_address(self, contract_hash):
        """
        Returns address of the corresponding hash by searching the leveldb
        :param contract_hash: Hash to be searched
        """
        if not re.match(r"0x[a-fA-F0-9]{64}", contract_hash):
            raise CriticalError("Invalid address hash. Expected format is '0x...'.")

        print(self.leveldb.contract_hash_to_address(contract_hash))
