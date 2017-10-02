import unittest
from mythril.ether.contractstorage import get_persistent_storage
import os


class GetAndSearchContractTestCase(unittest.TestCase):

    def mockCallback(self, code_hash, code, addresses, balances):
        self.isFound = True
        pass

    def runTest(self):

        script_path = os.path.dirname(os.path.realpath(__file__))
        storage_dir = os.path.join(script_path, 'teststorage')
        storage = get_persistent_storage(storage_dir)    

        contract = storage.get_contract_by_hash(bytes.fromhex("ea061445eacbe86b7ffed2bb9e52075e"))

        self.assertTrue("0x60606040" in contract.code,'error reading contract code from database')

        self.isFound = False

        storage.search("code#PUSH1#", self.mockCallback)

        self.assertTrue(self.isFound,'storage search error')      
