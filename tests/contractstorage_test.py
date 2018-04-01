from mythril.ether.contractstorage import get_persistent_storage
import os
from tests import BaseTestCase

class GetAndSearchContractTestCase(BaseTestCase):

    def setUp(self):
        super(GetAndSearchContractTestCase, self).setUp()
        script_path = os.path.dirname(os.path.realpath(__file__))
        storage_dir = os.path.join(script_path, 'teststorage')
        self.storage, self.db = get_persistent_storage(storage_dir)

    def tearDown(self):
        self.db.close()
        super(GetAndSearchContractTestCase, self).tearDown()

    def mockCallback(self, code_hash, code, addresses, balances):
        self.code_hash = code_hash
        self.isFound = True
        pass

    def runTest(self):
        contract = self.storage.get_contract_by_hash(bytes.fromhex("ea061445eacbe86b7ffed2bb9e52075e"))

        self.assertTrue("0x60606040" in contract.code, 'error reading contract code from database')

        self.isFound = False

        self.storage.search("code#PUSH1#", self.mockCallback)

        self.assertTrue(self.isFound, 'storage search error')
        self.assertEqual(self.code_hash, 'ea061445eacbe86b7ffed2bb9e52075e', 'storage search error')
