from mythril.ether.ethcontract import ETHContract
import logging
import re

class DynLoader:

    def __init__(self, eth):
        self.eth = eth
        self.storage_cache = {}


    def read_storage(self, contract_address, index):

        try:
            contract_ref = self.storage_cache[contract_address]
            data = contract_ref[index]

        except KeyError:

            self.storage_cache[contract_address] = {}

            data = self.eth.eth_getStorageAt(contract_address, position=index, block='latest')

            self.storage_cache[contract_address][index] = data

        except IndexError:

            data = self.eth.eth_getStorageAt(contract_address, position=index, block='latest')

            self.storage_cache[contract_address][index] = data

        return data


    def dynld(self, contract_address, dependency_address):

        logging.info("Dynld at contract " + contract_address + ": "  + dependency_address)

        m = re.match(r'^(0x[0-9a-fA-F]{40})$', dependency_address)

        if (m):
            dependency_address = m.group(1)

        else:
            return None

        logging.info("Dependency address: " +  dependency_address)

        code = self.eth.eth_getCode(dependency_address)

        if (code == "0x"):
            return None
        else:
            return ETHContract(self.eth.eth_getCode(dependency_address)).get_disassembly()
