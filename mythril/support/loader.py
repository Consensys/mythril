from mythril.disassembler.disassembly import Disassembly
import logging
import re


class DynLoader:
    def __init__(self, eth, contract_loading=True, storage_loading=True):
        self.eth = eth
        self.storage_cache = {}
        self.contract_loading = contract_loading
        self.storage_loading = storage_loading

    def read_storage(self, contract_address, index):

        if not self.storage_loading:
            raise Exception(
                "Cannot load from the storage when the storage_loading flag is false"
            )

        try:
            contract_ref = self.storage_cache[contract_address]
            data = contract_ref[index]

        except KeyError:

            self.storage_cache[contract_address] = {}

            data = self.eth.eth_getStorageAt(
                contract_address, position=index, block="latest"
            )

            self.storage_cache[contract_address][index] = data

        except IndexError:

            data = self.eth.eth_getStorageAt(
                contract_address, position=index, block="latest"
            )

            self.storage_cache[contract_address][index] = data

        return data

    def dynld(self, contract_address, dependency_address):

        if not self.contract_loading:
            raise ValueError("Cannot load contract when contract_loading flag is false")

        logging.debug(
            "Dynld at contract " + contract_address + ": " + dependency_address
        )

        m = re.match(r"^(0x[0-9a-fA-F]{40})$", dependency_address)

        if m:
            dependency_address = m.group(1)

        else:
            return None

        logging.debug("Dependency address: " + dependency_address)

        code = self.eth.eth_getCode(dependency_address)

        if code == "0x":
            return None
        else:
            return Disassembly(code)
