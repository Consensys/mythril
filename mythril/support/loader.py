"""This module contains the dynamic loader logic to get on-chain storage data
and dependencies."""
from mythril.disassembler.disassembly import Disassembly
import logging
import re

log = logging.getLogger(__name__)


class DynLoader:
    """The dynamic loader class."""

    def __init__(self, eth, contract_loading=True, storage_loading=True):
        """

        :param eth:
        :param contract_loading:
        :param storage_loading:
        """
        self.eth = eth
        self.storage_cache = {}
        self.contract_loading = contract_loading
        self.storage_loading = storage_loading

    def read_storage(self, contract_address, index):
        """

        :param contract_address:
        :param index:
        :return:
        """
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
        """

        :param contract_address:
        :param dependency_address:
        :return:
        """
        if not self.contract_loading:
            raise ValueError("Cannot load contract when contract_loading flag is false")

        log.debug("Dynld at contract " + contract_address + ": " + dependency_address)

        # Ensure that dependency_address is the correct length, with 0s prepended as needed.
        dependency_address = (
            "0x" + "0" * (42 - len(dependency_address)) + dependency_address[2:]
        )

        m = re.match(r"^(0x[0-9a-fA-F]{40})$", dependency_address)

        if m:
            dependency_address = m.group(1)

        else:
            return None

        log.debug("Dependency address: " + dependency_address)

        code = self.eth.eth_getCode(dependency_address)

        if code == "0x":
            return None
        else:
            return Disassembly(code)
