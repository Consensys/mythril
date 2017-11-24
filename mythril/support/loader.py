from mythril.ether.ethcontract import ETHContract
import logging
import re

class DynLoader:

    def __init__(self, eth):
        self.eth = eth

    def dynld(self, contract_address, dependency_address):

        logging.info("Dynld at contract " + contract_address + ": "  + dependency_address)

        m = re.match(r'^(0x[0-9a-fA-F]{40})$', dependency_address)

        if (m):
            dependency_address = m.group(1)

        else:
            m = re.search(r'storage_(\d+)', dependency_address)

            if (m):
                idx = int(m.group(1))
                logging.info("Dynamic contract address at storage index " + str(idx))

                # testrpc simply returns the address, geth response is more elaborate.

                dependency_address = self.eth.eth_getStorageAt(contract_address, position=idx, block='latest')

                logging.info("eth_getStorageAt: " + dependency_address)

                if not re.match(r"^0x[0-9a-f]{40}$", dependency_address):

                    dependency_address = "0x" + dependency_address[26:]
                

            else:
                logging.info("Unable to resolve address.")
                return None


        logging.info("Dependency address: " +  dependency_address)

        code = self.eth.eth_getCode(dependency_address)

        if (code == "0x"):
            return None
        else:
            contract = ETHContract(self.eth.eth_getCode(dependency_address), name=dependency_address, address=dependency_address)
            return contract.as_dict()