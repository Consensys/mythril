import os
from mythril.ether.contractstorage import get_persistent_storage
from mythril.rpc.client import EthJsonRpc
from mythril.disassembler.disassembly import Disassembly
from laser.ethereum import laserfree
import logging

app_root = os.path.dirname(os.path.realpath(__file__))
db_dir = os.path.join(app_root, "database")

eth = EthJsonRpc("localhost", 8545)

contract_storage = get_persistent_storage(os.path.join(os.path.expanduser('~'), ".mythril"))

logging.basicConfig(level=logging.INFO)

def searchCallback(contract_hash, contract, addresses, balances):

    try:

        print("Checking contract: " + str(contract_hash))

        print(addresses[0])

        disas = Disassembly(contract.code)

        laserfree.fire(disas)

    except Exception as e:
        
        print(str(e))

print("Searching " +str(len(list(contract_storage.contracts))) + " contracts...")

contract_storage.search("code#PUSH#", searchCallback)
