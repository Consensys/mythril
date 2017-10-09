from mythril.ether import evm
from mythril.ether.contractstorage import get_persistent_storage
from mythril.disassembler.disassembly import Disassembly
from mythril.rpc.client import EthJsonRpc
from mythril.disassembler.callgraph import generate_callgraph
import os


contract_storage = get_persistent_storage()
contract_keys = list(contract_storage.contracts)
homestead = EthJsonRpc()

# Iterate over all contracts in the database

for k in contract_keys:

    contract = contract_storage.contracts[k]

    # Run each contract in the PyEthereum EVM trace to check whether DELEGATECALL is reached
    # To execute the fallback function, we don't provide any input data

    ret = evm.trace(contract.code)

    if 'DELEGATECALL' in ret:

        print("DELEGATECALL in fallback function: Contract 0x" + k.hex() + " deployed at: ")

        instance_list = contract_storage.instance_lists[k]

        for i in range(1, len(instance_list.addresses)):
            print("Address: " + instance_list.addresses[i] + ", balance: " + str(instance_list.balances[i]))

        # contract.get_xrefs() should contain the delegateCall() target (library contract)

        print("Referenced contracts:")

        xrefs = contract.get_xrefs()

        print ("\n".join(xrefs))

        '''
        from here on are many different options!

        In this example, we'll only check one of the refernced contracts contains the initWallet() function
        If it does, we save the disassembly and callgraph for further analysis
        
        '''
 
        for xref in xrefs:
            code = homestead.eth_getCode(xref)

            disassembly = Disassembly(code)

            if contract.matches_expression("func#initWallet(address[],uint256,uint256)#"):
                print ("initWallet() in referenced library contract: " + xref)

                # Save list of contracts that forward calls to this library contract

                cwd = os.getcwd()

                with open("contracts_calling_" + xref + ".txt", "w") as f:
                    addresses = contract_storage.instance_lists[k].addresses

                    f.write("\n".join(addresses))

                easm = disassembly.get_easm()

                with open("library_" + xref + ".easm", "w") as f:
                    f.write(easm)

                generate_callgraph(disassembly, os.path.join(cwd, "library_" + xref))

