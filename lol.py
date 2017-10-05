from mythril.ether import evm,util
from mythril.disassembler.disassembly import Disassembly
import re
import os
from mythril.ether.contractstorage import get_persistent_storage


contract_storage = get_persistent_storage(os.path.join(os.path.expanduser('~'), ".mythril"))


def testDynamic(contract_hash, contract, addresses, balances):

    print("Checking contract with hash " + contract_hash)

    disas = Disassembly(contract.code)

    funcs = []

    for i in disas.func_to_addr:

        m = re.search(r'UNK_(0x[0-9a-f]*)', i)

        if (m):
            funcs.append(m.group(1))
        

    print(funcs)

    '''
    target_address_hex = '0xc41594f96a3a165cc57d550b0fbe4c8b9a717854'
    target_address_int = str(int(target_address_hex[2:],16))

    call_data = "0x" + util.encode_calldata('setOwner', ['address'], [target_address_hex]).hex()
    output = evm.trace(util.safe_decode(contract.code), target_address_hex, call_data)

    m = re.search(r'' + target_address_int + '.*SSTORE', output, re.MULTILINE)

    if (m):
        print("setOwner() successfully called.")
        print(output)

        print("Addresses:")
        print(addresses)    
   '''


print("Searching " +str(len(list(contract_storage.contracts))) + " contracts...")


contract_storage.search("code#PUSH#", testDynamic)
