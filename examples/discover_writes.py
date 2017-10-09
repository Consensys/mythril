from mythril.ether import util
from mythril.rpc.client import EthJsonRpc
from mythril.ether.contractstorage import get_persistent_storage
from mythril.disassembler.disassembly import Disassembly
from ethereum.abi import encode_abi
import re
import os


# Discover contract functions that write the sender address, or an address passed as an argument, to storage.
# Needs testrpc running on port 8546

# testrpc --port 8546 --gasLimit 0xFFFFFF --account 0x0b6f3fd29ca0e570faf9d0bb8945858b9c337cd2a2ff89d65013eec412a4a811,500000000000000000000 --account 0x2194ac1cd3b9ca6cccc1a90aa2c6f944994b80bb50c82b973adce7f288734d5c,500000000000000000000


addr_knupper= "0xe2beffc4bc7ebb9eae43d59d2b555749d9ce7c54"
addr_schnupper = "0xadc2f8617191ff60a36c3c136170cc69c03e64cd"

contract_storage = get_persistent_storage(os.path.join(os.path.expanduser('~'), ".mythril"))
testrpc = EthJsonRpc("localhost", 8546)

testargs1 = [
    ([], []),
    (['address'], [addr_schnupper]),
    (['address', 'uint256'], [addr_schnupper, 1 ]), 
    (['address', 'uint256', 'uint256'], [addr_schnupper, 1, 1]), 
    (['address[]'], [[addr_schnupper]]),
    (['address[]', 'uint256'], [[addr_schnupper], 1 ]),     
    (['address[]', 'uint256', 'uint256'], [[addr_schnupper], 1, 1]), 
]


def testCase(contract_addr, function_selector, arg_types, args):

    if re.match(r'^UNK_0x', function_selector):
        args = encode_abi(['address'], [addr_schnupper])
        data= function_selector[4:] + args.hex()
    else:
        data = util.encode_calldata(function_selector, arg_types, args)

    tx = testrpc.eth_sendTransaction(to_address=contract_addr, from_address=addr_schnupper, gas=5000000, value=0, data=data)

    trace = testrpc.traceTransaction(tx)

    if trace:
        for t in trace['structLogs']:
            if t['op'] == 'SSTORE':
                if addr_schnupper[2:] in t['stack'][-2]:
                    return True

    return False


def testDynamic(contract_hash, contract, addresses, balances):

    ret = testrpc.eth_sendTransaction(from_address=addr_knupper, gas=5000000, value=0, data=contract.creation_code)
    receipt = testrpc.eth_getTransactionReceipt(ret)
    contract_addr = receipt['contractAddress']

    try:
        disas = Disassembly(contract.code)
    except:
        return
        
    found = False

    for function_selector in disas.func_to_addr:

        try:
            for t in testargs1:
                if(testCase(contract_addr, function_selector, t[0], t[1])):
                    print("Possible write!")
                    print("Contract hash: " + contract_hash)
                    print("Selector: " + function_selector)
                    print("Input data: " + str(t[1]))

                    for i in range(0, len(addresses)):
                        print("Address: " + addresses[i] + ", balance: " + str(balances[i]))

                    found = True
                    break

            if found:
                break
        except:
            break


print("Searching " +str(len(list(contract_storage.contracts))) + " contracts...")

contract_storage.search("code#PUSH#", testDynamic) # Returns all contracts
