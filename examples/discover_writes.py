from mythril.ether import util
from mythril.rpc.client import EthJsonRpc
from mythril.ether.contractstorage import get_persistent_storage
from mythril.disassembler.disassembly import Disassembly
from ethereum.abi import encode_abi
import re
import os


# Discover contract functions that write the sender address, or an address passed as an argument, to storage.
# Needs testrpc running on port 8546


addr_knupper= "0xfa22c52a4c1a8751efec39c7f4135884c3fd9b47"
addr_schnupper = "0xe2034e3991cd7de846af04e3f6fe61fc56a46dde"

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
    '''
    Test one function in a contract.
    Calls the function with the arguments listed in testargs1, and looks for SSTORE [address] in the execution trace.
    '''
    
    if re.match(r'^0x', function_selector):
        args = encode_abi(['address'], [addr_schnupper])
        data= function_selector + args.hex()
    else:
        data = util.encode_calldata(function_selector, arg_types, args)

    tx = testrpc.eth_sendTransaction(to_address=contract_addr, from_address=addr_schnupper, gas=50000000, value=0, data=data)

    trace = testrpc.traceTransaction(tx)

    if trace:
        for t in trace['structLogs']:
            if t['op'] == 'SSTORE':
                if addr_schnupper[2:] in t['stack'][-2]:
                    return True

    return False


def testDynamic(contract_hash, contract, addresses, balances):

    error = False

    ret = testrpc.eth_sendTransaction(from_address=addr_knupper, gas=50000000, value=0, data=contract.creation_code)
    receipt = testrpc.eth_getTransactionReceipt(ret)

    contract_addr = receipt['contractAddress']

    code = testrpc.eth_getCode(contract_addr)

    try:
        disas = Disassembly(code)
    except:
        error = True

    found = False

    if not error:

        for i in disas.func_to_addr:

            m = re.search(r'UNK_(0x[0-9a-f]*)', i)
            
            if (m):
                function_selector = m.group(1)
            else:
                function_selector = i

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

