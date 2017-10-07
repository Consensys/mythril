from mythril.ether import util
from mythril.rpc.client import EthJsonRpc
from mythril.ether.contractstorage import get_persistent_storage
from mythril.disassembler.disassembly import Disassembly
from ethereum.abi import encode_abi
import re
import os


# Search for any contract functions write an address to storage.
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
    if re.match(r'^0x', function_selector):
        args = encode_abi(['address'], [addr_schnupper])
        data= function_selector + args.hex()
    else:
        data = util.encode_calldata(function_selector, arg_types, args)

    tx = testrpc.eth_sendTransaction(to_address=contract_addr, from_address=addr_schnupper, gas=50000000, value=0, data=data)

    trace = testrpc.traceTransaction(tx)

    if trace:
        for t in trace['structLogs']:
            # print (t['op'])
            if t['op'] == 'SSTORE':
                # print("SSTORE " + t['stack'][-2])
                if addr_schnupper[2:] in t['stack'][-2]:
                    return True

    return False


def testDynamic(contract_hash, contract, addresses, balances):

    error = False

    # print("Checking contract with hash " + contract_hash)

    ret = testrpc.eth_sendTransaction(from_address=addr_knupper, gas=50000000, value=0, data=contract.creation_code)

    # ret = testrpc.eth_sendTransaction(from_address=addr_knupper, gas=50000000, value=0, data="606060405233600160006101000a81548173ffffffffffffffffffffffffffffffffffffffff021916908373ffffffffffffffffffffffffffffffffffffffff16021790555033600260006101000a81548173ffffffffffffffffffffffffffffffffffffffff021916908373ffffffffffffffffffffffffffffffffffffffff1602179055506005600955341561009657600080fd5b61126c806100a56000396000f3006060604052361561015d576000357c0100000000000000000000000000000000000000000000000000000000900463ffffffff1680631fc0e5e91461016757806321a91d2b1461017c578063230c50fe146101a5578063326b7a14146101ca5780634d80bf14146102015780634dfdebe914610256578063547dfaf51461027f5780635af95010146102895780635cd51857146102e45780636006f1781461031d57806361f529af146103275780636eecf81a1461036057806370ce90d51461038357806370f5d3de1461039857806378357e53146103b05780637a2c1b71146104055780638386927a146104525780638da5cb5b1461045c5780639fc6ceac146104b1578063a6f9dae1146104da578063ae1345c414610513578063b0a77ef71461053c578063b0a9165914610573578063b16d22a014610588578063b9793dca1461059d578063bd9b6d86146105ea578063ed21248c146105ff575b610165610609565b005b341561017257600080fd5b61017a6106d5565b005b341561018757600080fd5b61018f61073d565b6040518082815260200191505060405180910390f35b34156101b057600080fd5b6101c860048080351515906020019091905050610743565b005b6101ff600480803573ffffffffffffffffffffffffffffffffffffffff1690602001909190803590602001909190505061076e565b005b341561020c57600080fd5b610214610809565b604051808273ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200191505060405180910390f35b341561026157600080fd5b61026961082f565b6040518082815260200191505060405180910390f35b610287610835565b005b341561029457600080fd5b6102c0600480803573ffffffffffffffffffffffffffffffffffffffff16906020019091905050610907565b60405180848152602001838152602001828152602001935050505060405180910390f35b34156102ef57600080fd5b61031b600480803573ffffffffffffffffffffffffffffffffffffffff16906020019091905050610931565b005b610325610983565b005b341561033257600080fd5b61035e600480803573ffffffffffffffffffffffffffffffffffffffff16906020019091905050610a73565b005b341561036b57600080fd5b6103816004808035906020019091905050610af8565b005b341561038e57600080fd5b610396610b27565b005b6103ae6004808035906020019091905050610be3565b005b34156103bb57600080fd5b6103c3610c9f565b604051808273ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200191505060405180910390f35b341561041057600080fd5b61043c600480803573ffffffffffffffffffffffffffffffffffffffff16906020019091905050610cc5565b6040518082815260200191505060405180910390f35b61045a610609565b005b341561046757600080fd5b61046f610d75565b604051808273ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200191505060405180910390f35b34156104bc57600080fd5b6104c4610d9b565b6040518082815260200191505060405180910390f35b34156104e557600080fd5b610511600480803573ffffffffffffffffffffffffffffffffffffffff16906020019091905050610da1565b005b341561051e57600080fd5b610526610df2565b6040518082815260200191505060405180910390f35b610571600480803573ffffffffffffffffffffffffffffffffffffffff16906020019091908035906020019091905050610df8565b005b341561057e57600080fd5b610586610eb7565b005b341561059357600080fd5b61059b610fa4565b005b34156105a857600080fd5b6105d4600480803573ffffffffffffffffffffffffffffffffffffffff1690602001909190505061100c565b6040518082815260200191505060405180910390f35b34156105f557600080fd5b6105fd611024565b005b6106076110de565b005b670de0b6b3a7640000341015156106d3576000600b60003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020541415610675576006600081548092919060010191905055505b34600b60003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060008282540192505081905550346007600082825401925050819055505b565b6106dd611138565b1561073b576106ec6001610743565b3373ffffffffffffffffffffffffffffffffffffffff167faf9cb8c082d497f25197d688303034bf5fde66e3faa3bdc1ef832e47088bde93426040518082815260200191505060405180910390a25b565b60095481565b61074b6111e8565b1561076b5780600a60006101000a81548160ff0219169083151502179055505b50565b600260009054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff161415610805578173ffffffffffffffffffffffffffffffffffffffff166108fc829081150290604051600060405180830381858888f19350505050151561080457600080fd5b5b5050565b600460009054906101000a900473ffffffffffffffffffffffffffffffffffffffff1681565b60085481565b600260009054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff16141561090557600260009054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff166108fc3073ffffffffffffffffffffffffffffffffffffffff16319081150290604051600060405180830381858888f19350505050151561090457600080fd5b5b565b600c6020528060005260406000206000915090508060000154908060010154908060020154905083565b610939611138565b156109805780600460006101000a81548173ffffffffffffffffffffffffffffffffffffffff021916908373ffffffffffffffffffffffffffffffffffffffff1602179055505b50565b6000600a60009054906101000a900460ff1615610a70576109a2610eb7565b600c60003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000206002015490506000600c60003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600201819055503373ffffffffffffffffffffffffffffffffffffffff166108fc829081150290604051600060405180830381858888f193505050501515610a6f57600080fd5b5b50565b33600560006101000a81548173ffffffffffffffffffffffffffffffffffffffff021916908373ffffffffffffffffffffffffffffffffffffffff16021790555080600360006101000a81548173ffffffffffffffffffffffffffffffffffffffff021916908373ffffffffffffffffffffffffffffffffffffffff16021790555050565b610b00611138565b15610b245760095481141515610b2357600181101515610b2257806009819055505b5b5b50565b600460009054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff161415610be157600460009054906101000a900473ffffffffffffffffffffffffffffffffffffffff16600360006101000a81548173ffffffffffffffffffffffffffffffffffffffff021916908373ffffffffffffffffffffffffffffffffffffffff1602179055505b565b600260009054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff161415610c9c57600260009054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff166108fc829081150290604051600060405180830381858888f193505050501515610c9b57600080fd5b5b50565b600360009054906101000a900473ffffffffffffffffffffffffffffffffffffffff1681565b600062015180600c60008473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600001544203811515610d1957fe5b046009546064600c60008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060010154811515610d6b57fe5b0402029050919050565b600560009054906101000a900473ffffffffffffffffffffffffffffffffffffffff1681565b60065481565b610da96111e8565b15610def57806000806101000a81548173ffffffffffffffffffffffffffffffffffffffff021916908373ffffffffffffffffffffffffffffffffffffffff1602179055505b50565b60075481565b6000600b60008473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020541115610eb357610e486111e8565b15610eb2578173ffffffffffffffffffffffffffffffffffffffff166108fc829081150290604051600060405180830381858888f1935050505015610eb15780600754101515610ea75780600760008282540392505081905550610eb0565b60006007819055505b5b5b5b5050565b6000600c60003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600101541115610f5b57610f0b33610cc5565b600c60003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600201600082825401925050819055505b42600c60003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060000181905550565b610fac611138565b1561100a57610fbb6000610743565b3373ffffffffffffffffffffffffffffffffffffffff167f191313aeddac1904c3453ef2898668c642135419a28b905f260bca51cf1b909a426040518082815260200191505060405180910390a25b565b600b6020528060005260406000206000915090505481565b6000809054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff1614156110dc576000809054906101000a900473ffffffffffffffffffffffffffffffffffffffff16600160006101000a81548173ffffffffffffffffffffffffffffffffffffffff021916908373ffffffffffffffffffffffffffffffffffffffff1602179055505b565b6110e6610eb7565b34600c60003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060010160008282540192505081905550565b6000600360009054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff1614806111e35750600560009054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff16145b905090565b60003373ffffffffffffffffffffffffffffffffffffffff16600160009054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16149050905600a165627a7a7230582025e150fc1bc525f049b9c9e3f7eac866b773035a27c84e6a6179e33e05c676920029")

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

