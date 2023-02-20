Tutorial
======================

******************************************
Introduction
******************************************
Mythril is a popular security analysis tool for smart contracts. It is an open-source tool that can analyze Ethereum smart contracts and report potential security vulnerabilities in them. By analyzing the bytecode of a smart contract, Mythril can identify and report on possible security vulnerabilities, such as reentrancy attacks, integer overflows, and other common smart contract vulnerabilities.
This tutorial explains how to use Mythril to analyze simple Solidity contracts for security vulnerabilities. A simple contract is one that does not have any imports. 


******************************************
Executing Mythril on Simple Contracts
******************************************

To start, we consider this simple contract, ``Exceptions``, which has a number of functions, including ``assert1()``, ``assert2()``, and ``assert3()``, that contain Solidity ``assert()`` statements. We will use Mythril to analyze this contract and report any potential vulnerabilities.




   .. code-block:: solidity

        contract Exceptions {

            uint256[8] myarray;
            uint counter = 0;
            function assert1() public pure {
                uint256 i = 1;
                assert(i == 0);
            }
            function counter_increase() public {
                counter+=1;
            }
            function assert5(uint input_x) public view{
                require(counter>2);
                assert(input_x > 10);
            }
            function assert2() public pure {
                uint256 i = 1;
                assert(i > 0);
            }

            function assert3(uint256 input) public pure {
                assert(input != 23);
            }

            function require_is_fine(uint256 input) public pure {
                require(input != 23);
            }

            function this_is_fine(uint256 input) public pure {
                if (input > 0) {
                    uint256 i = 1/input;
                }
            }

            function this_is_find_2(uint256 index) public view {
                if (index < 8) {
                    uint256 i = myarray[index];
                }
            }

        }

The sample contract has several functions, some of which contain vulnerabilities. For instance, the ``assert1()`` function contains an assertion violation. To analyze the contract using Mythril, the following command can be used:

    .. code-block:: bash

        $ myth analyze <file_path>

The output will show the vulnerabilities in the contract. In the case of the "Exceptions" contract, Mythril detected two instances of assertion violations.


    .. code-block:: none

        ==== Exception State ====
        SWC ID: 110
        Severity: Medium
        Contract: Exceptions
        Function name: assert1()
        PC address: 708
        Estimated Gas Usage: 207 - 492
        An assertion violation was triggered.
        It is possible to trigger an assertion violation. Note that Solidity assert() statements should only be used to check invariants. Review the transaction trace generated for this issue and either make sure your program logic is correct, or use require() instead of assert() if your goal is to constrain user inputs or enforce preconditions. Remember to validate inputs from both callers (for instance, via passed arguments) and callees (for instance, via return values).
        --------------------
        In file: solidity_examples/exceptions.sol:7

        assert(i == 0)

        --------------------
        Initial State:

        Account: [CREATOR], balance: 0x2, nonce:0, storage:{}
        Account: [ATTACKER], balance: 0x0, nonce:0, storage:{}

        Transaction Sequence:

        Caller: [CREATOR], calldata: , value: 0x0
        Caller: [ATTACKER], function: assert1(), txdata: 0xb34c3610, value: 0x0

        ==== Exception State ====
        SWC ID: 110
        Severity: Medium
        Contract: Exceptions
        Function name: assert3(uint256)
        PC address: 708
        Estimated Gas Usage: 482 - 767
        An assertion violation was triggered.
        It is possible to trigger an assertion violation. Note that Solidity assert() statements should only be used to check invariants. Review the transaction trace generated for this issue and either make sure your program logic is correct, or use require() instead of assert() if your goal is to constrain user inputs or enforce preconditions. Remember to validate inputs from both callers (for instance, via passed arguments) and callees (for instance, via return values).
        --------------------
        In file: solidity_examples/exceptions.sol:20

        assert(input != 23)

        --------------------
        Initial State:

        Account: [CREATOR], balance: 0x40207f9b0, nonce:0, storage:{}
        Account: [ATTACKER], balance: 0x0, nonce:0, storage:{}

        Transaction Sequence:

        Caller: [CREATOR], calldata: , value: 0x0
        Caller: [SOMEGUY], function: assert3(uint256), txdata: 0x546455b50000000000000000000000000000000000000000000000000000000000000017, value: 0x0


One of the functions, ``assert5(uint256)``, should also have an assertion failure, but it is not detected because Mythril's default configuration is to run three transactions. 
To detect this vulnerability, the transaction count can be increased to four using the ``-t`` option, as shown below:

.. code-block:: bash

    $ myth analyze <file_path> -t 4

This gives the following execution output:

    .. code-block:: none

        ==== Exception State ====
        SWC ID: 110
        Severity: Medium
        Contract: Exceptions
        Function name: assert1()
        PC address: 731
        Estimated Gas Usage: 207 - 492
        An assertion violation was triggered.
        It is possible to trigger an assertion violation. Note that Solidity assert() statements should only be used to check invariants. Review the transaction trace generated for this issue and either make sure your program logic is correct, or use require() instead of assert() if your goal is to constrain user inputs or enforce preconditions. Remember to validate inputs from both callers (for instance, via passed arguments) and callees (for instance, via return values).
        --------------------
        In file: solidity_examples/exceptions.sol:7

        assert(i == 0)

        --------------------
        Initial State:

        Account: [CREATOR], balance: 0x2, nonce:0, storage:{}
        Account: [ATTACKER], balance: 0x0, nonce:0, storage:{}

        Transaction Sequence:

        Caller: [CREATOR], calldata: , value: 0x0
        Caller: [ATTACKER], function: assert1(), txdata: 0xb34c3610, value: 0x0

        ==== Exception State ====
        SWC ID: 110
        Severity: Medium
        Contract: Exceptions
        Function name: assert3(uint256)
        PC address: 731
        Estimated Gas Usage: 504 - 789
        An assertion violation was triggered.
        It is possible to trigger an assertion violation. Note that Solidity assert() statements should only be used to check invariants. Review the transaction trace generated for this issue and either make sure your program logic is correct, or use require() instead of assert() if your goal is to constrain user inputs or enforce preconditions. Remember to validate inputs from both callers (for instance, via passed arguments) and callees (for instance, via return values).
        --------------------
        In file: solidity_examples/exceptions.sol:22

        assert(input != 23)

        --------------------
        Initial State:

        Account: [CREATOR], balance: 0x3, nonce:0, storage:{}
        Account: [ATTACKER], balance: 0x0, nonce:0, storage:{}

        Transaction Sequence:

        Caller: [CREATOR], calldata: , value: 0x0
        Caller: [ATTACKER], function: assert3(uint256), txdata: 0x546455b50000000000000000000000000000000000000000000000000000000000000017, value: 0x0

        ==== Exception State ====
        SWC ID: 110
        Severity: Medium
        Contract: Exceptions
        Function name: assert5(uint256)
        PC address: 731
        Estimated Gas Usage: 1302 - 1587
        An assertion violation was triggered.
        It is possible to trigger an assertion violation. Note that Solidity assert() statements should only be used to check invariants. Review the transaction trace generated for this issue and either make sure your program logic is correct, or use require() instead of assert() if your goal is to constrain user inputs or enforce preconditions. Remember to validate inputs from both callers (for instance, via passed arguments) and callees (for instance, via return values).
        --------------------
        In file: solidity_examples/exceptions.sol:14

        assert(input_x > 10)

        --------------------
        Initial State:

        Account: [CREATOR], balance: 0x20000000, nonce:0, storage:{}
        Account: [ATTACKER], balance: 0x1000000, nonce:0, storage:{}

        Transaction Sequence:

        Caller: [CREATOR], calldata: , value: 0x0
        Caller: [ATTACKER], function: counter_increase(), txdata: 0xe47b0253, value: 0x0
        Caller: [CREATOR], function: counter_increase(), txdata: 0xe47b0253, value: 0x0
        Caller: [CREATOR], function: counter_increase(), txdata: 0xe47b0253, value: 0x0
        Caller: [ATTACKER], function: assert5(uint256), txdata: 0x1d5d53dd0000000000000000000000000000000000000000000000000000000000000003, value: 0x0




For the violation in the 4th transaction, the input value should be less than 10. The transaction data generated by Mythril for the
4th transaction is ``0x1d5d53dd0000000000000000000000000000000000000000000000000000000000000003``, the first 4 bytes ``1d5d53dd``
correspond to the function signature hence the input generated by Mythril is ``0000000000000000000000000000000000000000000000000000000000000003``
in hex, which is 3. For automated resolution of the input try using a different output format such as JSON.

    .. code-block:: bash

        $ myth analyze <file_path> -o json

This leads to the following output:

    .. code-block:: json

        {
            "error": null,
            "issues": [{
                "address": 731,
                "code": "assert(i == 0)",
                "contract": "Exceptions",
                "description": "An assertion violation was triggered.\nIt is possible to trigger an assertion violation. Note that Solidity assert() statements should only be used to check invariants. Review the transaction trace generated for this issue and either make sure your program logic is correct, or use require() instead of assert() if your goal is to constrain user inputs or enforce preconditions. Remember to validate inputs from both callers (for instance, via passed arguments) and callees (for instance, via return values).",
                "filename": "solidity_examples/exceptions.sol",
                "function": "assert1()",
                "lineno": 7,
                "max_gas_used": 492,
                "min_gas_used": 207,
                "severity": "Medium",
                "sourceMap": ":::i",
                "swc-id": "110",
                "title": "Exception State",
                "tx_sequence": {
                    "initialState": {
                        "accounts": {
                            "0xaffeaffeaffeaffeaffeaffeaffeaffeaffeaffe": {
                                "balance": "0x2",
                                "code": "",
                                "nonce": 0,
                                "storage": "{}"
                            },
                            "0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef": {
                                "balance": "0x0",
                                "code": "",
                                "nonce": 0,
                                "storage": "{}"
                            }
                        }
                    },
                    "steps": [{
                        "address": "",
                        "calldata": "",
                        "input": "0x6080604052600060085534801561001557600080fd5b506103f7806100256000396000f3fe608060405234801561001057600080fd5b50600436106100885760003560e01c8063b34c36101161005b578063b34c3610146100fd578063b630d70614610107578063e47b025314610123578063f44f13d81461012d57610088565b806301d4277c1461008d5780631d5d53dd146100a9578063546455b5146100c557806378375f14146100e1575b600080fd5b6100a760048036038101906100a29190610251565b610137565b005b6100c360048036038101906100be9190610251565b61015e565b005b6100df60048036038101906100da9190610251565b610181565b005b6100fb60048036038101906100f69190610251565b610196565b005b6101056101a7565b005b610121600480360381019061011c9190610251565b6101c1565b005b61012b6101e0565b005b6101356101fc565b005b600881101561015b5760008082600881106101555761015461027e565b5b01549050505b50565b60026008541161016d57600080fd5b600a811161017e5761017d6102ad565b5b50565b6017811415610193576101926102ad565b5b50565b60178114156101a457600080fd5b50565b600060019050600081146101be576101bd6102ad565b5b50565b60008111156101dd5760008160016101d9919061033a565b9050505b50565b6001600860008282546101f3919061036b565b92505081905550565b60006001905060008111610213576102126102ad565b5b50565b600080fd5b6000819050919050565b61022e8161021b565b811461023957600080fd5b50565b60008135905061024b81610225565b92915050565b60006020828403121561026757610266610216565b5b60006102758482850161023c565b91505092915050565b7f4e487b7100000000000000000000000000000000000000000000000000000000600052603260045260246000fd5b7f4e487b7100000000000000000000000000000000000000000000000000000000600052600160045260246000fd5b7f4e487b7100000000000000000000000000000000000000000000000000000000600052601260045260246000fd5b7f4e487b7100000000000000000000000000000000000000000000000000000000600052601160045260246000fd5b60006103458261021b565b91506103508361021b565b9250826103605761035f6102dc565b5b828204905092915050565b60006103768261021b565b91506103818361021b565b9250827fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff038211156103b6576103b561030b565b5b82820190509291505056fea2646970667358221220b474c01fa60d997027e1ceb779bcb2b34b6752282e0ea3a038a08b889fe0163f64736f6c634300080c0033",
                        "name": "unknown",
                        "origin": "0xaffeaffeaffeaffeaffeaffeaffeaffeaffeaffe",
                        "value": "0x0"
                    }, {
                        "address": "0x901d12ebe1b195e5aa8748e62bd7734ae19b51f",
                        "calldata": "0xb34c3610",
                        "input": "0xb34c3610",
                        "name": "assert1()",
                        "origin": "0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef",
                        "resolved_input": null,
                        "value": "0x0"
                    }]
                }
            }, {
                "address": 731,
                "code": "assert(input != 23)",
                "contract": "Exceptions",
                "description": "An assertion violation was triggered.\nIt is possible to trigger an assertion violation. Note that Solidity assert() statements should only be used to check invariants. Review the transaction trace generated for this issue and either make sure your program logic is correct, or use require() instead of assert() if your goal is to constrain user inputs or enforce preconditions. Remember to validate inputs from both callers (for instance, via passed arguments) and callees (for instance, via return values).",
                "filename": "solidity_examples/exceptions.sol",
                "function": "assert3(uint256)",
                "lineno": 22,
                "max_gas_used": 789,
                "min_gas_used": 504,
                "severity": "Medium",
                "sourceMap": ":::i",
                "swc-id": "110",
                "title": "Exception State",
                "tx_sequence": {
                    "initialState": {
                        "accounts": {
                            "0xaffeaffeaffeaffeaffeaffeaffeaffeaffeaffe": {
                                "balance": "0x3",
                                "code": "",
                                "nonce": 0,
                                "storage": "{}"
                            },
                            "0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef": {
                                "balance": "0x0",
                                "code": "",
                                "nonce": 0,
                                "storage": "{}"
                            }
                        }
                    },
                    "steps": [{
                        "address": "",
                        "calldata": "",
                        "input": "0x6080604052600060085534801561001557600080fd5b506103f7806100256000396000f3fe608060405234801561001057600080fd5b50600436106100885760003560e01c8063b34c36101161005b578063b34c3610146100fd578063b630d70614610107578063e47b025314610123578063f44f13d81461012d57610088565b806301d4277c1461008d5780631d5d53dd146100a9578063546455b5146100c557806378375f14146100e1575b600080fd5b6100a760048036038101906100a29190610251565b610137565b005b6100c360048036038101906100be9190610251565b61015e565b005b6100df60048036038101906100da9190610251565b610181565b005b6100fb60048036038101906100f69190610251565b610196565b005b6101056101a7565b005b610121600480360381019061011c9190610251565b6101c1565b005b61012b6101e0565b005b6101356101fc565b005b600881101561015b5760008082600881106101555761015461027e565b5b01549050505b50565b60026008541161016d57600080fd5b600a811161017e5761017d6102ad565b5b50565b6017811415610193576101926102ad565b5b50565b60178114156101a457600080fd5b50565b600060019050600081146101be576101bd6102ad565b5b50565b60008111156101dd5760008160016101d9919061033a565b9050505b50565b6001600860008282546101f3919061036b565b92505081905550565b60006001905060008111610213576102126102ad565b5b50565b600080fd5b6000819050919050565b61022e8161021b565b811461023957600080fd5b50565b60008135905061024b81610225565b92915050565b60006020828403121561026757610266610216565b5b60006102758482850161023c565b91505092915050565b7f4e487b7100000000000000000000000000000000000000000000000000000000600052603260045260246000fd5b7f4e487b7100000000000000000000000000000000000000000000000000000000600052600160045260246000fd5b7f4e487b7100000000000000000000000000000000000000000000000000000000600052601260045260246000fd5b7f4e487b7100000000000000000000000000000000000000000000000000000000600052601160045260246000fd5b60006103458261021b565b91506103508361021b565b9250826103605761035f6102dc565b5b828204905092915050565b60006103768261021b565b91506103818361021b565b9250827fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff038211156103b6576103b561030b565b5b82820190509291505056fea2646970667358221220b474c01fa60d997027e1ceb779bcb2b34b6752282e0ea3a038a08b889fe0163f64736f6c634300080c0033",
                        "name": "unknown",
                        "origin": "0xaffeaffeaffeaffeaffeaffeaffeaffeaffeaffe",
                        "value": "0x0"
                    }, {
                        "address": "0x901d12ebe1b195e5aa8748e62bd7734ae19b51f",
                        "calldata": "0x546455b50000000000000000000000000000000000000000000000000000000000000017",
                        "input": "0x546455b50000000000000000000000000000000000000000000000000000000000000017",
                        "name": "assert3(uint256)",
                        "origin": "0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef",
                        "resolved_input": [23],
                        "value": "0x0"
                    }]
                }
            }, {
                "address": 731,
                "code": "assert(input_x > 10)",
                "contract": "Exceptions",
                "description": "An assertion violation was triggered.\nIt is possible to trigger an assertion violation. Note that Solidity assert() statements should only be used to check invariants. Review the transaction trace generated for this issue and either make sure your program logic is correct, or use require() instead of assert() if your goal is to constrain user inputs or enforce preconditions. Remember to validate inputs from both callers (for instance, via passed arguments) and callees (for instance, via return values).",
                "filename": "solidity_examples/exceptions.sol",
                "function": "assert5(uint256)",
                "lineno": 14,
                "max_gas_used": 1587,
                "min_gas_used": 1302,
                "severity": "Medium",
                "sourceMap": ":::i",
                "swc-id": "110",
                "title": "Exception State",
                "tx_sequence": {
                    "initialState": {
                        "accounts": {
                            "0xaffeaffeaffeaffeaffeaffeaffeaffeaffeaffe": {
                                "balance": "0x0",
                                "code": "",
                                "nonce": 0,
                                "storage": "{}"
                            },
                            "0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef": {
                                "balance": "0x0",
                                "code": "",
                                "nonce": 0,
                                "storage": "{}"
                            }
                        }
                    },
                    "steps": [{
                        "address": "",
                        "calldata": "",
                        "input": "0x6080604052600060085534801561001557600080fd5b506103f7806100256000396000f3fe608060405234801561001057600080fd5b50600436106100885760003560e01c8063b34c36101161005b578063b34c3610146100fd578063b630d70614610107578063e47b025314610123578063f44f13d81461012d57610088565b806301d4277c1461008d5780631d5d53dd146100a9578063546455b5146100c557806378375f14146100e1575b600080fd5b6100a760048036038101906100a29190610251565b610137565b005b6100c360048036038101906100be9190610251565b61015e565b005b6100df60048036038101906100da9190610251565b610181565b005b6100fb60048036038101906100f69190610251565b610196565b005b6101056101a7565b005b610121600480360381019061011c9190610251565b6101c1565b005b61012b6101e0565b005b6101356101fc565b005b600881101561015b5760008082600881106101555761015461027e565b5b01549050505b50565b60026008541161016d57600080fd5b600a811161017e5761017d6102ad565b5b50565b6017811415610193576101926102ad565b5b50565b60178114156101a457600080fd5b50565b600060019050600081146101be576101bd6102ad565b5b50565b60008111156101dd5760008160016101d9919061033a565b9050505b50565b6001600860008282546101f3919061036b565b92505081905550565b60006001905060008111610213576102126102ad565b5b50565b600080fd5b6000819050919050565b61022e8161021b565b811461023957600080fd5b50565b60008135905061024b81610225565b92915050565b60006020828403121561026757610266610216565b5b60006102758482850161023c565b91505092915050565b7f4e487b7100000000000000000000000000000000000000000000000000000000600052603260045260246000fd5b7f4e487b7100000000000000000000000000000000000000000000000000000000600052600160045260246000fd5b7f4e487b7100000000000000000000000000000000000000000000000000000000600052601260045260246000fd5b7f4e487b7100000000000000000000000000000000000000000000000000000000600052601160045260246000fd5b60006103458261021b565b91506103508361021b565b9250826103605761035f6102dc565b5b828204905092915050565b60006103768261021b565b91506103818361021b565b9250827fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff038211156103b6576103b561030b565b5b82820190509291505056fea2646970667358221220b474c01fa60d997027e1ceb779bcb2b34b6752282e0ea3a038a08b889fe0163f64736f6c634300080c0033",
                        "name": "unknown",
                        "origin": "0xaffeaffeaffeaffeaffeaffeaffeaffeaffeaffe",
                        "value": "0x0"
                    }, {
                        "address": "0x901d12ebe1b195e5aa8748e62bd7734ae19b51f",
                        "calldata": "0xe47b0253",
                        "input": "0xe47b0253",
                        "name": "counter_increase()",
                        "origin": "0xaffeaffeaffeaffeaffeaffeaffeaffeaffeaffe",
                        "resolved_input": null,
                        "value": "0x0"
                    }, {
                        "address": "0x901d12ebe1b195e5aa8748e62bd7734ae19b51f",
                        "calldata": "0xe47b0253",
                        "input": "0xe47b0253",
                        "name": "counter_increase()",
                        "origin": "0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef",
                        "resolved_input": null,
                        "value": "0x0"
                    }, {
                        "address": "0x901d12ebe1b195e5aa8748e62bd7734ae19b51f",
                        "calldata": "0xe47b0253",
                        "input": "0xe47b0253",
                        "name": "counter_increase()",
                        "origin": "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
                        "resolved_input": null,
                        "value": "0x0"
                    }, {
                        "address": "0x901d12ebe1b195e5aa8748e62bd7734ae19b51f",
                        "calldata": "0x1d5d53dd0000000000000000000000000000000000000000000000000000000000000003",
                        "input": "0x1d5d53dd0000000000000000000000000000000000000000000000000000000000000003",
                        "name": "assert5(uint256)",
                        "origin": "0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef",
                        "resolved_input": [3],
                        "value": "0x0"
                    }]
                }
            }],
            "success": true
        }

We can observe that the "resolved_input" field for the final transaction resolves to ``[3]``. Although this resolution
fails in some circumstances where output generated by Mythril is although executable on the bytecode, it cannot be decoded due 
to not being a valid ABI.

There are interesting options such as ``--execution-timeout <seconds>`` and ``--solver-timeout <milliseconds>`` 
which can be increased for better results. The default execution-timeout and solver-timeout are 86400 seconds and
25000 milliseconds respectively.





********************************************************
Executing Mythril on Contracts with Imports
********************************************************

When using Mythril to analyze a Solidity contract, you may encounter issues related to import statements. Solidity does not have access to the import locations, which can result in errors when compiling the program. In order to provide import information to Solidity, you can use the remappings option in Mythril.

Consider the following Solidity contract, which imports the PRC20 contract from the ``@openzeppelin/contracts/token/PRC20/PRC20.sol`` file:


    .. code-block:: solidity

        import "@openzeppelin/contracts/token/PRC20/PRC20.sol";

        contract Nothing is PRC20{
            string x_0 = "";

            bytes3 x_1 = "A";

            bytes5 x_2 = "E";

            bytes5 x_3 = "";

            bytes3 x_4 = "I";

            bytes3 x_5 = "U";

            bytes3 x_6 = "O";

            bytes3 x_7 = "0";

            bytes3 x_8 = "U";

            bytes3 x_9 = "U";
            function stringCompare(string memory a, string memory b) internal pure returns (bool) {
                if(bytes(a).length != bytes(b).length) {
                    return false;
                } else {
                    return keccak256(bytes(a)) == keccak256(bytes(b));
                }
            }

            function nothing(string memory g_0, bytes3 g_5, bytes3 g_6, bytes3 g_7, bytes3 g_8, bytes3 g_9, bytes3 g_10, bytes3 g_11) public view returns (bool){
                if (!stringCompare(g_0, x_0)) return false;
                        
                        
                if (g_5 != x_5) return false;
                        
                if (g_6 != x_6) return false;
                        
                if (g_7 != x_7) return false;
                        
                if (g_8 != x_8) return false;
                        
                if (g_9 != x_9) return false;
                
                if (g_10 != x_9) return false;

                if (g_11 != x_9) return false;

                return true;

            }
        }


When this contract is directly executed by using the following command:

    .. code-block:: bash

        $ myth analyze <file_path>

We encounter the following error:

    .. code-block:: none

        mythril.interfaces.cli [ERROR]: Solc experienced a fatal error.

        ParserError: Source "@openzeppelin/contracts/token/PRC20/PRC20.sol" not found: File not found. Searched the following locations: "".
        --> <file_path>:1:1:
        |
        1 | import "@openzeppelin/contracts/token/PRC20/PRC20.sol";
        | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^


This error occurs because Solidity cannot locate the ``PRC20.sol`` file. 
To solve this issue, you need to provide remapping information to Mythril, which will relay it to the Solidity compiler. 
Remapping involves mapping an import statement to the path that contains the corresponding file.

In this example, we can map the import statement ``@openzeppelin/contracts/token/PRC20/`` to the path that contains ``PRC20.sol``. Let's assume that the file is located at ``node_modules/PRC20/PRC20.sol``. We can provide the remapping information to Mythril in a JSON file like this:


    .. code-block:: json

        {
        "remappings": [ "@openzeppelin/contracts/token/PRC20/=node_modules/PRC20/"]
        }

This JSON file maps the prefix ``@openzeppelin/contracts/token/PRC20/`` to the path ``node_modules/PRC20/`` in the file system. 
When you run Mythril, you can use the ``--solc-json`` option to provide the remapping file:


    .. code-block:: bash

        $ myth analyze {file_path} --solc-json {json_file_path}


With this command, Mythril will be able to locate the ``PRC20.sol`` file, and the analysis should proceed without errors. 

For more information on remappings, you can refer to the `Solidity documentation <https://docs.soliditylang.org/en/v0.8.14/using-the-compiler.html#base-path-and-import-remapping>`_.

********************************************************
Executing Mythril by Restricting Transaction Sequences
********************************************************
Mythril is a security analysis tool that can be used to search certain transaction sequences. 
The `--transaction-sequences` argument can be used to direct the search. 
You should provide a list of transactions that are sequenced in the same order that they will be executed in the contract.
For example, suppose you want to find vulnerabilities in a contract that executes three transactions, where the first transaction is constrained with ``func_hash1`` and ``func_hash2``, 
the second transaction is constrained with ``func_hash2`` and ``func_hash3``, and the final transaction is unconstrained on any function. You would provide ``--transaction-sequences [[func_hash1,func_hash2], [func_hash2,func_hash3],[]]`` as an argument to Mythril.

You can use ``-1`` as a proxy for the hash of the `fallback()` function and ``-2`` as a proxy for the hash of the ``receive()`` function.

Here is an example contract that demonstrates how to use Mythril with ``--transaction-sequences``.

Consider the following contract:




    .. code-block:: solidity

        pragma solidity ^0.5.0;


        contract Rubixi {
            //Declare variables for storage critical to contract
            uint private balance = 0;
            uint private collectedFees = 0;
            uint private feePercent = 10;
            uint private pyramidMultiplier = 300;
            uint private payoutOrder = 0;

            address payable private creator;

            modifier onlyowner {
                if (msg.sender == creator) _;
            }

            struct Participant {
                address payable etherAddress;
                uint payout;
            }

            //Fallback function
            function() external payable {
                init();
            }

            //Sets creator
            function dynamicPyramid() public {
                creator = msg.sender;
            }

            Participant[] private participants;

            //Fee functions for creator
            function collectAllFees() public onlyowner {
                require(collectedFees > 0);
                creator.transfer(collectedFees);
                collectedFees = 0;
            }

            function collectFeesInEther(uint _amt) public onlyowner {
                _amt *= 1 ether;
                if (_amt > collectedFees) collectAllFees();

                require(collectedFees > 0);

                creator.transfer(_amt);
                collectedFees -= _amt;
            }

            function collectPercentOfFees(uint _pcent) public onlyowner {
                require(collectedFees > 0 && _pcent <= 100);

                uint feesToCollect = collectedFees / 100 * _pcent;
                creator.transfer(feesToCollect);
                collectedFees -= feesToCollect;
            }

            //Functions for changing variables related to the contract
            function changeOwner(address payable _owner) public onlyowner {
                creator = _owner;
            }

            function changeMultiplier(uint _mult) public onlyowner {
                require(_mult <= 300 &&  _mult >= 120);
                pyramidMultiplier = _mult;
            }

            function changeFeePercentage(uint _fee) public onlyowner {
                require(_fee <= 10);
                feePercent = _fee;
            }

            //Functions to provide information to end-user using JSON interface or other interfaces
            function currentMultiplier() public view returns (uint multiplier, string memory info) {
                multiplier = pyramidMultiplier;
                info = "This multiplier applies to you as soon as transaction is received, may be lowered to hasten payouts or increased if payouts are fast enough. Due to no float or decimals, multiplier is x100 for a fractional multiplier e.g. 250 is actually a 2.5x multiplier. Capped at 3x max and 1.2x min.";
            }

            function currentFeePercentage() public view returns (uint fee, string memory info) {
                fee = feePercent;
                info = "Shown in % form. Fee is halved(50%) for amounts equal or greater than 50 ethers. (Fee may change, but is capped to a maximum of 10%)";
            }

            function currentPyramidBalanceApproximately() public view returns (uint pyramidBalance, string memory info) {
                pyramidBalance = balance / 1 ether;
                info = "All balance values are measured in Ethers, note that due to no decimal placing, these values show up as integers only, within the contract itself you will get the exact decimal value you are supposed to";
            }

            function nextPayoutWhenPyramidBalanceTotalsApproximately() public view returns (uint balancePayout) {
                balancePayout = participants[payoutOrder].payout / 1 ether;
            }

            function feesSeperateFromBalanceApproximately() public view returns (uint fees) {
                fees = collectedFees / 1 ether;
            }

            function totalParticipants() public view returns (uint count) {
                count = participants.length;
            }

            function numberOfParticipantsWaitingForPayout() public view returns (uint count) {
                count = participants.length - payoutOrder;
            }

            function participantDetails(uint orderInPyramid) public view returns (address addr, uint payout) {
                if (orderInPyramid <= participants.length) {
                    addr = participants[orderInPyramid].etherAddress;
                    payout = participants[orderInPyramid].payout / 1 ether;
                }
            }

            //init function run on fallback
            function init() private {
                //Ensures only tx with value of 1 ether or greater are processed and added to pyramid
                if (msg.value < 1 ether) {
                    collectedFees += msg.value;
                    return;
                }

                uint _fee = feePercent;
                // 50% fee rebate on any ether value of 50 or greater
                if (msg.value >= 50 ether) _fee /= 2;

                addPayout(_fee);
            }

            //Function called for valid tx to the contract
            function addPayout(uint _fee) private {
                //Adds new address to participant array
                participants.push(Participant(msg.sender, (msg.value * pyramidMultiplier) / 100));

                // These statements ensure a quicker payout system to
                // later pyramid entrants, so the pyramid has a longer lifespan
                if (participants.length == 10) pyramidMultiplier = 200;
                else if (participants.length == 25) pyramidMultiplier = 150;

                // collect fees and update contract balance
                balance += (msg.value * (100 - _fee)) / 100;
                collectedFees += (msg.value * _fee) / 100;

                //Pays earlier participiants if balance sufficient
                while (balance > participants[payoutOrder].payout) {
                    uint payoutToSend = participants[payoutOrder].payout;
                    participants[payoutOrder].etherAddress.transfer(payoutToSend);

                    balance -= participants[payoutOrder].payout;
                    payoutOrder += 1;
                }
            }
        }


Since this contract has ``16`` functions, it is infeasible to execute uninteresting functions such as ``feesSeperateFromBalanceApproximately()``.
To successfully explore useful transaction sequences we can use Mythril's ``--transaction-sequences`` argument.

.. code-block:: bash

    $ myth analyze rubixi.sol -t 3 --transaction-sequences [["0x89b8ae9b"],[-1],["0x686f2c90","0xb4022950","0x4229616d"]]

The first transaction is constrained to the function ``dynamicPyramid()``, the second one to the ``fallback()`` function, and finally, the third transaction is constrained to``collectAllFees()``, ``collectFeesInEther(uint256)`` and ``collectPercentOfFees(uint256)``.
Make sure to use ``-t 3`` argument, since the length of the transaction sequence should match with the transaction count argument.
