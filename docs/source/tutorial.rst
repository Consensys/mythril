Tutorial
======================

******************************************
Executing Mythril on Simple Contracts
******************************************

We consider a contract simple if it does not have any imports, like the following contract:

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

We can execute such a contract by directly using the following command:

    .. code-block:: bash

        $ myth analyze <file_path>

This execution can give the following output:

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


We can observe that the function ``assert5(uint256)`` should have an assertion failure 
with the assertion ``assert(input_x > 10)`` which is missing from our output. This can be attributed to
Mythril's default configuration of running three transactions. We can increase the transaction count to 4
using the ``-t <tx_count>``.

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

Consider the following contract:

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

            function nothing(string memory g_0, bytes3 g_1, bytes5 g_2, bytes5 g_3, bytes3 g_4, bytes3 g_5, bytes3 g_6, bytes3 g_7, bytes3 g_8, bytes3 g_9, bytes3 g_10, bytes3 g_11) public view returns (bool){
                if (!stringCompare(g_0, x_0)) return false;
                        
                if (g_1 != x_1) return false;
                        
                if (g_2 != x_2) return false;
                        
                if (g_3 != x_3) return false;
                        
                if (g_4 != x_4) return false;
                        
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


When this contract is directly executed, by using the following command:

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

This is because Mythril uses Solidity to compile the program, to circumvent this issue we can use the following solc-json file:

    .. code-block:: json

        {
        "remappings": [ "@openzeppelin/contracts/token/PRC20/=node_modules/PRC20" ],
        }

Here we are mapping the import ``@openzeppelin/contracts/token/PRC20/`` to the path which contains ``PRC20.sol`` which in this case
is ``node_modules/PRC20``. This instructs the compiler to search for anything with the prefix ``@openzeppelin/contracts/token/PRC20/` `
in the path ``node_modules/PRC20`` in our file system. We feed to file to Mythril using ``--solc-json`` argument.

    .. code-block:: bash

        $ myth analyze {file_path} --solc-json {json_file_path}


This can effectively execute the file since the Solidity compiler can locate `PRC20.sol`. For more information on remappings, you can
refer to `Solc docs <https://docs.soliditylang.org/en/v0.8.14/using-the-compiler.html#base-path-and-import-remapping>`_.