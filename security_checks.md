# Smart Contract Security Issues

| Issue | Description | Mythril Detection Module(s) | References |
|------:|-------------|------------|----------|
|Unprotected functions| Critical functions such as sends with non-zero value or suicide() calls are callable by anyone, or msg.sender is compared against an address in storage that can be written to. E.g. Parity wallet bugs. | [unchecked_suicide](mythril/analysis/modules/unchecked_suicide.py), [ether_send](mythril/analysis/modules/ether_send.py)          | |
|Missing check on CALL return value|  | [unchecked_retval](mythril/analysis/modules/unchecked_retval.py) | [Handle errors in external calls](https://consensys.github.io/smart-contract-best-practices/recommendations/#use-caution-when-making-external-calls) |
|Re-entrancy|                        | [call to untrusted contract with gas](mythril/analysis/modules/call_to_dynamic_with_gas.py) | [Call external functions last](https://consensys.github.io/smart-contract-best-practices/known_attacks/#reentrancy) |
|Multiple sends in a single transaction| External calls can fail accidentally or deliberately. Avoid combining multiple send() calls in a single transaction. |           |   [Favor pull over push for external calls](https://consensys.github.io/smart-contract-best-practices/recommendations/#favor-pull-over-push-for-external-calls) |
|Function call to untrusted contract|       |           [call to untrusted contract with gas](mythril/analysis/modules/call_to_dynamic_with_gas.py) | |
|Delegatecall or callcode to untrusted contract|                   | [delegatecall_forward](mythril/analysis/modules/delegatecall_forward.py), [delegatecall_to_dynamic.py](mythril/analysis/modules/delegatecall_to_dynamic.py) |  |
|Integer overflow/underflow|                | [integer_underflow](mythril/analysis/modules/integer_underflow.py)   | [Validate arithmetic](https://consensys.github.io/smart-contract-best-practices/known_attacks/#integer-overflow-and-underflow) |
|Timestamp dependence|                      |           | [Miner time manipulation](https://consensys.github.io/smart-contract-best-practices/known_attacks/#timestamp-dependence) |
|Payable transaction does not revert in case of failure | | |   |
|Use of `tx.origin`|                        | [tx_origin](mythril/analysis/modules/tx_origin.py)       | [Solidity documentation](https://solidity.readthedocs.io/en/develop/security-considerations.html#tx-origin), [Avoid using tx.origin](https://consensys.github.io/smart-contract-best-practices/recommendations/#avoid-using-txorigin) |
|Type confusion|                            |           |  |
|Predictable RNG|                           | [weak_random](mythril/analysis/modules/weak_random.py) | |
|Transaction order dependence|              |           | [Front Running](https://consensys.github.io/smart-contract-best-practices/known_attacks/#transaction-ordering-dependence-tod-front-running) |
|Information exposure|                      |           |   |
|Complex fallback function (uses more than 2,300 gas) | A too complex fallback function will cause send() and transfer() from other contracts to fail. To implement this we first need to fully implement gas simulation. | | 
|Call depth attack| Deprecated!             |           | [EIP 150 Hard Fork](https://consensys.github.io/smart-contract-best-practices/known_attacks/#call-depth-attack-deprecated)|
|User require() instead of assert() | Use `assert()` only to check against states which should be completely unreachable. This facilitates static analysis using solidity's built-in SMTChecker. For more information, refer to the documentation.        |           | [Solidity docs](https://solidity.readthedocs.io/en/develop/control-structures.html#error-handling-assert-require-revert-and-exceptions)|

