# Mythril Detection Capabilities

Detection modules, ideas collection and wish list. Contributions are welcome!

| Issue | Description | Mythril Detection Module(s) | References |
|------:|-------------|------------|----------|
|Unprotected functions| Critical functions such as sends with non-zero value or suicide() calls are callable by anyone, or msg.sender is compared against an address in storage that can be written to. E.g. Parity wallet bugs. | [unchecked_suicide](mythril/analysis/modules/suicide.py), [ether_send](mythril/analysis/modules/ether_send.py)          | |
|Missing check on CALL return value|  | [unchecked_retval](mythril/analysis/modules/unchecked_retval.py) | [Handle errors in external calls](https://consensys.github.io/smart-contract-best-practices/recommendations/#use-caution-when-making-external-calls) |
|Re-entrancy| Contract state should never be relied on if untrusted contracts are called. State changes after external calls should be avoided. | [external calls to untrusted contracts](mythril/analysis/modules/external_calls.py) | [Call external functions last](https://consensys.github.io/smart-contract-best-practices/known_attacks/#reentrancy) [Avoid state changes after external calls](https://consensys.github.io/smart-contract-best-practices/recommendations/#avoid-state-changes-after-external-calls)|
|Multiple sends in a single transaction| External calls can fail accidentally or deliberately. Avoid combining multiple send() calls in a single transaction. |           |   [Favor pull over push for external calls](https://consensys.github.io/smart-contract-best-practices/recommendations/#favor-pull-over-push-for-external-calls) |
|External call to untrusted contract|       |           [external call to untrusted contract](mythril/analysis/modules/call_to_dynamic_with_gas.py) | |
|Delegatecall or callcode to untrusted contract|                   | [delegatecall_forward](mythril/analysis/modules/delegatecall.py) |  |
|Integer overflow/underflow|                | [integer_underflow](mythril/analysis/modules/integer.py)   | [Validate arithmetic](https://consensys.github.io/smart-contract-best-practices/known_attacks/#integer-overflow-and-underflow) |
|Timestamp dependence|                      | [Dependence on predictable variables](mythril/analysis/modules/dependence_on_predictable_vars.py)  | [Miner time manipulation](https://consensys.github.io/smart-contract-best-practices/known_attacks/#timestamp-dependence) |
|Payable transaction does not revert in case of failure | | |   |
|Use of `tx.origin`|                        | [tx_origin](mythril/analysis/modules/depreciated_ops.py)       | [Solidity documentation](https://solidity.readthedocs.io/en/develop/security-considerations.html#tx-origin), [Avoid using tx.origin](https://consensys.github.io/smart-contract-best-practices/recommendations/#avoid-using-txorigin) |
|Type confusion|                            |           |  |
|Predictable RNG|                           | [Dependence on predictable variables](mythril/analysis/modules/dependence_on_predictable_vars.py) | |
|Transaction order dependence|              |           | [Front Running](https://consensys.github.io/smart-contract-best-practices/known_attacks/#transaction-ordering-dependence-tod-front-running) |
|Information exposure|                      |           |   |
|Complex fallback function (uses more than 2,300 gas) | A too complex fallback function will cause send() and transfer() from other contracts to fail. To implement this we first need to fully implement gas simulation. | | 
|Use require() instead of assert() | Use `assert()` only to check against states which should be completely unreachable.  | [Exceptions](mythril/analysis/modules/exceptions.py)          | [Solidity docs](https://solidity.readthedocs.io/en/develop/control-structures.html#error-handling-assert-require-revert-and-exceptions)|
|Use of depreciated functions | Use `revert()` instead of `throw()`, `selfdestruct()` instead of `suicide()`, `keccak256()` instead of `sha3()` |           | |
|Detect tautologies| Detect comparisons that always evaluate to 'true', see also [#54](https://github.com/ConsenSys/mythril/issues/54) |  |
|Call depth attack| Depreciated             |           | [EIP 150 Hard Fork](https://consensys.github.io/smart-contract-best-practices/known_attacks/#call-depth-attack-deprecated)|

