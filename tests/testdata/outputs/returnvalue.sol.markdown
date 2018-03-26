# Analysis Results
## Message call to external contract
- Type: Informational
- Contract: ReturnValue
- Function name: `_function_0x633ab5e0`
- PC address: 196

### Description
This contract executes a message call to to another contract. Make sure that the called contract is trusted and does not execute user-supplied code.

In *<TEST_FILES>/inputs/returnvalue.sol:10*

```
callee.call()
```
## Message call to external contract
- Type: Informational
- Contract: ReturnValue
- Function name: `_function_0xe3bea282`
- PC address: 285

### Description
This contract executes a message call to to another contract. Make sure that the called contract is trusted and does not execute user-supplied code.

In *<TEST_FILES>/inputs/returnvalue.sol:6*

```
callee.call()
```
## Unchecked CALL return value
- Type: Informational
- Contract: ReturnValue
- Function name: `_function_0xe3bea282`
- PC address: 285

### Description
The return value of an external call is not checked. Note that execution continue even if the called contract throws.

In *<TEST_FILES>/inputs/returnvalue.sol:6*

```
callee.call()
```
