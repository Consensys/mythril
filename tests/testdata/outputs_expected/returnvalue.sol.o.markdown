# Analysis results for test-filename.sol

## Message call to external contract
- SWC ID: 107
- Type: Informational
- Contract: Unknown
- Function name: `_function_0x633ab5e0`
- PC address: 196
- Estimated Gas Usage: 390 - 1001

### Description

This contract executes a message call to to another contract. Make sure that the called contract is trusted and does not execute user-supplied code.

## Message call to external contract
- SWC ID: 107
- Type: Informational
- Contract: Unknown
- Function name: `_function_0xe3bea282`
- PC address: 285
- Estimated Gas Usage: 412 - 1023

### Description

This contract executes a message call to to another contract. Make sure that the called contract is trusted and does not execute user-supplied code.

## Unchecked CALL return value
- SWC ID: 104
- Type: Informational
- Contract: Unknown
- Function name: `_function_0xe3bea282`
- PC address: 290
- Estimated Gas Usage: 1121 - 35732

### Description

The return value of an external call is not checked. Note that execution continue even if the called contract throws.
