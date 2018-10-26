# Analysis results for test-filename.sol

## Message call to external contract
- SWC ID: 107
- Type: Informational
- Contract: Unknown
- Function name: `callchecked()`
- PC address: 196

### Description

This contract executes a message call to to another contract. Make sure that the called contract is trusted and does not execute user-supplied code.

## Message call to external contract
- SWC ID: 107
- Type: Informational
- Contract: Unknown
- Function name: `callnotchecked()`
- PC address: 285

### Description

This contract executes a message call to to another contract. Make sure that the called contract is trusted and does not execute user-supplied code.

## Unchecked CALL return value
- SWC ID: 104
- Type: Informational
- Contract: Unknown
- Function name: `callnotchecked()`
- PC address: 290

### Description

The return value of an external call is not checked. Note that execution continue even if the called contract throws.
