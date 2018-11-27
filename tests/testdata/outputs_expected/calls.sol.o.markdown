# Analysis results for test-filename.sol

## Unchecked CALL return value
- SWC ID: 104
- Type: Informational
- Contract: Unknown
- Function name: `thisisfine()`
- PC address: 666
- Estimated Gas Usage: 1352 - 35963

### Description

The return value of an external call is not checked. Note that execution continue even if the called contract throws.

## Unchecked CALL return value
- SWC ID: 104
- Type: Informational
- Contract: Unknown
- Function name: `callstoredaddress()`
- PC address: 784
- Estimated Gas Usage: 1396 - 36007

### Description

The return value of an external call is not checked. Note that execution continue even if the called contract throws.

## Unchecked CALL return value
- SWC ID: 104
- Type: Informational
- Contract: Unknown
- Function name: `reentrancy()`
- PC address: 871
- Estimated Gas Usage: 6432 - 61043

### Description

The return value of an external call is not checked. Note that execution continue even if the called contract throws.

## Message call to external contract
- SWC ID: 107
- Type: Warning
- Contract: Unknown
- Function name: `calluseraddress(address)`
- PC address: 912
- Estimated Gas Usage: 335 - 616

### Description

This contract executes a message call to an address provided as a function argument. Generally, it is not recommended to call user-supplied addresses using Solidity's call() construct. Note that attackers might leverage reentrancy attacks to exploit race conditions or manipulate this contract's state.

## Unchecked CALL return value
- SWC ID: 104
- Type: Informational
- Contract: Unknown
- Function name: `calluseraddress(address)`
- PC address: 918
- Estimated Gas Usage: 1046 - 35327

### Description

The return value of an external call is not checked. Note that execution continue even if the called contract throws.
