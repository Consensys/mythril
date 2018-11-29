# Analysis results for test-filename.sol

## External call
- SWC ID: 107
- Type: Informational
- Contract: Unknown
- Function name: `callchecked()`
- PC address: 196
- Estimated Gas Usage: 599 - 1210

### Description

The contract executes a function call to an external address. Verify that the code at this address is trusted and immutable.

## External call
- SWC ID: 107
- Type: Informational
- Contract: Unknown
- Function name: `callnotchecked()`
- PC address: 285
- Estimated Gas Usage: 621 - 1232

### Description

The contract executes a function call to an external address. Verify that the code at this address is trusted and immutable.

## Unchecked CALL return value
- SWC ID: 104
- Type: Informational
- Contract: Unknown
- Function name: `callnotchecked()`
- PC address: 290
- Estimated Gas Usage: 1330 - 35941

### Description

The return value of an external call is not checked. Note that execution continue even if the called contract throws.
