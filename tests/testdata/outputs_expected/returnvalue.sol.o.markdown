# Analysis results for test-filename.sol

## External Call To Fixed Address
- SWC ID: 107
- Severity: Low
- Contract: Unknown
- Function name: `callchecked()`
- PC address: 196
- Estimated Gas Usage: 599 - 1210

### Description

The contract executes an external message call.
An external function call to a fixed contract address is executed. Make sure that the callee contract has been reviewed carefully.

## External Call To Fixed Address
- SWC ID: 107
- Severity: Low
- Contract: Unknown
- Function name: `callnotchecked()`
- PC address: 285
- Estimated Gas Usage: 621 - 1232

### Description

The contract executes an external message call.
An external function call to a fixed contract address is executed. Make sure that the callee contract has been reviewed carefully.

## Unchecked Call Return Value
- SWC ID: 104
- Severity: Low
- Contract: Unknown
- Function name: `callnotchecked()`
- PC address: 285
- Estimated Gas Usage: 1339 - 35950

### Description

The return value of a message call is not checked.
External calls return a boolean value. If the callee contract halts with an exception, 'false' is returned and execution continues in the caller. It is usually recommended to wrap external calls into a require statement to prevent unexpected states.
