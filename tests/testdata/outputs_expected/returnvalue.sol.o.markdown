# Analysis results for test-filename.sol

## External Call To User-Supplied Address
- SWC ID: 107
- Severity: Medium
- Contract: Unknown
- Function name: `callchecked()`
- PC address: 196
- Estimated Gas Usage: 599 - 1210

### Description

A call to a user-supplied address is executed.
The callee address of an external message call can be set by the caller. Note that the callee can contain arbitrary code and may re-enter any function in this contract. Review the business logic carefully to prevent averse effects on the contract state.

### Transaction Sequence

Caller: [ATTACKER], data: 0x633ab5e0, value: 0x0


## External Call To User-Supplied Address
- SWC ID: 107
- Severity: Medium
- Contract: Unknown
- Function name: `callnotchecked()`
- PC address: 285
- Estimated Gas Usage: 621 - 1232

### Description

A call to a user-supplied address is executed.
The callee address of an external message call can be set by the caller. Note that the callee can contain arbitrary code and may re-enter any function in this contract. Review the business logic carefully to prevent averse effects on the contract state.

### Transaction Sequence

Caller: [ATTACKER], data: 0xe3bea282, value: 0x0


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

