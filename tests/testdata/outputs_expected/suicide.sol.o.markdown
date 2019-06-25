# Analysis results for test-filename.sol

## Unprotected Selfdestruct
- SWC ID: 106
- Severity: High
- Contract: Unknown
- Function name: `kill(address)`
- PC address: 146
- Estimated Gas Usage: 168 - 263

### Description

The contract can be killed by anyone.
Anyone can kill this contract and withdraw its balance to an arbitrary address.

### Transaction Sequence

Caller: [ATTACKER], data: 0xcbf0b0c0bebebebebebebebebebebebedeadbeefdeadbeefdeadbeefdeadbeefdeadbeef, value: 0x0

