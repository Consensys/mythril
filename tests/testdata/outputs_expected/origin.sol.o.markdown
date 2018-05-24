# Analysis results for test-filename.sol

## Use of tx.origin

- Type: Warning
- Contract: Unknown
- Function name: `transferOwnership(address)`
- PC address: 317

### Description

Function transferOwnership(address) retrieves the transaction origin (tx.origin) using the ORIGIN opcode. Use tx.sender instead.
See also: https://solidity.readthedocs.io/en/develop/security-considerations.html#tx-origin
