# Analysis results for test-filename.sol

## Use of tx.origin is deprecated.
- SWC ID: 111
- Severity: Medium
- Contract: Unknown
- Function name: `transferOwnership(address)`
- PC address: 317
- Estimated Gas Usage: 626 - 1051

### Description

Use of tx.origin is deprecated.
The function `transferOwnership(address)` retrieves the transaction origin (tx.origin) using the ORIGIN opcode. Use msg.sender instead.
See also: https://solidity.readthedocs.io/en/develop/security-considerations.html#tx-origin
