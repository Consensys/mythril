# Analysis results for test-filename.sol

## Use of tx.origin
- SWC ID: 115
- Type: Warning
- Contract: Unknown
- Function name: `_function_0xf2fde38b`
- PC address: 317

### Description

The function `_function_0xf2fde38b` retrieves the transaction origin (tx.origin) using the ORIGIN opcode. Use msg.sender instead.
See also: https://solidity.readthedocs.io/en/develop/security-considerations.html#tx-origin
