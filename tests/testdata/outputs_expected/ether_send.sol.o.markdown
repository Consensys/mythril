# Analysis results for test-filename.sol

## Ether thief
- SWC ID: 105
- Type: Warning
- Contract: Unknown
- Function name: `withdrawfunds()`
- PC address: 722
- Estimated Gas Usage: 1138 - 1749

### Description

Users other than the contract creator can withdraw ETH from the contract account without previously having sent any ETH to it. This is likely to be vulnerability.

## Integer Overflow
- SWC ID: 101
- Type: Warning
- Contract: Unknown
- Function name: `invest()`
- PC address: 883
- Estimated Gas Usage: 1943 - 2228

### Description

This binary add operation can result in integer overflow.
