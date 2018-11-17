# Analysis results for test-filename.sol

## Ether thief
- SWC ID: 105
- Type: Warning
- Contract: Unknown
- Function name: `_function_0x8a4068dd`
- PC address: 142
- Estimated Gas Usage: 186 - 467

### Description

Arbitrary senders other than the contract creator can withdraw ETH from the contract account without previously having sent an equivalent amount of ETH to it. This is likely to be a vulnerability.
