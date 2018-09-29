# Analysis results for test-filename.sol

## Ether send
- SWC ID: 105
- Type: Warning
- Contract: Unknown
- Function name: `_function_0x8a4068dd`
- PC address: 142

### Description

In the function `_function_0x8a4068dd` a non-zero amount of Ether is sent to msg.sender.
It seems that this function can be called without restrictions.
