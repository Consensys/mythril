# Analysis results for test-filename.sol

## Ether send
- SWC ID: 105
- Type: Warning
- Contract: Unknown
- Function name: `withdrawfunds()`
- PC address: 722

### Description

A non-zero amount of Ether is sent to a user-supplied address. The target address is msg.sender.

There is a check on storage index 1. This storage slot can be written to by calling the function `crowdfunding()`.

## Integer Overflow
- SWC ID: 101
- Type: Warning
- Contract: Unknown
- Function name: `invest()`
- PC address: 883

### Description

The arithmetic operation can result in integer overflow.
