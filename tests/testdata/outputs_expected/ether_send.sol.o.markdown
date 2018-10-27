# Analysis results for test-filename.sol

## Ether send
- SWC ID: 105
- Type: Warning
- Contract: Unknown
- Function name: `_function_0x6c343ffe`
- PC address: 722

### Description

In the function `_function_0x6c343ffe` a non-zero amount of Ether is sent to msg.sender.

There is a check on storage index 1. This storage slot can be written to by calling the function `_function_0x56885cd8`.

## Integer Overflow
- SWC ID: 101
- Type: Warning
- Contract: Unknown
- Function name: `_function_0xe8b5e51f`
- PC address: 883

### Description

The arithmetic operation can result in integer overflow.
