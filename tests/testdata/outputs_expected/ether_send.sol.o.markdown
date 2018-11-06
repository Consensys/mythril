# Analysis results for test-filename.sol

## Ether send
- SWC ID: 105
- Type: Warning
- Contract: Unknown
- Function name: `withdrawfunds()`
- PC address: 722
- Estimated Gas Usage: 929 - 1540

### Description

It seems that an attacker is able to execute an call instruction, this can mean that the attacker is able to extract funds out of the contract.

## Integer Overflow
- SWC ID: 101
- Type: Warning
- Contract: Unknown
- Function name: `invest()`
- PC address: 883
- Estimated Gas Usage: 950 - 1283

### Description

The arithmetic operation can result in integer overflow.
