# Analysis results for test-filename.sol

## Unchecked SUICIDE
- SWC ID: 106
- Type: Warning
- Contract: Unknown
- Function name: `kill(address)`
- PC address: 146
- Estimated Gas Usage: 168 - 263

### Description

A reachable SUICIDE instruction was detected. The remaining Ether is sent to an address provided as a function argument.
