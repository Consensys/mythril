# Analysis results for test-filename.sol

## Unchecked SUICIDE

- Type: Warning
- Contract: Unknown
- Function name: `_function_0xcbf0b0c0`
- PC address: 146

### Description

The function `_function_0xcbf0b0c0` executes the SUICIDE instruction. The remaining Ether is sent to an address provided as a function argument.

It seems that this function can be called without restrictions.