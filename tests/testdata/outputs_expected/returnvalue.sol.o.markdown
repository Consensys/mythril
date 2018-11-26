# Analysis results for test-filename.sol

## Unchecked CALL return value
- SWC ID: 104
- Type: Informational
- Contract: Unknown
- Function name: `callnotchecked()`
- PC address: 290
- Estimated Gas Usage: 1330 - 35941

### Description

The return value of an external call is not checked. Note that execution continue even if the called contract throws.
