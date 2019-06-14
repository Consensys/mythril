# Analysis results for test-filename.sol

## Integer Overflow
- SWC ID: 101
- Severity: High
- Contract: Unknown
- Function name: `sendToken(address,uint256)`
- PC address: 498
- Estimated Gas Usage: 11860 - 52806

### Description

The binary addition can overflow.
The operands of the addition operation are not sufficiently constrained. The addition could therefore result in an integer overflow. Prevent the overflow by checking inputs or ensure sure that the overflow is caught by an assertion.
