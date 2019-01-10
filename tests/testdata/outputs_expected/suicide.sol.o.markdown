# Analysis results for test-filename.sol

## Unprotected Selfdestruct
- SWC ID: 106
- Severity: High
- Contract: Unknown
- Function name: `kill(address)`
- PC address: 146
- Estimated Gas Usage: 168 - 263

### Description

The contract can be killed by anyone.
Arbitrary senders can kill this contract and withdraw its balance to their own account.
