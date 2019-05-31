# Analysis results for test-filename.sol

## Unprotected Ether Withdrawal
- SWC ID: 105
- Severity: High
- Contract: Unknown
- Function name: `withdrawfunds()`
- PC address: 722
- Estimated Gas Usage: 1138 - 1749

### Description

Anyone can withdraw ETH from the contract account.
Arbitrary senders other than the contract creator can withdraw ETH from the contract account without previously having sent an equivalent amount of ETH to it. This is likely to be a vulnerability.

## Integer Overflow
- SWC ID: 101
- Severity: High
- Contract: Unknown
- Function name: `invest()`
- PC address: 883
- Estimated Gas Usage: 6598 - 26883

### Description

The binary addition can overflow.
The operands of the addition operation are not sufficiently constrained. The addition could therefore result in an integer overflow. Prevent the overflow by checking inputs or ensure sure that the overflow is caught by an assertion.
