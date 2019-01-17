# Analysis results for test-filename.sol

## Unprotected Ether Withdrawal
- SWC ID: 105
- Severity: High
- Contract: Unknown
- Function name: `transfer()`
- PC address: 142
- Estimated Gas Usage: 186 - 467

### Description

Anyone can withdraw ETH from the contract account.
Arbitrary senders other than the contract creator can withdraw ETH from the contract account without previously having sent an equivalent amount of ETH to it. This is likely to be a vulnerability.
