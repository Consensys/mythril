# Analysis Results
## Ether send
- Type: Warning
- Contract: Transfer2
- Function name: `transfer()`
- PC address: 142

### Description
In the function 'transfer()' a non-zero amount of Ether is sent to msg.sender.
It seems that this function can be called without restrictions.

In *<TEST_FILES>/multi_contracts.sol:14*

```
msg.sender.transfer(2 ether)
```
