# Analysis Results
## Ether send
- Type: Warning
- Contract: Crowdfunding
- Function name: `withdrawfunds()`
- PC address: 816

### Description
In the function 'withdrawfunds()' a non-zero amount of Ether is sent to msg.sender.

There is a check on storage index 7. This storage slot can be written to by calling the function 'crowdfunding()'.

In *<TEST_FILES>/ether_send.sol:18*

```
msg.sender.transfer(this.balance)
```
