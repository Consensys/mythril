# Analysis Results
## Ether send
- Type: Warning
- Contract: Transfer2
- Function name: `_function_0x8a4068dd`
- PC address: 142

### Description
In the function '_function_0x8a4068dd' a non-zero amount of Ether is sent to msg.sender.
It seems that this function can be called without restrictions.

In *<TESTDATA>/inputs/multi_contracts.sol:14*

```
msg.sender.transfer(2 ether)
```
