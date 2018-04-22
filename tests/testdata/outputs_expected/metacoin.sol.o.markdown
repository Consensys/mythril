# Analysis results for <TESTDATA>/inputs/metacoin.sol

## Integer Overflow 

- Type: Warning
- Contract: Unknown
- Function name: `sendToken(address,uint256)`
- PC address: 498

### Description

A possible integer overflow exists in the function `sendToken(address,uint256)`.
The addition or multiplication may result in a value higher than the maximum representable integer.
In *<TESTDATA>/inputs/metacoin.sol:12*

```
balances[receiver] += amount
```
