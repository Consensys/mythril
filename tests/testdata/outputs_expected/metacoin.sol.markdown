# Analysis Results
## Integer Overflow 
- Type: Warning
- Contract: metaCoin
- Function name: `sendToken(address,uint256)`
- PC address: 498

### Description
A possible integer overflow exists in the function sendToken(address,uint256).
 Addition may result in a lower value.

In *<TESTDATA>/inputs/metacoin.sol:12*

```
balances[receiver] += amount
```
