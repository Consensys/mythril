

## Integer Underflow

- Type: Warning
- Contract: Over
- Function name: `sendeth(address,uint256)`
- PC address: 649



### Description

A possible integer underflow exists in the function `sendeth(address,uint256)`.
The subtraction may result in a value < 0.

In *<TESTDATA>/inputs/overflow.sol:12*

```
balances[msg.sender] -= _value
```


## Integer Overflow 

- Type: Warning
- Contract: Over
- Function name: `sendeth(address,uint256)`
- PC address: 725



### Description

A possible integer overflow exists in the function `sendeth(address,uint256)`.
The addition may result in a value higher than the maximum representable integer.

In *<TESTDATA>/inputs/overflow.sol:13*

```
balances[_to] += _value
```


## Integer Underflow

- Type: Warning
- Contract: Over
- Function name: `sendeth(address,uint256)`
- PC address: 567



### Description

A possible integer underflow exists in the function `sendeth(address,uint256)`.
The subtraction may result in a value < 0.

In *<TESTDATA>/inputs/overflow.sol:11*

```
balances[msg.sender] - _value
```
