# Analysis Results
## Integer Underflow
- Type: Warning
- Contract: Under
- Function name: `sendeth(address,uint256)`
- PC address: 649

### Description
A possible integer underflow exists in the function sendeth(address,uint256).
The substraction may result in a value < 0.

In *<TEST_FILES>/underflow.sol:12*

```
balances[msg.sender] -= _value
```
## Integer Underflow
- Type: Warning
- Contract: Under
- Function name: `sendeth(address,uint256)`
- PC address: 567

### Description
A possible integer underflow exists in the function sendeth(address,uint256).
The substraction may result in a value < 0.

In *<TEST_FILES>/underflow.sol:11*

```
balances[msg.sender] - _value
```
