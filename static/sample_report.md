# Analysis Results
## Ether send
- Type: Warning
- Contract: Crowdfunding
- Function name: withdrawfunds()
- PC address: 816

### Description
In the function `withdrawfunds()` a non-zero amount of Ether is sent to msg.sender.
Call value is balance_at_1461501637330902918203684832716283019655932542975 & address.

There is a check on storage index 7. This storage slot can be written to by calling the function 'crowdfunding()'.

In *ether_send.sol:*

```
msg.sender.transfer(this.balance)
```
## Use of tx.origin
- Type: Warning
- Contract: Origin
- Function name: transferOwnership(address)
- PC address: 317

### Description
Function transferOwnership(address) retrieves the transaction origin (tx.origin) using the ORIGIN opcode. Use tx.sender instead.
See also: https://solidity.readthedocs.io/en/develop/security-considerations.html#tx-origin

In *origin.sol:*

```
tx.origin
```
## CALL with gas to dynamic address
- Type: Warning
- Contract: Reentrancy
- Function name: withdraw(uint256)
- PC address: 552

### Description
The function withdraw(uint256) contains a function call to the address of the transaction sender. The available gas is forwarded to the called contract. Make sure that the logic of the calling contract is not adversely affected if the called contract misbehaves (e.g. reentrancy).

In *reentrancy.sol:*

```
msg.sender.call.value(_amount)()
```
## Unchecked CALL return value
- Type: Informational
- Contract: Reentrancy
- Function name: withdraw(uint256)
- PC address: 552

### Description
The function withdraw(uint256) contains a call to msg.sender.
The return value of this call is not checked. Note that the function will continue to execute with a return value of '0' if the called contract throws.

In *reentrancy.sol:*

```
msg.sender.call.value(_amount)()
```
## Integer Underflow
- Type: Warning
- Contract: Under
- Function name: sendeth(address,uint256)
- PC address: 649

### Description
A possible integer underflow exists in the function `sendeth(address,uint256)`.
The SUB instruction at address 649 may result in a value < 0.

In *underflow.sol:*

```
balances[msg.sender] -= _value
```
## Integer Underflow
- Type: Warning
- Contract: Under
- Function name: sendeth(address,uint256)
- PC address: 567

### Description
A possible integer underflow exists in the function `sendeth(address,uint256)`.
The SUB instruction at address 567 may result in a value < 0.

In *underflow.sol:*

```
balances[msg.sender] - _value
```
## Weak random
- Type: Warning
- Contract: WeakRandom
- Function name: _function_0xe9874106
- PC address: 1285

### Description
In the function `'_function_0xe9874106'` the following predictable state variables are used to determine Ether recipient:
- block.coinbase


In *weak_random.sol:*

```
winningAddress.transfer(prize)
```

