

## Dependence on predictable environment variable

- Type: Warning
- Contract: WeakRandom
- Function name: `_function_0xe9874106`
- PC address: 1285



### Description
In the function `_function_0xe9874106` the following predictable state variables are used to determine Ether recipient:
- block.coinbase


In *<TESTDATA>/inputs/weak_random.sol:47*

```
winningAddress.transfer(prize)
```


## Ether send

- Type: Warning
- Contract: WeakRandom
- Function name: `_function_0xe9874106`
- PC address: 1285



### Description
In the function `_function_0xe9874106` a non-zero amount of Ether is sent to an address taken from storage slot 0.
There is a check on storage index 0. This storage slot can be written to by calling the function `fallback`.

There is a check on storage index 1. This storage slot can be written to by calling the function `fallback`.
There is a check on storage index 1. This storage slot can be written to by calling the function `fallback`.

In *<TESTDATA>/inputs/weak_random.sol:47*

```
winningAddress.transfer(prize)
```


## Exception state

- Type: Informational
- Contract: WeakRandom
- Function name: `fallback`
- PC address: 356



### Description
A reachable exception (opcode 0xfe) has been detected. This can be caused by type errors, division by zero, out-of-bounds array access, or assert violations. This is acceptable in most situations. Note however that `assert()` should only be used to check invariants. Use `require()` for regular input checking. 

In *<TESTDATA>/inputs/weak_random.sol:11*

```
prize / totalTickets
```


## Exception state

- Type: Informational
- Contract: WeakRandom
- Function name: `_function_0xe9874106`
- PC address: 146



### Description
A reachable exception (opcode 0xfe) has been detected. This can be caused by type errors, division by zero, out-of-bounds array access, or assert violations. This is acceptable in most situations. Note however that `assert()` should only be used to check invariants. Use `require()` for regular input checking. 

In *<TESTDATA>/inputs/weak_random.sol:11*

```
prize / totalTickets
```


## Integer Overflow 

- Type: Warning
- Contract: WeakRandom
- Function name: `_function_0xe9874106`
- PC address: 1216



### Description

A possible integer overflow exists in the function `_function_0xe9874106`.
The addition or multiplication may result in a value higher than the maximum representable integer.

In *<TESTDATA>/inputs/weak_random.sol:45*

```
gameId++
```


## Integer Overflow 

- Type: Warning
- Contract: WeakRandom
- Function name: `_function_0xe9874106`
- PC address: 262



### Description

A possible integer overflow exists in the function `_function_0xe9874106`.
The addition or multiplication may result in a value higher than the maximum representable integer.

In *<TESTDATA>/inputs/weak_random.sol:22*

```
contestants[currTicket] = Contestant(msg.sender, gameId)
```
