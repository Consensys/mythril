# Analysis results for test-filename.sol

## Dependence on predictable environment variable

- Type: Warning
- Contract: Unknown
- Function name: `_function_0xe9874106`
- PC address: 1285

### Description

In the function `_function_0xe9874106` the following predictable state variables are used to determine Ether recipient:
- block.coinbase


## Ether send

- Type: Warning
- Contract: Unknown
- Function name: `_function_0xe9874106`
- PC address: 1285

### Description

In the function `_function_0xe9874106` a non-zero amount of Ether is sent to an address taken from storage slot 0.
There is a check on storage index 0. This storage slot can be written to by calling the function `fallback`.

There is a check on storage index 1. This storage slot can be written to by calling the function `fallback`.
There is a check on storage index 1. This storage slot can be written to by calling the function `fallback`.

## Exception state

- Type: Informational
- Contract: Unknown
- Function name: `fallback`
- PC address: 356

### Description

A reachable exception (opcode 0xfe) has been detected. This can be caused by type errors, division by zero, out-of-bounds array access, or assert violations. This is acceptable in most situations. Note however that `assert()` should only be used to check invariants. Use `require()` for regular input checking. 

## Exception state

- Type: Informational
- Contract: Unknown
- Function name: `_function_0xe9874106`
- PC address: 146

### Description

A reachable exception (opcode 0xfe) has been detected. This can be caused by type errors, division by zero, out-of-bounds array access, or assert violations. This is acceptable in most situations. Note however that `assert()` should only be used to check invariants. Use `require()` for regular input checking. 

## Transaction order dependence

- Type: Warning
- Contract: Unknown
- Function name: `_function_0xe9874106`
- PC address: 1285

### Description

A possible transaction order independence vulnerability exists in function _function_0xe9874106. The value or direction of the call statement is determined from a tainted storage location