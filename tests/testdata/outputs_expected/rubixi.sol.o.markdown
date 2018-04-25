# Analysis results for test-filename.sol

## Ether send

- Type: Warning
- Contract: Unknown
- Function name: `_function_0x4229616d`
- PC address: 1599

### Description

In the function `_function_0x4229616d` a non-zero amount of Ether is sent to an address taken from storage slot 5.
There is a check on storage index 5. This storage slot can be written to by calling the function `_function_0x67f809e9`.

There is a check on storage index 5. This storage slot can be written to by calling the function `_function_0x67f809e9`.
There is a check on storage index 1. This storage slot can be written to by calling the function `fallback`.

## Ether send

- Type: Warning
- Contract: Unknown
- Function name: `_function_0x686f2c90`
- PC address: 1940

### Description

In the function `_function_0x686f2c90` a non-zero amount of Ether is sent to an address taken from storage slot 5.
There is a check on storage index 5. This storage slot can be written to by calling the function `_function_0x67f809e9`.

There is a check on storage index 5. This storage slot can be written to by calling the function `_function_0x67f809e9`.
There is a check on storage index 1. This storage slot can be written to by calling the function `fallback`.

## Exception state

- Type: Informational
- Contract: Unknown
- Function name: `_function_0x57d4021b`
- PC address: 1653

### Description

A reachable exception (opcode 0xfe) has been detected. This can be caused by type errors, division by zero, out-of-bounds array access, or assert violations. This is acceptable in most situations. Note however that `assert()` should only be used to check invariants. Use `require()` for regular input checking. 

## Exception state

- Type: Informational
- Contract: Unknown
- Function name: `_function_0x9dbc4f9b`
- PC address: 2085

### Description

A reachable exception (opcode 0xfe) has been detected. This can be caused by type errors, division by zero, out-of-bounds array access, or assert violations. This is acceptable in most situations. Note however that `assert()` should only be used to check invariants. Use `require()` for regular input checking. 

## Unchecked CALL return value

- Type: Informational
- Contract: Unknown
- Function name: `_function_0x4229616d`
- PC address: 1599

### Description

The return value of an external call is not checked. Note that execution continue even if the called contract throws.

## Unchecked CALL return value

- Type: Informational
- Contract: Unknown
- Function name: `_function_0xb4022950`
- PC address: 1940

### Description

The return value of an external call is not checked. Note that execution continue even if the called contract throws.

## Unchecked CALL return value

- Type: Informational
- Contract: Unknown
- Function name: `_function_0xb4022950`
- PC address: 2582

### Description

The return value of an external call is not checked. Note that execution continue even if the called contract throws.