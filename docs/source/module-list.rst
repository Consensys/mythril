Modules
=======

***********************************
Delegate Call To Untrusted Contract
***********************************

The `delegatecall module <https://github.com/ConsenSys/mythril/blob/develop/mythril/analysis/modules/delegatecall.py>`_ detects `SWC-112 (DELEGATECALL to Untrusted Callee) <https://smartcontractsecurity.github.io/SWC-registry/docs/SWC-112>`_.

***********************************
Dependence on Predictable Variables
***********************************

The `predictable variables module <https://github.com/ConsenSys/mythril/blob/develop/mythril/analysis/modules/dependence_on_predictable_vars.py>`_ detects `SWC-120 (Weak Randomness) <https://smartcontractsecurity.github.io/SWC-registry/docs/SWC-120>`_ and `SWC-116 (Timestamp Dependence) <https://smartcontractsecurity.github.io/SWC-registry/docs/SWC-116>`_.

******************
Deprecated Opcodes
******************

The `deprecated opcodes module <https://github.com/ConsenSys/mythril/blob/develop/mythril/analysis/modules/deprecated_ops.py>`_ detects `SWC-111 (Use of Deprecated Functions) <https://smartcontractsecurity.github.io/SWC-registry/docs/SWC-111>`_.

***********
Ether Thief
***********

The `Ether Thief module <https://github.com/ConsenSys/mythril/blob/develop/mythril/analysis/modules/ether_thief.py>`_ detects `SWC-105 (Unprotected Ether Withdrawal) <https://smartcontractsecurity.github.io/SWC-registry/docs/SWC-105>`_.

**********
Exceptions
**********

The `exceptions module <https://github.com/ConsenSys/mythril/blob/develop/mythril/analysis/modules/exceptions.py>`_ detects `SWC-110 (Assert Violation) <https://smartcontractsecurity.github.io/SWC-registry/docs/SWC-110>`_.

**************
External Calls
**************

The `external calls module <https://github.com/ConsenSys/mythril/blob/develop/mythril/analysis/modules/external_calls.py>`_ warns about `SWC-117 (Reentrancy) <https://smartcontractsecurity.github.io/SWC-registry/docs/SWC-107>`_ by detecting calls to external contracts.

*******
Integer
*******

The `integer module <https://github.com/ConsenSys/mythril/blob/develop/mythril/analysis/modules/integer.py>`_ detects `SWC-101 (Integer Overflow and Underflow) <https://smartcontractsecurity.github.io/SWC-registry/docs/SWC-101>`_.

**************
Multiple Sends
**************

The `multiple sends module <https://github.com/ConsenSys/mythril/blob/develop/mythril/analysis/modules/multiple_sends.py>`_ detects `SWC-113 (Denial of Service with Failed Call) <https://smartcontractsecurity.github.io/SWC-registry/docs/SWC-113>`_ by checking for multiple calls or sends in a single transaction.

*******
Suicide
*******

The `suicide module <https://github.com/ConsenSys/mythril/blob/develop/mythril/analysis/modules/suicide.py>`_ detects `SWC-106 (Unprotected SELFDESTRUCT) <https://smartcontractsecurity.github.io/SWC-registry/docs/SWC-106>`_.


****************************
State Change External Calls
****************************

The `state change external calls module <https://github.com/ConsenSys/mythril/blob/develop/mythril/analysis/modules/state_change_external_calls.py>`_ detects `SWC-107 (Reentrancy) <https://smartcontractsecurity.github.io/SWC-registry/docs/SWC-107>`_ by detecting state change after calls to an external contract.

****************
Unchecked Retval
****************

The `unchecked retval module <https://github.com/ConsenSys/mythril/blob/develop/mythril/analysis/modules/unchecked_retval.py>`_ detects `SWC-104 (Unchecked Call Return Value) <https://smartcontractsecurity.github.io/SWC-registry/docs/SWC-104>`_.

****************
Unchecked Retval
****************

The `user supplied assertion module <https://github.com/ConsenSys/mythril/blob/develop/mythril/analysis/modules/unchecked_retval.py>`_ detects `SWC-110 (Assert Violation) <https://smartcontractsecurity.github.io/SWC-registry/docs/SWC-110>`_ for user-supplied assertions. User supplied assertions should be log messages of the form: :code:`emit AssertionFailed(string)`.
