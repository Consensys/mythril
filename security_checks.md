# Smart Contract Security Issues

| Issue | Description | Mythril Detection Module(s) |
|------:|-------------|------------|
|Unprotected functions|         | [unchecked_suicide](mythril/analysis/modules/unchecked_suicide.py), [ether_send](mythril/analysis/modules/ether_send.py)          |
|Missing check on CALL return value|          | [unchecked_retval](mythril/analysis/modules/unchecked_retval.py)
|Re-entrancy|                        |           |
|Multiple transfers in a single transaction|             |           |           |
|Function call to untrusted contract|             |           |           |
|Delegatecall or callcode to untrusted contract|                   | [delegatecall_forward](mythril/analysis/modules/delegatecall_forward.py), [delegatecall_to_dynamic.py](mythril/analysis/modules/delegatecall_to_dynamic.py) |
|Integer overflow/underflow|                        | [integer_underflow](mythril/analysis/modules/integer_underflow.py)          |
|Type confusion|                        |           |
|Predictable RNG|                        |           |
|Transaction order dependence|             |           |           |
|Timestamp dependence|                        |           |
|Information exposure|                        |           |
|Payable transaction does not revert in case of failure | | |
|Call depth attack|                        |           |
