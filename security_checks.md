# Smart Contract Security Issues

| Issue | Description | Mythril Detection Module(s) |
|------:|-------------|------------|
|Unprotected functions|         | [unchecked_suicide](mythril/analysis/modules/unchecked_suicide.py), [ether_send](mythril/analysis/modules/ether_send.py)          |
|Missing check on CALL return value|          | [unchecked_retval](mythril/analysis/modules/unchecked_retval.py)
|Re-entrancy|                        |           |
|Multiple transfers in a single transaction|             |           |           |
|Function call to untrusted contract|             |           |           |
|Delegatecall or callcode to untrusted contract|             |           |           |
|Integer overflow/underflow|                        | [integer_underflow](mythril/analysis/modules/integer_underflow.py)          |
|Type confusion|                        |           |
|Predictable RNG|                        |           |
|Transaction order dependence|             |           |           |
|Timestamp dependence|                        |           |
|Information exposure|                        |           |
|Call depth attack|                        |           |
