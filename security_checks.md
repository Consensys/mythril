# Smart Contract Security Issues

| Issue | Description | Detection | Mythril Module(s) |
|------:|-------------|-----------|-----------|
|Unprotected functions|             |           | [unchecked_suicide](mythril/analysis/modules/unchecked_suicide.py), [ether_send](mythril/analysis/modules/ether_send.py)          |
|Re-entrancy|             |           |           |
|Multiple transfers in a single transaction|             |           |           |
|Integer overflow/underflow|             |           |           |
|Type confusion|             |           |           |
|Predictable RNG|             |           |           |
|Transaction order dependence|             |           |           |
|Timestamp dependence|             |           |           |
|Information exposure|             |           |           |
|Missing check on CALL return value|           |           |
|Call depth attack|             |           |           |
