from typing import Dict

from z3 import ExprRef, BitVecVal

from mythril.laser.ethereum.state.account import Account
from mythril.laser.ethereum.state.calldata import CalldataType, BaseCalldata


class Environment:
    """
    The environment class represents the current execution environment for the symbolic executor
    """

    def __init__(
        self,
        active_account: Account,
        sender: ExprRef,
        calldata: BaseCalldata,
        gasprice: ExprRef,
        callvalue: ExprRef,
        origin: ExprRef,
        code=None,
        calldata_type=CalldataType.SYMBOLIC,
    ):
        # Metadata

        self.active_account = active_account
        self.active_function_name = ""

        self.address = BitVecVal(int(active_account.address, 16), 256)

        # Ib
        self.code = active_account.code if code is None else code

        self.sender = sender
        self.calldata = calldata
        self.calldata_type = calldata_type
        self.gasprice = gasprice
        self.origin = origin
        self.callvalue = callvalue

    def __str__(self) -> str:
        return str(self.as_dict)

    @property
    def as_dict(self) -> Dict:
        return dict(
            active_account=self.active_account,
            sender=self.sender,
            calldata=self.calldata,
            gasprice=self.gasprice,
            callvalue=self.callvalue,
            origin=self.origin,
            calldata_type=self.calldata_type,
        )
