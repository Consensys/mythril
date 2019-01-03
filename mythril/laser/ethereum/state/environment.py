"""This module contains the representation for an execution state's
environment."""
from typing import Dict

from z3 import ExprRef

from mythril.laser.ethereum.state.account import Account
from mythril.laser.ethereum.state.calldata import BaseCalldata
from mythril.laser.smt import symbol_factory


class Environment:
    """The environment class represents the current execution environment for
    the symbolic executor."""

    def __init__(
        self,
        active_account: Account,
        sender: ExprRef,
        calldata: BaseCalldata,
        gasprice: ExprRef,
        callvalue: ExprRef,
        origin: ExprRef,
        code=None,
    ):
        """

        :param active_account:
        :param sender:
        :param calldata:
        :param gasprice:
        :param callvalue:
        :param origin:
        :param code:
        :param calldata_type:
        """
        # Metadata

        self.active_account = active_account
        self.active_function_name = ""

        self.address = symbol_factory.BitVecVal(int(active_account.address, 16), 256)

        # Ib
        self.code = active_account.code if code is None else code

        self.sender = sender
        self.calldata = calldata
        self.gasprice = gasprice
        self.origin = origin
        self.callvalue = callvalue

    def __str__(self) -> str:
        """

        :return:
        """
        return str(self.as_dict)

    @property
    def as_dict(self) -> Dict:
        """

        :return:
        """
        return dict(
            active_account=self.active_account,
            sender=self.sender,
            calldata=self.calldata,
            gasprice=self.gasprice,
            callvalue=self.callvalue,
            origin=self.origin,
        )
