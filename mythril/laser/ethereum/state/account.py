"""This module contains account-related functionality.

This includes classes representing accounts and their storage.
"""
import logging
from copy import copy, deepcopy
from typing import Any, Dict, Union, Set

from mythril.laser.ethereum.state.storage import Storage
from mythril.laser.smt import Array, K, BitVec, simplify, BaseArray
from mythril.disassembler.disassembly import Disassembly
from mythril.laser.smt import symbol_factory

log = logging.getLogger(__name__)


class Account:
    """Account class representing ethereum accounts."""

    def __init__(
        self,
        address: Union[BitVec, str],
        code=None,
        contract_name=None,
        balances: Array = None,
        concrete_storage=False,
        dynamic_loader=None,
    ) -> None:
        """Constructor for account.

        :param address: Address of the account
        :param code: The contract code of the account
        :param contract_name: The name associated with the account
        :param balance: The balance for the account
        :param concrete_storage: Interpret storage as concrete
        """
        self.nonce = 0
        self.code = code or Disassembly("")
        self.address = (
            address
            if isinstance(address, BitVec)
            else symbol_factory.BitVecVal(int(address, 16), 256)
        )

        self.storage = Storage(
            concrete_storage, address=self.address, dynamic_loader=dynamic_loader
        )

        # Metadata
        if contract_name is None:
            self.contract_name = (
                "{0:#0{1}x}".format(self.address.value, 42)
                if not self.address.symbolic
                else "unknown"
            )
        else:
            self.contract_name = contract_name

        self.deleted = False

        self._balances = balances
        self.balance = lambda: self._balances[self.address]

    def __str__(self) -> str:
        return str(self.as_dict)

    def set_balance(self, balance: Union[int, BitVec]) -> None:
        """

        :param balance:
        """
        balance = (
            symbol_factory.BitVecVal(balance, 256)
            if isinstance(balance, int)
            else balance
        )
        assert self._balances is not None
        self._balances[self.address] = balance

    def add_balance(self, balance: Union[int, BitVec]) -> None:
        """

        :param balance:
        """
        balance = (
            symbol_factory.BitVecVal(balance, 256)
            if isinstance(balance, int)
            else balance
        )
        self._balances[self.address] += balance

    @property
    def as_dict(self) -> Dict:
        """

        :return:
        """
        return {
            "nonce": self.nonce,
            "code": self.code,
            "balance": self.balance(),
            "storage": self.storage,
        }

    def __copy__(self, memodict={}):
        new_account = Account(
            address=self.address,
            code=self.code,
            contract_name=self.contract_name,
            balances=self._balances,
        )
        new_account.storage = deepcopy(self.storage)
        new_account.code = self.code
        return new_account
