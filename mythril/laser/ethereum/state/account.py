"""This module contains account-related functionality.

This includes classes representing accounts and their storage.
"""
from copy import deepcopy, copy
from typing import Any, Dict, KeysView, Union

from z3 import ExprRef

from mythril.disassembler.disassembly import Disassembly
from mythril.laser.smt import symbol_factory


class Storage:
    """Storage class represents the storage of an Account."""

    def __init__(self, concrete=False, address=None, dynamic_loader=None) -> None:
        """Constructor for Storage.

        :param concrete: bool indicating whether to interpret uninitialized storage as concrete versus symbolic
        """
        self._storage = {}  # type: Dict[Union[int, str], Any]
        self.concrete = concrete
        self.dynld = dynamic_loader
        self.address = address

    def __getitem__(self, item: Union[str, int]) -> Any:
        try:
            return self._storage[item]
        except KeyError:
            if (
                self.address
                and int(self.address[2:], 16) != 0
                and (self.dynld and self.dynld.storage_loading)
            ):
                try:
                    self._storage[item] = symbol_factory.BitVecVal(
                        int(
                            self.dynld.read_storage(
                                contract_address=self.address, index=int(item)
                            ),
                            16,
                        ),
                        256,
                    )
                    return self._storage[item]
                except ValueError:
                    pass
        if self.concrete:
            return symbol_factory.BitVecVal(0, 256)
        self._storage[item] = symbol_factory.BitVecVal(0, 256)
        return self._storage[item]

    def __setitem__(self, key: Union[int, str], value: Any) -> None:
        self._storage[key] = value

    def keys(self) -> KeysView:
        """

        :return:
        """
        return self._storage.keys()

    def __deepcopy__(self, memodict={}):
        storage = Storage(
            concrete=self.concrete, address=self.address, dynamic_loader=self.dynld
        )
        storage._storage = copy(self._storage)
        return storage


class Account:
    """Account class representing ethereum accounts."""

    def __init__(
        self,
        address: str,
        code=None,
        contract_name="unknown",
        balance=None,
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
        self.balance = (
            balance
            if balance
            else symbol_factory.BitVecSym("{}_balance".format(address), 256)
        )
        self.storage = Storage(
            concrete_storage, address=address, dynamic_loader=dynamic_loader
        )
        # Metadata
        self.address = address
        self.contract_name = contract_name

        self.deleted = False

    def __str__(self) -> str:
        return str(self.as_dict)

    def set_balance(self, balance: ExprRef) -> None:
        """

        :param balance:
        """
        self.balance = balance

    def add_balance(self, balance: ExprRef) -> None:
        """

        :param balance:
        """
        self.balance += balance

    @property
    def as_dict(self) -> Dict:
        """

        :return:
        """
        return {
            "nonce": self.nonce,
            "code": self.code,
            "balance": self.balance,
            "storage": self.storage,
        }

    def __deepcopy__(self, memodict={}):
        new_account = Account(
            address=self.address,
            code=self.code,
            balance=self.balance,
            contract_name=self.contract_name,
        )
        new_account.storage = deepcopy(self.storage)
        new_account.code = self.code
        return new_account
