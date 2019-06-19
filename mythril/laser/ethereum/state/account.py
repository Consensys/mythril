"""This module contains account-related functionality.

This includes classes representing accounts and their storage.
"""
from copy import deepcopy, copy
from typing import Any, Dict, KeysView, Union

from z3 import ExprRef

from mythril.laser.smt import Array, symbol_factory, BitVec
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
                and self.address.value != 0
                and (self.dynld and self.dynld.storage_loading)
            ):
                try:
                    self._storage[item] = symbol_factory.BitVecVal(
                        int(
                            self.dynld.read_storage(
                                contract_address=hex(self.address.value), index=int(item)
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

        self._storage[item] = symbol_factory.BitVecSym(
            "storage_{}_{}".format(str(item), str(self.address)), 256
        )
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

    def __str__(self):
        return str(self._storage)


class Account:
    """Account class representing ethereum accounts."""

    def __init__(
        self,
        address: Union[BitVec, str],
        code=None,
        contract_name="unknown",
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

    def __deepcopy__(self, memodict={}):
        new_account = Account(
            address=self.address,
            code=self.code,
            contract_name=self.contract_name,
            balances=self._balances,
        )
        new_account.storage = deepcopy(self.storage)
        new_account.code = self.code
        return new_account
