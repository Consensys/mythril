"""This module contains account-related functionality.

This includes classes representing accounts and their storage.
"""
from copy import deepcopy, copy
from typing import Any, Dict, Union


from mythril.laser.smt import Array, K, BitVec, simplify, BitVecFunc, Extract
from mythril.disassembler.disassembly import Disassembly
from mythril.laser.smt import symbol_factory


class Storage:
    """Storage class represents the storage of an Account."""

    def __init__(
        self, concrete=False, address=None, dynamic_loader=None, keys=None
    ) -> None:
        """Constructor for Storage.

        :param concrete: bool indicating whether to interpret uninitialized storage as concrete versus symbolic
        """
        if concrete:
            self._standard_storage = K(256, 256, 0)
            self._map_storage = {}
        else:
            self._standard_storage = Array("Storage", 256, 256)
            self._map_storage = {}

        self._keys = keys or set()
        self.dynld = dynamic_loader
        self.address = address

    def __getitem__(self, item: Union[str, int]) -> Any:
        self._keys.add(item)
        storage = self._get_corresponding_storage(item)
        return simplify(storage[item])

    @staticmethod
    def get_map_index(key):
        if not isinstance(key, BitVecFunc) or key.func_name != "keccak256":
            return None
        index = Extract(255, 0, key.input_)
        print(simplify(index), key.input_)
        return simplify(index)

    def _get_corresponding_storage(self, key):
        index = self.get_map_index(key)
        if index is None:
            storage = self._standard_storage
        else:
            try:
                storage = self._map_storage[index]
            except KeyError:
                if isinstance(self._standard_storage, Array):
                    self._map_storage[index] = Array("Storage", 256, 256)
                else:
                    self._map_storage[index] = K(256, 256, 0)
                storage = self._map_storage[index]
        return storage

    def __setitem__(self, key, value: Any) -> None:
        self._keys.add(key)
        storage = self._get_corresponding_storage(key)
        storage[key] = value

    def __deepcopy__(self, memodict={}):
        concrete = isinstance(self._standard_storage, K)
        storage = Storage(
            concrete=concrete,
            address=self.address,
            dynamic_loader=self.dynld,
            keys=deepcopy(self._keys),
        )
        storage._standard_storage = deepcopy(self._standard_storage)
        storage._map_storage = deepcopy(self._map_storage)
        return storage

    def __str__(self):
        return str(self._standard_storage)

    def keys(self):
        return self._keys


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

    def __copy__(self, memodict={}):
        new_account = Account(
            address=self.address,
            code=self.code,
            contract_name=self.contract_name,
            balances=self._balances,
        )
        new_account.storage = copy(self.storage)
        new_account.code = self.code
        return new_account
