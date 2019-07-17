"""This module contains account-related functionality.

This includes classes representing accounts and their storage.
"""
from copy import copy, deepcopy
from typing import Any, Dict, Union, Tuple, cast


from mythril.laser.smt import (
    Array,
    K,
    BitVec,
    simplify,
    BitVecFunc,
    Extract,
    BaseArray,
    Concat,
    If,
)
from mythril.disassembler.disassembly import Disassembly
from mythril.laser.smt import symbol_factory


class ArrayStorageRegion:
    """ An ArrayStorageRegion is a storage region that leverages smt array theory to resolve expressions"""

    def __init__(self, concrete=False, address=None, dynamic_loader=None) -> None:
        """Constructor for Storage.

        :param concrete: bool indicating whether to interpret uninitialized storage as concrete versus symbolic
        """
        if concrete:
            self._standard_storage = K(256, 256, 0)  # type: BaseArray
        else:
            self._standard_storage = Array("Storage", 256, 256)
        self._map_storage = {}  # type: Dict[BitVec, BaseArray]

        self.printable_storage = {}  # type: Dict[BitVec, BitVec]

        self.dynld = dynamic_loader
        self.address = address

    @staticmethod
    def _sanitize(input_: BitVec) -> BitVec:
        if input_.size() == 512:
            return input_
        if input_.size() > 512:
            return Extract(511, 0, input_)
        else:
            return Concat(symbol_factory.BitVecVal(0, 512 - input_.size()), input_)

    def __getitem__(self, item: BitVec) -> BitVec:
        storage, is_keccak_storage = self._get_corresponding_storage(item)
        if is_keccak_storage:
            item = self._sanitize(cast(BitVecFunc, item).input_)
        value = storage[item]
        if (
            value.value == 0
            and self.address
            and item.symbolic is False
            and self.address.value != 0
            and (self.dynld and self.dynld.storage_loading)
        ):
            try:
                storage[item] = symbol_factory.BitVecVal(
                    int(
                        self.dynld.read_storage(
                            contract_address="0x{:040X}".format(self.address.value),
                            index=int(item.value),
                        ),
                        16,
                    ),
                    256,
                )
                self.printable_storage[item] = storage[item]
                return storage[item]
            except ValueError:
                pass

        return simplify(storage[item])

    @staticmethod
    def get_map_index(key: BitVec) -> BitVec:
        if (
            not isinstance(key, BitVecFunc)
            or key.func_name != "keccak256"
            or key.input_ is None
        ):
            return None
        index = Extract(255, 0, key.input_)
        return simplify(index)

    def _get_corresponding_storage(self, key: BitVec) -> Tuple[BaseArray, bool]:
        index = self.get_map_index(key)
        if index is None:
            storage = self._standard_storage
            is_keccak_storage = False
        else:
            storage_map = self._map_storage
            try:
                storage = storage_map[index]
            except KeyError:
                if isinstance(self._standard_storage, Array):
                    storage_map[index] = Array("Storage", 512, 256)
                else:
                    storage_map[index] = K(512, 256, 0)
                storage = storage_map[index]
            is_keccak_storage = True
        return storage, is_keccak_storage

    def __setitem__(self, key, value: Any) -> None:
        storage, is_keccak_storage = self._get_corresponding_storage(key)
        self.printable_storage[key] = value
        if is_keccak_storage:
            key = self._sanitize(key.input_)
        storage[key] = value

    def __deepcopy__(self, memodict=dict()):
        concrete = isinstance(self._standard_storage, K)
        storage = Storage(
            concrete=concrete, address=self.address, dynamic_loader=self.dynld
        )
        storage._standard_storage = deepcopy(self._standard_storage)
        storage._map_storage = deepcopy(self._map_storage)
        storage.print_storage = copy(self.printable_storage)
        return storage

    def __str__(self) -> str:
        # TODO: Do something better here
        return str(self.printable_storage)


class IteStorageRegion:
    """ An IteStorageRegion is a storage region that uses Ite statements to implement a storage"""

    def __init__(self) -> None:
        """Constructor for Storage.
        """
        self.itelist = []

    def __getitem__(self, item: BitVecFunc):
        print(item, item.nested_functions)
        storage = symbol_factory.BitVecVal(0, 256)
        for key, val in self.itelist[::-1]:
            storage = If(item == key, val, storage)
        return storage

    def __setitem__(self, key: BitVecFunc, value):
        print(key, key.nested_functions)
        self.itelist.append((key, value))

    def __deepcopy__(self, memodict={}):
        ite_copy = IteStorageRegion()
        ite_copy.itelist = copy(self.itelist)
        return ite_copy


class Storage:
    """Storage class represents the storage of an Account."""

    def __init__(self, concrete=False, address=None, dynamic_loader=None) -> None:
        """Constructor for Storage.

        :param concrete: bool indicating whether to interpret uninitialized storage as concrete versus symbolic
        """
        self.array_region = ArrayStorageRegion(concrete, address, dynamic_loader)
        self.ite_region = IteStorageRegion()

    @staticmethod
    def _array_condition(key):
        return isinstance(key, BitVecFunc) is False or (
            key.func_name == "keccak256" and len(key.nested_functions) <= 1
        )

    def __getitem__(self, key: BitVec) -> BitVec:
        if self._array_condition(key):
            return self.array_region[key]
        return self.ite_region[key]

    def __setitem__(self, key: BitVec, value: Any) -> None:
        if self._array_condition(key):
            self.array_region[key] = value
            return

        self.ite_region[key] = value

    def __deepcopy__(self, memodict=dict()):
        storage = Storage()
        storage.array_region = deepcopy(self.array_region)
        storage.ite_region = deepcopy(self.ite_region)
        return storage

    def __str__(self) -> str:
        # TODO: Do something better here
        return ""


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
        new_account.storage = deepcopy(self.storage)
        new_account.code = self.code
        return new_account
