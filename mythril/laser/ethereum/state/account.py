"""This module contains account-related functionality.

This includes classes representing accounts and their storage.
"""
import logging
from copy import copy, deepcopy
from typing import Any, Dict, Union, Tuple, Set, cast


from mythril.laser.smt import (
    Array,
    K,
    BitVec,
    simplify,
    BitVecFunc,
    Extract,
    BaseArray,
    Concat,
)
from mythril.disassembler.disassembly import Disassembly
from mythril.laser.smt import symbol_factory

log = logging.getLogger(__name__)


class StorageRegion:
    def __getitem__(self, item):
        raise NotImplementedError

    def __setitem__(self, key, value):
        raise NotImplementedError


class ArrayStorageRegion(StorageRegion):
    """ An ArrayStorageRegion is a storage region that leverages smt array theory to resolve expressions"""

    pass


class IteStorageRegion(StorageRegion):
    """ An IteStorageRegion is a storage region that uses Ite statements to implement a storage"""

    pass


class Storage:
    """Storage class represents the storage of an Account."""

    def __init__(self, concrete=False, address=None, dynamic_loader=None) -> None:
        """Constructor for Storage.

        :param concrete: bool indicating whether to interpret uninitialized storage as concrete versus symbolic
        """
        if concrete:
            self._standard_storage = K(256, 256, 0)  # type: BaseArray
        else:
            self._standard_storage = Array("Storage", 256, 256)

        self.printable_storage = {}  # type: Dict[BitVec, BitVec]

        self.dynld = dynamic_loader
        self.storage_keys_loaded = set()  # type: Set[int]
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
        storage = self._standard_storage
        sanitized_item = item
        if (
            self.address
            and self.address.value != 0
            and item.symbolic is False
            and int(item.value) not in self.storage_keys_loaded
            and (self.dynld and self.dynld.storage_loading)
        ):
            try:
                storage[sanitized_item] = symbol_factory.BitVecVal(
                    int(
                        self.dynld.read_storage(
                            contract_address="0x{:040X}".format(self.address.value),
                            index=int(item.value),
                        ),
                        16,
                    ),
                    256,
                )
                self.storage_keys_loaded.add(int(item.value))
                self.printable_storage[item] = storage[sanitized_item]
            except ValueError as e:
                log.debug("Couldn't read storage at %s: %s", item, e)
        return simplify(storage[sanitized_item])

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

    def _get_corresponding_storage(self, key: BitVec) -> BaseArray:
        return self._standard_storage

    def __setitem__(self, key, value: Any) -> None:
        storage = self._get_corresponding_storage(key)
        self.printable_storage[key] = value
        storage[key] = value
        if key.symbolic is False:
            self.storage_keys_loaded.add(int(key.value))

    def __deepcopy__(self, memodict=dict()):
        concrete = isinstance(self._standard_storage, K)
        storage = Storage(
            concrete=concrete, address=self.address, dynamic_loader=self.dynld
        )
        storage._standard_storage = deepcopy(self._standard_storage)
        storage.printable_storage = copy(self.printable_storage)
        storage.storage_keys_loaded = copy(self.storage_keys_loaded)
        return storage

    def __str__(self) -> str:
        # TODO: Do something better here
        return str(self.printable_storage)


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
