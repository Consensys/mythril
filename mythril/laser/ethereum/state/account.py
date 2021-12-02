"""This module contains account-related functionality.

This includes classes representing accounts and their storage.
"""
import logging
from copy import copy, deepcopy
from typing import Any, Dict, Union, Set


from mythril.laser.smt import Array, K, BitVec, simplify, BaseArray, If, Bool
from mythril.disassembler.disassembly import Disassembly
from mythril.laser.smt import symbol_factory
from mythril.support.support_args import args

log = logging.getLogger(__name__)


class Storage:
    """Storage class represents the storage of an Account."""

    def __init__(self, concrete=False, address=None, dynamic_loader=None) -> None:
        """Constructor for Storage.

        :param concrete: bool indicating whether to interpret uninitialized storage as concrete versus symbolic
        """
        if concrete and args.unconstrained_storage is False:
            self._standard_storage: BaseArray = K(256, 256, 0)
        else:
            self._standard_storage = Array(f"Storage{address}", 256, 256)

        self.printable_storage: Dict[BitVec, BitVec] = {}

        self.dynld = dynamic_loader
        self.storage_keys_loaded: Set[int] = set()
        self.address = address

        # Stores all keys set in the storage
        self.keys_set: Set[BitVec] = set()

    def __getitem__(self, item: BitVec) -> BitVec:
        storage = self._standard_storage
        if (
            self.address
            and self.address.value != 0
            and item.symbolic is False
            and int(item.value) not in self.storage_keys_loaded
            and (self.dynld and self.dynld.active)
            and args.unconstrained_storage is False
        ):
            try:
                value = symbol_factory.BitVecVal(
                    int(
                        self.dynld.read_storage(
                            contract_address="0x{:040X}".format(self.address.value),
                            index=int(item.value),
                        ),
                        16,
                    ),
                    256,
                )

                for key in self.keys_set:
                    value = If(key == item, storage[item], value)

                storage[item] = value
                self.storage_keys_loaded.add(int(item.value))
                self.printable_storage[item] = storage[item]
            except ValueError as e:
                log.debug("Couldn't read storage at %s: %s", item, e)

        return simplify(storage[item])

    def __setitem__(self, key, value: Any) -> None:
        if isinstance(value, Bool):
            value = If(value, 1, 0)

        self.printable_storage[key] = value
        self._standard_storage[key] = value

        self.keys_set.add(key)

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
        storage.keys_set = copy(self.keys_set)
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
        self.concrete_storage = concrete_storage
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
            "code": self.serialised_code(),
            "balance": self.balance(),
            "storage": self.storage,
        }

    def serialised_code(self):
        if type(self.code.bytecode) == str:
            return self.code.bytecode
        new_code = "0x"
        for byte in self.code.bytecode:
            if type(byte) == int:
                new_code += hex(byte)
            else:
                new_code += "<call_data>"
        return new_code

    def __copy__(self, memodict={}):
        new_account = Account(
            address=self.address,
            code=self.code,
            contract_name=self.contract_name,
            balances=self._balances,
            concrete_storage=self.concrete_storage,
        )
        new_account.storage = deepcopy(self.storage)
        new_account.code = self.code
        return new_account
