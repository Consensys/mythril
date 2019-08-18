"""This module contains account-related functionality.

This includes classes representing accounts and their storage.
"""
import logging
from copy import copy, deepcopy
from typing import Any, Dict, Union, Tuple, cast
from sha3 import keccak_256
from random import randint

from mythril.laser.smt import (
    Array,
    K,
    BitVec,
    simplify,
    BitVecFunc,
    Extract,
    BaseArray,
    Concat,
    And,
    If,
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
    """Storage class represents the storage of an Account."""

    def __init__(self, concrete=False, address=None, dynamic_loader=None) -> None:
        """Constructor for Storage.

        :param concrete: bool indicating whether to interpret uninitialized storage as concrete versus symbolic
        """
        if concrete:
            self._standard_storage = K(256, 256, 0)  # type: BaseArray
        else:
            self._standard_storage = Array("Storage", 256, 256)
        self._map_storage = {}  # type: Dict[BitVec, BaseArray]

        self.dynld = dynamic_loader
        self.address = address

    @staticmethod
    def _sanitize(input_: BitVec) -> BitVec:
        if input_.potential_values:
            input_ = input_.potential_values
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
        if is_keccak_storage:
            key = self._sanitize(key.input_)
        storage[key] = value

    def __deepcopy__(self, memodict=dict()):
        concrete = isinstance(self._standard_storage, K)
        storage = ArrayStorageRegion(
            concrete=concrete, address=self.address, dynamic_loader=self.dynld
        )
        storage._standard_storage = deepcopy(self._standard_storage)
        storage._map_storage = deepcopy(self._map_storage)

        return storage


class IteStorageRegion(StorageRegion):
    """ An IteStorageRegion is a storage region that uses Ite statements to implement a storage"""

    def __init__(self) -> None:
        """Constructor for Storage.
        """
        self.itedict = {}  # type: Dict[Tuple[BitVecFunc, Any]]

    def __getitem__(self, item: BitVecFunc):
        storage = symbol_factory.BitVecVal(0, 256)
        for key, val in self.itedict.items():
            storage = If(item == key, val, storage)
        return storage

    def __setitem__(self, key: BitVecFunc, value):
        self.itedict[key] = value

    def __deepcopy__(self, memodict={}):
        ite_copy = IteStorageRegion()
        ite_copy.itedict = copy(self.itedict)
        return ite_copy


class Storage:
    """Storage class represents the storage of an Account."""

    def __init__(
        self, concrete=False, address=None, dynamic_loader=None, copy_call=False
    ) -> None:
        """Constructor for Storage.

        :param concrete: bool indicating whether to interpret uninitialized storage as concrete versus symbolic
        """
        if copy_call:
            # This is done because it was costly create these instances
            self._array_region = None
            self._ite_region = None
        else:
            self._array_region = ArrayStorageRegion(concrete, address, dynamic_loader)
            self._ite_region = IteStorageRegion()
        self._printable_storage = {}  # type: Dict[BitVec, BitVec]

    @staticmethod
    def _array_condition(key: BitVec):
        return not isinstance(key, BitVecFunc) or (
            isinstance(key, BitVecFunc)
            and key.func_name == "keccak256"
            and len(key.nested_functions) <= 1
        )

    def __getitem__(self, key: BitVec) -> BitVec:
        ite_get = self._ite_region[cast(BitVecFunc, key)]
        array_get = self._array_region[key]
        if self._array_condition(key):
            return If(ite_get, ite_get, array_get)
        else:
            return ite_get

    def __setitem__(self, key: BitVec, value: Any) -> None:
        self._printable_storage[key] = value
        if self._array_condition(key):
            self._array_region[key] = value

        self._ite_region[cast(BitVecFunc, key)] = value

    def __deepcopy__(self, memodict=dict()):
        storage = Storage(copy_call=True)
        storage._array_region = deepcopy(self._array_region)
        storage._ite_region = deepcopy(self._ite_region)
        storage._printable_storage = copy(self._printable_storage)
        return storage

    def __str__(self) -> str:
        # TODO: Do something better here
        return str(self._printable_storage)

    def concretize(self, models):
        for key, value in self._ite_region.itedict.items():
            key_concrete = self._traverse_concretise(key, models)
            key.potential_values = key_concrete

    def calc_sha3(self, val, size):
        try:
            hex_val = hex(val.value)[2:]
            if len(hex_val) % 2 != 0:
                hex_val += "0"
            val = int(keccak_256(bytes.fromhex(hex_val)).hexdigest(), 16)
        except (AttributeError, TypeError):
            ran = hex(randint(0, 2 ** size - 1))[2:]
            if len(ran) % 2 != 0:
                ran += "0"
            val = int(keccak_256(bytes.fromhex(ran)).hexdigest(), 16)
        return symbol_factory.BitVecVal(val, 256)

    def _find_value(self, symbol, model):
        if model is None:
            return
        modify = symbol
        size = min(symbol.size(), 256)
        if symbol.size() > 256:
            index = simplify(Extract(255, 0, symbol))
        else:
            index = None
        if index and not index.symbolic:
            modify = Extract(511, 256, modify)
        modify = model.eval(modify.raw)
        try:
            modify = modify.as_long()
        except AttributeError:
            modify = randint(0, 2 ** modify.size() - 1)
        modify = symbol_factory.BitVecVal(modify, size)
        if index and not index.symbolic:
            modify = Concat(modify, index)

        assert modify.size() == symbol.size()
        return modify

    def _traverse_concretise(self, key, models):
        """
        Breadth first Search
        :param key:
        :param model:
        :return:
        """
        if not isinstance(key, BitVecFunc):
            concrete_values = [self._find_value(key, model[0]) for model in models]
            if key.size() == 512:
                ex_key = Extract(511, 256, key)
            else:
                ex_key = key
            potential_values = concrete_values
            key.potential_values = []
            for i, val in enumerate(potential_values):
                key.potential_values.append(
                    (val, And(models[i][1], BitVec(key.raw) == val))
                )

            return key.potential_values
        if key.size() == 512:
            val = simplify(Extract(511, 256, key))
            concrete_vals = self._traverse_concretise(val, models)
            vals2 = self._traverse_concretise(Extract(255, 0, key), models)
            key.potential_values = []
            i = 0
            for val1, val2 in zip(concrete_vals, vals2):
                if val2[0] and val1[0]:
                    c_val = Concat(val1[0], val2[0])
                    condition = And(
                        models[i][1], BitVec(key.raw) == c_val, val1[1], val2[1]
                    )
                    key.potential_values.append((c_val, condition))
                else:
                    key.potential_values.append((None, None))

        if isinstance(key.input_, BitVec) or (
            isinstance(key.input_, BitVecFunc) and key.input_.func_name == "sha3"
        ):
            self._traverse_concretise(key.input_, models)

        if isinstance(key, BitVecFunc):
            if key.size() == 512:
                p1 = Extract(511, 256, key)
                if not isinstance(p1, BitVecFunc):
                    p1 = Extract(255, 0, key)
                p1 = [
                    (self.calc_sha3(val[0], p1.input_.size()), val[1])
                    for val in p1.input_.potential_values
                ]
                key.potential_values = []
                for i, val in enumerate(p1):
                    if val[0]:
                        c_val = Concat(val[0], Extract(255, 0, key))
                        condition = And(models[i][1], val[1], BitVec(key.raw) == c_val)
                        key.potential_values.append((c_val, condition))
                    else:
                        key.potential_values.append((None, None))
            else:
                key.potential_values = []
                for i, val in enumerate(key.input_.potential_values):
                    if val[0]:
                        concrete_val = self.calc_sha3(val[0], key.input_.size())
                        condition = And(
                            models[i][1], val[1], BitVec(key.raw) == concrete_val
                        )
                        key.potential_values.append((concrete_val, condition))
                    else:
                        key.potential_values.append((None, None))
        if key.potential_values[0][0] is not None:
            assert key.size() == key.potential_values[0][0].size()

        return key.potential_values


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
