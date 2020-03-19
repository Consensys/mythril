import logging
from copy import copy, deepcopy
from typing import Any, Dict, Union, Set

from mythril.laser.ethereum.keccak_function_manager import keccak_function_manager
from mythril.laser.smt import (
    Array,
    K,
    BitVec,
    simplify,
    BaseArray,
    Extract,
    symbol_factory,
)

log = logging.getLogger(__name__)


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
        self.map_storage = MapStorage(concrete=concrete)
        self.printable_storage = {}  # type: Dict[BitVec, BitVec]

        self.dynld = dynamic_loader
        self.storage_keys_loaded = set()  # type: Set[int]
        self.address = address

    def get_storage(self, item: BitVec) -> Union[Array, "MapStorage"]:
        if simplify(item) not in keccak_function_manager.quick_inverse:
            return self._standard_storage

        inv_item = keccak_function_manager.quick_inverse[item]
        if Extract(255, 0, inv_item).symbolic:
            return self._standard_storage
        else:
            return self.map_storage

    def __getitem__(self, item: BitVec) -> BitVec:
        storage = self.get_storage(item)
        if (
            self.address
            and self.address.value != 0
            and item.symbolic is False
            and int(item.value) not in self.storage_keys_loaded
            and (self.dynld and self.dynld.active)
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
                self.storage_keys_loaded.add(int(item.value))
                self.printable_storage[item] = storage[item]
            except ValueError as e:
                log.debug("Couldn't read storage at %s: %s", item, e)
        return simplify(storage[item])

    def __setitem__(self, key, value: Any) -> None:
        self.printable_storage[key] = value
        storage = self.get_storage(key)
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


class MapStorage:
    def __init__(self, concrete=False) -> None:
        self.storages = {}
        self.concrete = concrete

    def get_storage(self, item: BitVec) -> Array:
        inverse = keccak_function_manager.quick_inverse[simplify(item)]
        slot = simplify(Extract(255, 0, inverse))
        assert slot.symbolic is False
        if slot.value not in self.storages:
            if self.concrete:
                self.storages[slot.value] = K(512, 256, 0)
            else:
                self.storages[slot.value] = Array("Map_{}".format(slot.value), 512, 256)
        return self.storages[slot.value]

    def __getitem__(self, item: BitVec) -> BitVec:
        storage = self.get_storage(item)
        inverse = keccak_function_manager.quick_inverse[simplify(item)]
        return storage[inverse]

    def __setitem__(self, key, value):
        storage = self.get_storage(key)
        inv_keccak_key = keccak_function_manager.quick_inverse[simplify(key)]
        storage[inv_keccak_key] = value
