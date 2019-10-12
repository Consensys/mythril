from ethereum import utils
from random import randint
from mythril.laser.ethereum.state.constraints import Constraints
from mythril.laser.smt import (
    BitVec,
    Function,
    URem,
    symbol_factory,
    ULE,
    And,
    ULT,
    simplify,
)
from typing import Dict, Tuple

TOTAL_PARTS = 10 ** 40
PART = (2 ** 256 - 1) // TOTAL_PARTS
INTERVAL_DIFFERENCE = 10 ** 30


class KeccakFunctionManager:
    def __init__(self):
        self.store_function: Dict[int, Tuple[Function, Function]] = {}
        self.interval_hook_for_size: Dict[int, int] = {}
        self._index_counter: int = TOTAL_PARTS - 34534

    def find_keccak(self, data: BitVec) -> BitVec:
        keccak = symbol_factory.BitVecVal(
            int.from_bytes(
                utils.sha3(data.value.to_bytes(data.size() // 8, byteorder="big")),
                "big",
            ),
            256,
        )
        return keccak

    def get_function(self, length: int) -> Tuple[Function, Function]:
        try:
            func, inverse = self.store_function[length]
        except KeyError:
            func = Function("keccak256_{}".format(length), length, 256)
            inverse = Function("keccak256_{}-1".format(length), 256, length)
            self.store_function[length] = (func, inverse)
        return func, inverse

    def create_keccak(self, data: BitVec):

        length = data.size()
        simplify(data)
        constraints = Constraints()
        func, inverse = self.get_function(length)
        constraints.append(inverse(func(data)) == data)

        try:
            index = self.interval_hook_for_size[length]
        except KeyError:
            self.interval_hook_for_size[length] = self._index_counter
            index = self._index_counter
            self._index_counter -= INTERVAL_DIFFERENCE

        lower_bound = index * PART
        upper_bound = lower_bound + PART

        condition = And(
            ULE(symbol_factory.BitVecVal(lower_bound, 256), func(data)),
            ULT(func(data), symbol_factory.BitVecVal(upper_bound, 256)),
            URem(func(data), symbol_factory.BitVecVal(64, 256)) == 0,
        )
        constraints.append(condition)

        return func(data), constraints

    def get_new_cond(self, val, length: int):
        new_func, new_inv = self.get_function(length)
        random_number = symbol_factory.BitVecSym(
            "randval_{}".format(randint(0, 10000)), length
        )
        cond = And(
            new_func(random_number) == val,
            new_inv(new_func(random_number)) == random_number,
        )
        try:
            index = self.interval_hook_for_size[length]
        except KeyError:
            self.interval_hook_for_size[length] = self._index_counter
            index = self._index_counter
            self._index_counter -= INTERVAL_DIFFERENCE

        lower_bound = index * PART
        upper_bound = lower_bound + PART

        cond = And(
            cond,
            ULE(symbol_factory.BitVecVal(lower_bound, 256), new_func(random_number)),
            ULT(new_func(random_number), symbol_factory.BitVecVal(upper_bound, 256)),
            URem(new_func(random_number), symbol_factory.BitVecVal(64, 256)) == 0,
        )
        return cond


keccak_function_manager = KeccakFunctionManager()
