from ethereum import utils
from random import randint
from mythril.laser.smt import (
    BitVec,
    Function,
    URem,
    symbol_factory,
    ULE,
    And,
    ULT,
    Bool,
)
from typing import Dict, Tuple

TOTAL_PARTS = 10 ** 40
PART = (2 ** 256 - 1) // TOTAL_PARTS
INTERVAL_DIFFERENCE = 10 ** 30


class KeccakFunctionManager:
    def __init__(self):
        self.store_function = {}  # type: Dict[int, Tuple[Function, Function]]
        self.interval_hook_for_size = {}  # type: Dict[int, int]
        self._index_counter = TOTAL_PARTS - 34534
        self.quick_inverse = {}  # type: Dict[BitVec, BitVec]  # This is for VMTests

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

    def create_keccak(self, data: BitVec) -> Tuple[BitVec, Bool]:
        length = data.size()
        func, _ = self.get_function(length)
        condition = self._create_condition(func_input=data, func_output=func(data))
        self.quick_inverse[func(data)] = data
        return func(data), condition

    def get_new_cond(self, val, length: int) -> Bool:
        random_number = symbol_factory.BitVecSym(
            "randval_{}".format(randint(0, 10000)), length
        )
        return self._create_condition(func_input=random_number, func_output=val)

    def _create_condition(self, func_input: BitVec, func_output: BitVec) -> Bool:
        length = func_input.size()
        func, inv = self.get_function(length)
        cond = And(func(func_input) == func_output, inv(func(func_input)) == func_input)
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
            ULE(symbol_factory.BitVecVal(lower_bound, 256), func(func_input)),
            ULT(func(func_input), symbol_factory.BitVecVal(upper_bound, 256)),
            URem(func(func_input), symbol_factory.BitVecVal(64, 256)) == 0,
        )
        return cond


keccak_function_manager = KeccakFunctionManager()
