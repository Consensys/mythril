from random import randint

from ethereum import utils
from mythril.laser.smt import (
    BitVec,
    Function,
    URem,
    symbol_factory,
    ULE,
    And,
    ULT,
    Or,
    simplify,
)

TOTAL_PARTS = 10 ** 40
PART = (2 ** 256 - 1) // TOTAL_PARTS
INTERVAL_DIFFERENCE = 10 ** 30


class KeccakFunctionManager:
    def __init__(self):
        self.sizes = {}
        self.size_index = {}
        self.index_counter = TOTAL_PARTS - 34534
        self.concrete_dict = {}
        self.size_values = {}

    def find_keccak(self, data: BitVec) -> BitVec:
        return symbol_factory.BitVecVal(
            int.from_bytes(
                utils.sha3(data.value.to_bytes(data.size() // 8, byteorder="big")),
                "big",
            ),
            256,
        )

    def create_keccak(self, data: BitVec, length: int):
        length = length * 8
        data = simplify(data)
        assert length == data.size()
        try:
            func, inverse = self.sizes[length]
        except KeyError:
            func = Function("keccak256_{}".format(length), length, 256)
            inverse = Function("keccak256_{}-1".format(length), 256, length)
            self.sizes[length] = (func, inverse)
            self.size_values[length] = []
        constraints = []
        if data.symbolic is False:
            keccak = self.find_keccak(data)
            self.size_values[length].append(keccak)
            constraints.append(func(data) == keccak)

        constraints.append(inverse(func(data)) == data)
        if data.symbolic is False:
            return func(data), constraints

        try:
            index = self.size_index[length]
        except KeyError:
            self.size_index[length] = self.index_counter
            index = self.index_counter
            self.index_counter -= INTERVAL_DIFFERENCE

        lower_bound = index * PART
        upper_bound = (index + 1) * PART

        condition = And(
            ULE(symbol_factory.BitVecVal(lower_bound, 256), func(data)),
            ULT(func(data), symbol_factory.BitVecVal(upper_bound, 256)),
            URem(func(data), symbol_factory.BitVecVal(64, 256)) == 0,
        )
        condition = False
        try:
            concrete_input = self.concrete_dict[data]
            keccak = self.find_keccak(concrete_input)
        except KeyError:
            concrete_input = symbol_factory.BitVecVal(
                randint(0, 2 ** data.size() - 1), data.size()
            )
            self.concrete_dict[data] = concrete_input
            keccak = self.find_keccak(concrete_input)
        self.concrete_dict[func(data)] = keccak

        condition = Or(condition, And(data == concrete_input, keccak == func(data)))

        for val in self.size_values[length]:
            condition = Or(condition, func(data) == val)

        constraints.append(condition)
        return func(data), constraints


keccak_function_manager = KeccakFunctionManager()
